#!/usr/bin/env node
/*
 * JURAGAN-1 — Proof Gatekeeper agent for zkVerify Agent Games.
 *
 * Protocol (verified against agentgames.zkverify.io/build on 2026-11-14,
 * see ../../NOTES.md):
 *  - Platform POSTs HMAC-SHA256 signed JSON envelopes to /agent.
 *    Signature = header `x-agent-games-signature`, computed over the RAW body.
 *  - Preflight  { type: "agent-games.preflight.v1" }  ->  { ok: true, protocolVersion: "v1" }
 *  - Task       { type: "agent-games.proof-gatekeeper.v1", task_id, mode,
 *                 issued_at, deadline_at, input: { registered_vk, proof_vk,
 *                 minimum, public_balance, expiry_block, current_block,
 *                 recipient, condition_recipient, amount, max_transfer, proof_tx } }
 *    -> { decision, reason_code, proof?, public_signals?, proof_tx? }
 *  - Every response is signed with the same HMAC header over the raw body.
 *  - Hard deadline 60 s; we guarantee a response within RESPONSE_BUDGET_MS.
 *  - Fail closed: any error/uncertainty => REJECT (or a signed 4xx for
 *    unauthenticated / malformed traffic).
 *
 * Decision rules mirror the gatekeeper circuit EXACTLY (empirically verified):
 *   APPROVE iff proof_vk == registered_vk
 *           AND proof_tx not seen before
 *           AND current_block <  expiry_block      (equality == EXPIRED)
 *           AND public_balance >= minimum          (equality == VALID)
 *           AND recipient == condition_recipient
 *           AND amount <= max_transfer             (equality == VALID)
 *
 * Our decision is proven with the official gatekeeper circuit (Groth16/BN128,
 * snarkjs). The circuit asserts decision == evaluation of the field checks,
 * so a proof for a wrong decision cannot exist. PROOF_REUSED responses carry
 * no proof (per the event rules, those tasks are excluded from proof scoring).
 */
"use strict";

const http = require("http");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const snarkjs = require("snarkjs");
const { ethers } = require("ethers");

// ---------------------------------------------------------------- config ---
const ROOT = path.join(__dirname, "..");
function loadDotEnv() {
  const file = path.join(ROOT, ".env");
  if (!fs.existsSync(file)) return;
  for (const line of fs.readFileSync(file, "utf8").split("\n")) {
    const m = line.match(/^\s*([A-Z0-9_]+)\s*=\s*(.*)\s*$/);
    if (m && process.env[m[1]] === undefined) process.env[m[1]] = m[2];
  }
}
loadDotEnv();

const PORT = parseInt(process.env.PORT || "8787", 10);
const HOST = process.env.HOST || "127.0.0.1";
const HMAC_SECRET = process.env.AGENT_GAMES_HMAC_SECRET || "";
const KURIER_API_KEY = process.env.KURIER_API_KEY || "";
const KURIER_BASE = process.env.KURIER_BASE || "https://api.kurier.xyz/api/v1";
const TASK_ID_MODE = (process.env.TASK_ID_MODE || "keccak").toLowerCase();
const RESPONSE_BUDGET_MS = parseInt(process.env.RESPONSE_BUDGET_MS || "55000", 10);
const KURIER_WAIT_MS = parseInt(process.env.KURIER_WAIT_MS || "40000", 10);
const SIGNATURE_FORMAT = (process.env.SIGNATURE_FORMAT || "hex").toLowerCase();

const GATEKEEPER_VK_HASH =
  "0x6b79c6012a6d8651f3e13bc4d2a20370280ab49700c90c5316d4168bfbad77b0";
const WASM_PATH = path.join(ROOT, "..", "artifacts", "gatekeeper.wasm");
const ZKEY_PATH = path.join(ROOT, "..", "artifacts", "gatekeeper_final.zkey");
const SEEN_PATH = path.join(ROOT, "data", "seen_proofs.json");
const LOG_PATH = path.join(ROOT, "logs", "tasks.jsonl");

const BN128_PRIME =
  21888242871839275222246405745257275088548364400416034343698204186575808495617n;

if (!HMAC_SECRET) {
  console.error("FATAL: AGENT_GAMES_HMAC_SECRET is not set (see .env.example)");
  process.exit(1);
}

// ---------------------------------------------------------------- logging --
function logEvent(obj) {
  const line = JSON.stringify({ ts: new Date().toISOString(), ...obj });
  console.log(line);
  try { fs.appendFileSync(LOG_PATH, line + "\n"); } catch (_) {}
}

// ------------------------------------------------------------- seen store --
let seen = new Set();
try {
  if (fs.existsSync(SEEN_PATH)) {
    seen = new Set(JSON.parse(fs.readFileSync(SEEN_PATH, "utf8")));
  }
} catch (e) {
  logEvent({ event: "seen_store_load_failed", error: String(e) });
}
function persistSeen() {
  const tmp = SEEN_PATH + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify([...seen]));
  fs.renameSync(tmp, SEEN_PATH);
}

// ----------------------------------------------------------------- crypto --
function hmacHex(secret, bodyBuf) {
  return crypto.createHmac("sha256", secret).update(bodyBuf).digest("hex");
}
function hmacBase64(secret, bodyBuf) {
  return crypto.createHmac("sha256", secret).update(bodyBuf).digest("base64");
}
function signBody(bodyBuf) {
  return SIGNATURE_FORMAT === "base64"
    ? hmacBase64(HMAC_SECRET, bodyBuf)
    : hmacHex(HMAC_SECRET, bodyBuf);
}
function verifySignature(bodyBuf, header) {
  if (!header || typeof header !== "string") return false;
  const candidates = [
    hmacHex(HMAC_SECRET, bodyBuf),
    hmacBase64(HMAC_SECRET, bodyBuf),
    "sha256=" + hmacHex(HMAC_SECRET, bodyBuf),
  ];
  const given = Buffer.from(header.trim());
  return candidates.some((c) => {
    const exp = Buffer.from(c);
    return exp.length === given.length && crypto.timingSafeEqual(exp, given);
  });
}

// --------------------------------------------------------- field encoding --
function toField(value) {
  let v;
  if (typeof value === "number") v = BigInt(value);
  else if (typeof value === "bigint") v = value;
  else if (typeof value === "string") {
    const s = value.trim();
    if (/^0x[0-9a-fA-F]+$/.test(s)) v = BigInt(s);
    else if (/^[0-9]+$/.test(s)) v = BigInt(s);
    else throw new Error("not a numeric field value: " + s.slice(0, 40));
  } else throw new Error("unsupported field value type: " + typeof value);
  const r = v % BN128_PRIME;
  return (r < 0n ? r + BN128_PRIME : r).toString();
}
// task_id is a string like "gk_24_9d1"; its conversion to a field element is
// NOT documented by the platform. TASK_ID_MODE picks the strategy; calibrate
// during practice (see NOTES.md).
function taskIdToField(taskId) {
  const s = String(taskId);
  if (/^0x[0-9a-fA-F]+$/.test(s) || /^[0-9]+$/.test(s)) return toField(s);
  if (TASK_ID_MODE === "sha256") {
    const h = crypto.createHash("sha256").update(s, "utf8").digest("hex");
    return (BigInt("0x" + h) % BN128_PRIME).toString();
  }
  if (TASK_ID_MODE === "numeric") {
    const digits = s.replace(/[^0-9]/g, "");
    return toField(digits === "" ? "0" : digits);
  }
  // default: keccak
  const h = ethers.keccak256(ethers.toUtf8Bytes(s));
  return (BigInt(h) % BN128_PRIME).toString();
}
function randomSalt() {
  return BigInt("0x" + crypto.randomBytes(16).toString("hex")).toString();
}

// ----------------------------------------------------------------- kurier --
async function fetchWithTimeout(url, options, timeoutMs) {
  const ctrl = new AbortController();
  const t = setTimeout(() => ctrl.abort(), timeoutMs);
  try { return await fetch(url, { ...options, signal: ctrl.signal }); }
  finally { clearTimeout(t); }
}
// Submit our decision proof to zkVerify via Kurier and poll to Finalized,
// bounded by `deadlineMs` (epoch). Returns { status, txHash } or null when
// Kurier is not configured / unreachable. Never throws.
async function kurierSubmitAndWait(proof, publicSignals, deadlineMs) {
  if (!KURIER_API_KEY) return null;
  try {
    const submitRes = await fetchWithTimeout(
      `${KURIER_BASE}/submit-proof/${KURIER_API_KEY}`,
      {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({
          proofType: "groth16",
          vkRegistered: true,
          proofOptions: { library: "snarkjs", curve: "bn128" },
          proofData: { proof, publicSignals, vk: GATEKEEPER_VK_HASH },
        }),
      },
      10000
    );
    const job = await submitRes.json().catch(() => ({}));
    if (!submitRes.ok || !job.jobId) {
      logEvent({ event: "kurier_submit_failed", status: submitRes.status, body: job });
      return null;
    }
    if (job.optimisticVerify && job.optimisticVerify !== "success") {
      logEvent({ event: "kurier_optimistic_verify_failed", jobId: job.jobId });
      return { status: "Failed", txHash: null, jobId: job.jobId };
    }
    let last = { status: "Submitted", txHash: null, jobId: job.jobId };
    while (Date.now() < deadlineMs) {
      await new Promise((r) => setTimeout(r, 3000));
      try {
        const stRes = await fetchWithTimeout(
          `${KURIER_BASE}/job-status/${KURIER_API_KEY}/${job.jobId}`, {}, 10000
        );
        const st = await stRes.json().catch(() => ({}));
        if (st.status) last = { status: st.status, txHash: st.txHash || last.txHash, jobId: job.jobId };
        if (st.status === "Finalized" || st.status === "Failed") break;
      } catch (_) { /* keep polling until the budget runs out */ }
    }
    return last;
  } catch (e) {
    logEvent({ event: "kurier_error", error: String(e && e.message || e) });
    return null;
  }
}

// -------------------------------------------------------------- decisions --
const REASON_PRECEDENCE = [
  ["vkMatch", "VK_SUBSTITUTION"],
  ["notReused", "PROOF_REUSED"],
  ["notExpired", "EXPIRED_CONDITION"],
  ["thresholdOk", "THRESHOLD_MISMATCH"],
  ["recipientOk", "RECIPIENT_MISMATCH"],
  ["amountOk", "AMOUNT_OVERFLOW"],
];

async function handleTask(envelope, receivedAt) {
  const input = envelope.input || {};
  const started = Date.now();
  const respondBy = Math.min(
    envelope.deadline_at ? Date.parse(envelope.deadline_at) || Infinity : Infinity,
    receivedAt + RESPONSE_BUDGET_MS
  );

  // --- field extraction (BigInt; throw => malformed => fail closed) ---
  const regVk = toField(input.registered_vk);
  const proofVk = toField(input.proof_vk);
  const minimum = BigInt(toField(input.minimum));
  const publicBalance = BigInt(toField(input.public_balance));
  const expiryBlock = BigInt(toField(input.expiry_block));
  const currentBlock = BigInt(toField(input.current_block));
  const recipient = toField(input.recipient);
  const conditionRecipient = toField(input.condition_recipient);
  const amount = BigInt(toField(input.amount));
  const maxTransfer = BigInt(toField(input.max_transfer));
  const proofTxKey = String(input.proof_tx || "").toLowerCase();

  // --- checks (mirror the circuit exactly) ---
  const checks = {
    vkMatch: regVk === proofVk,
    notReused: proofTxKey !== "" && !seen.has(proofTxKey),
    notExpired: currentBlock < expiryBlock,
    thresholdOk: publicBalance >= minimum,
    recipientOk: recipient === conditionRecipient,
    amountOk: amount <= maxTransfer,
  };
  const failed = REASON_PRECEDENCE.filter(([k]) => !checks[k]);
  const decision = failed.length === 0 ? "APPROVE" : "REJECT";
  const reason_code = decision === "APPROVE" ? "VALID_CONDITION" : failed[0][1];

  // Record the proof reference as seen AFTER evaluating this task.
  if (proofTxKey) { seen.add(proofTxKey); try { persistSeen(); } catch (_) {} }

  const response = { decision, reason_code };

  // --- our Groth16 decision proof (skipped for PROOF_REUSED by the rules) ---
  let kurier = null;
  if (reason_code !== "PROOF_REUSED") {
    try {
      const circuitInput = {
        registeredVkHash: regVk,
        proofVkHash: proofVk,
        minimum: minimum.toString(),
        publicBalance: publicBalance.toString(),
        expiryBlock: expiryBlock.toString(),
        currentBlock: currentBlock.toString(),
        recipient,
        conditionRecipient,
        amount: amount.toString(),
        maxTransfer: maxTransfer.toString(),
        taskId: taskIdToField(envelope.task_id),
        salt: randomSalt(),
        decision: decision === "APPROVE" ? "1" : "0",
      };
      const { proof, publicSignals } = await snarkjs.groth16.fullProve(
        circuitInput, WASM_PATH, ZKEY_PATH
      );
      response.proof = proof;
      response.public_signals = publicSignals;

      // On-chain finalization of OUR proof (optional audit pointer).
      const waitUntil = Math.min(respondBy - 2000, Date.now() + KURIER_WAIT_MS);
      if (waitUntil > Date.now()) {
        kurier = await kurierSubmitAndWait(proof, publicSignals, waitUntil);
        if (kurier && kurier.txHash) response.proof_tx = kurier.txHash;
      }
    } catch (e) {
      // Proof generation failed (should not happen if logic mirrors the
      // circuit). Fail closed: force REJECT, ship no proof.
      logEvent({ event: "proof_generation_failed", task_id: envelope.task_id, error: String(e && e.message || e) });
      response.decision = "REJECT";
      if (response.reason_code === "VALID_CONDITION") response.reason_code = "PROOF_GENERATION_FAILED";
      delete response.proof; delete response.public_signals;
    }
  } else {
    // Echo the reused reference as the audit pointer.
    if (input.proof_tx) response.proof_tx = input.proof_tx;
  }

  logEvent({
    event: "task", task_id: envelope.task_id, mode: envelope.mode || null,
    decision: response.decision, reason_code: response.reason_code,
    checks, proof: Boolean(response.proof),
    kurier: kurier ? kurier.status : (KURIER_API_KEY ? "skipped" : "not_configured"),
    latency_ms: Date.now() - started,
  });
  return response;
}

// ----------------------------------------------------------------- server --
function sendJson(res, status, obj) {
  const body = Buffer.from(JSON.stringify(obj));
  res.writeHead(status, {
    "content-type": "application/json",
    "x-agent-games-signature": signBody(body),
  });
  res.end(body);
}

// Serialize task handling so the seen-set ordering stays deterministic.
let taskChain = Promise.resolve();
function enqueueTask(fn) {
  const run = taskChain.then(fn, fn);
  taskChain = run.catch(() => {});
  return run;
}

const server = http.createServer((req, res) => {
  const receivedAt = Date.now();
  if (req.method === "GET" && (req.url === "/healthz" || req.url === "/")) {
    return sendJson(res, 200, { ok: true, protocolVersion: "v1", agent: "proof-gatekeeper" });
  }
  if (req.method !== "POST" || (req.url !== "/agent" && req.url !== "/")) {
    return sendJson(res, 404, { ok: false, error: "not found" });
  }
  const chunks = [];
  let size = 0;
  req.on("data", (c) => {
    size += c.length;
    if (size > 1024 * 1024) { req.destroy(); return; }
    chunks.push(c);
  });
  req.on("end", async () => {
    const raw = Buffer.concat(chunks);
    // 1) HMAC over the RAW body, before parsing. Fail closed.
    if (!verifySignature(raw, req.headers["x-agent-games-signature"])) {
      logEvent({ event: "bad_signature", bytes: raw.length });
      return sendJson(res, 401, { ok: false, error: "invalid signature" });
    }
    let envelope;
    try { envelope = JSON.parse(raw.toString("utf8")); }
    catch (_) { return sendJson(res, 400, { ok: false, error: "invalid json" }); }

    try {
      if (envelope.type === "agent-games.preflight.v1") {
        logEvent({ event: "preflight", agent_id: envelope.agent_id || null });
        return sendJson(res, 200, { ok: true, protocolVersion: "v1" });
      }
      if (envelope.type === "agent-games.proof-gatekeeper.v1") {
        const response = await enqueueTask(() => handleTask(envelope, receivedAt));
        return sendJson(res, 200, response);
      }
      return sendJson(res, 400, { ok: false, error: "unknown type" });
    } catch (e) {
      // Fail closed on any internal error while handling a task.
      logEvent({ event: "handler_error", type: envelope && envelope.type, error: String(e && e.message || e) });
      if (envelope && envelope.type === "agent-games.proof-gatekeeper.v1") {
        return sendJson(res, 200, { decision: "REJECT", reason_code: "INTERNAL_ERROR" });
      }
      return sendJson(res, 500, { ok: false, error: "internal error" });
    }
  });
});

server.listen(PORT, HOST, () => {
  logEvent({
    event: "listening", host: HOST, port: PORT,
    kurier: KURIER_API_KEY ? "configured" : "not_configured",
    task_id_mode: TASK_ID_MODE, seen_loaded: seen.size,
  });
});
