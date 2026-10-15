#!/usr/bin/env python3
"""DEP-1.1-1.5, VER-2, VER-3 and VER-8 (strategy.md section 5.10) against a
NEAR JSON-RPC endpoint. Run through check_deployment.sh <net>.

Configuration: [deployment.<net>] in projects/near-approval/status.toml. Any
key can be overridden by the environment as CHECK_<KEY> (upper case), which
is how the sandbox demo (sandbox/tests/deploy.rs) points it at a local
near-sandbox whose port and accounts change per run.

Keys
  rpc_url             JSON-RPC endpoint. VER-2/VER-3/VER-8 query past blocks,
                      so on a public network it must be archival.
  contract_account    C
  expected_code_hash  base58(sha256(wasm)), NEAR's code_hash (DEP-1.1, VER-2)
  wasm_sha256         hex sha256 of the reproducible build; must match
                      expected_code_hash (and APPROVAL_WASM, if set)
  lock_tx_hash        the DEP-1.2 transaction: deploy + new + delete every
  lock_tx_signer      full-access key of C, signed by C (lock_tx_signer = C)
  owner_code_hashes   DEP-1.3: code hashes of accepted multisig/DAO contracts
  allow_plain_owner   true: a plain-account owner is a WARN, not a FAIL
                      (sandbox only)
  balance_buffer_near DEP-1.5: free balance above storage staking
  indexer             "rpc-scan": rebuild receipts to C by walking every
                      block from b0 over RPC (local chains only); "": none,
                      so DEP-1.4, VER-3's scan and VER-8 FAIL as unchecked
  scan_max_blocks     refuse rpc-scan over more blocks than this

Exit status: 0 if no check FAILed, 1 otherwise, 2 on a usage/config error.
`--facts FILE` writes the VER-8 observations as Prolog facts for
prolog/verification/verifier_rules.pl; `--json FILE` writes the results.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import pathlib
import sys
import time
import tomllib
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
STATUS = HERE.parent / "status.toml"
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
YOCTO_PER_BYTE = 10**19
FORBIDDEN = {"DeployContract", "UseGlobalContract", "UseGlobalContractByAccountId", "AddKey", "DeleteAccount"}
ROLE_METHODS = {"agent": [["request_action"]], "approver": [["approve"], ["approve", "reject"]]}


def b58(data: bytes) -> str:
    n = int.from_bytes(data, "big")
    s = ""
    while n:
        n, r = divmod(n, 58)
        s = B58[r] + s
    return "1" * (len(data) - len(data.lstrip(b"\0"))) + s


class Rpc:
    def __init__(self, url: str):
        self.url = url
        self.n = 0

    def call(self, method: str, params):
        self.n += 1
        body = json.dumps({"jsonrpc": "2.0", "id": self.n, "method": method, "params": params}).encode()
        req = urllib.request.Request(self.url, body, {"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=60) as r:
            out = json.load(r)
        if "error" in out:
            raise RpcError(out["error"])
        return out["result"]

    def query(self, at: dict, **params):
        return self.call("query", {**params, **at})

    def view(self, contract: str, method: str, args: dict, at: dict):
        r = self.query(at, request_type="call_function", account_id=contract, method_name=method,
                       args_base64=base64.b64encode(json.dumps(args).encode()).decode())
        return json.loads(bytes(r["result"]) or b"null")


class RpcError(Exception):
    pass


def final() -> dict:
    return {"finality": "final"}


def at_block(h: int) -> dict:
    return {"block_id": h}


def action_name(a) -> str:
    return a if isinstance(a, str) else next(iter(a))


def permission(view) -> tuple:
    """('full_access',) | ('missing',) | ('function_call', receiver, sorted methods, allowance|None)"""
    if view is None:
        return ("missing",)
    p = view["permission"]
    if p == "FullAccess":
        return ("full_access",)
    fc = p["FunctionCall"]
    return ("function_call", fc["receiver_id"], sorted(fc["method_names"]), fc.get("allowance"))


def perm_ok(perm: tuple, c: str, role: str) -> bool:
    return (perm[0] == "function_call" and perm[1] == c and perm[2] in ROLE_METHODS[role]
            and perm[3] is not None)


def pl_atom(s) -> str:
    return "'" + str(s).replace("\\", "\\\\").replace("'", "\\'") + "'"


def pl_perm(perm: tuple) -> str:
    if perm[0] != "function_call":
        return perm[0]
    allowance = "unlimited" if perm[3] is None else str(int(perm[3]))
    return f"function_call({pl_atom(perm[1])}, [{', '.join(pl_atom(m) for m in perm[2])}], {allowance})"


class Checker:
    def __init__(self, cfg: dict):
        self.cfg = cfg
        self.rpc = Rpc(cfg["rpc_url"])
        self.c = cfg["contract_account"]
        self.results: list[dict] = []
        self.facts: list[str] = []

    def report(self, rid: str, verdict: str, detail: str):
        self.results.append({"id": rid, "verdict": verdict, "detail": detail})
        print(f"{verdict:4} {rid}: {detail}")

    def access_key(self, account: str, key: str, at: dict):
        try:
            return self.rpc.query(at, request_type="view_access_key", account_id=account, public_key=key)
        except RpcError as e:
            if "UNKNOWN_ACCESS_KEY" in json.dumps(e.args[0]) or "does not exist" in json.dumps(e.args[0]):
                return None
            raise

    def key_list(self, at: dict) -> list:
        try:
            return self.rpc.query(at, request_type="view_access_key_list", account_id=self.c)["keys"]
        except RpcError as e:
            if "UNKNOWN_ACCOUNT" in json.dumps(e.args[0]):
                return []
            raise

    def account(self, account: str, at: dict):
        try:
            return self.rpc.query(at, request_type="view_account", account_id=account)
        except RpcError as e:
            if "UNKNOWN_ACCOUNT" in json.dumps(e.args[0]):
                return None
            raise

    def height_of(self, block_hash: str) -> int:
        return self.rpc.call("block", {"block_id": block_hash})["header"]["height"]

    # -- indexer --------------------------------------------------------------
    def scan(self, b0: int, head: int):
        """Every receipt executed on C from b0 to head, in execution order, with
        its originating transaction. Walks blocks and chunks over RPC and asks
        EXPERIMENTAL_tx_status for each transaction found (rpc-scan indexer)."""
        mode = self.cfg.get("indexer", "")
        if mode != "rpc-scan":
            return None
        limit = int(self.cfg.get("scan_max_blocks", 20000))
        if head - b0 > limit:
            raise SystemExit(f"rpc-scan over {head - b0} blocks exceeds scan_max_blocks={limit}; use an indexer")
        txs = []
        for h in range(b0, head + 1):
            try:
                block = self.rpc.call("block", {"block_id": h})
            except RpcError:
                continue  # skipped height
            for ch in block["chunks"]:
                if ch.get("height_included") != h:
                    continue
                chunk = self.rpc.call("chunk", {"chunk_id": ch["chunk_hash"]})
                for tx in chunk["transactions"]:
                    txs.append((h, tx["hash"], tx["signer_id"]))
        out = []
        for incl, txh, signer in txs:
            st = self.rpc.call("EXPERIMENTAL_tx_status",
                               {"tx_hash": txh, "sender_account_id": signer, "wait_until": "FINAL"})
            outcomes = {o["id"]: o for o in st["receipts_outcome"]}
            seen = set()
            for r in st.get("receipts", []):
                if r["receiver_id"] != self.c or "Action" not in r["receipt"]:
                    continue
                o = outcomes.get(r["receipt_id"])
                if o is None:
                    continue
                seen.add(r["receipt_id"])
                act = r["receipt"]["Action"]
                out.append({
                    "tx": txh, "tx_block": incl, "exec_block": self.height_of(o["block_hash"]),
                    "predecessor": r["predecessor_id"], "signer": act["signer_id"],
                    "signer_pk": act["signer_public_key"], "actions": act["actions"],
                    "status": o["outcome"]["status"],
                })
            # A transaction whose signer is its receiver becomes a local receipt,
            # which tx_status does not list: take its actions from the transaction.
            tx = st["transaction"]
            first = st["transaction_outcome"]["outcome"]["status"].get("SuccessReceiptId")
            if tx["receiver_id"] == self.c and first and first not in seen and first in outcomes:
                o = outcomes[first]
                out.append({
                    "tx": txh, "tx_block": incl, "exec_block": self.height_of(o["block_hash"]),
                    "predecessor": tx["signer_id"], "signer": tx["signer_id"],
                    "signer_pk": tx["public_key"], "actions": tx["actions"],
                    "status": o["outcome"]["status"],
                })
        out.sort(key=lambda r: r["exec_block"])
        return out

    # -- the checks -----------------------------------------------------------
    def run(self) -> int:
        cfg, c, rpc = self.cfg, self.c, self.rpc
        expected = cfg.get("expected_code_hash", "")
        wasm_sha = cfg.get("wasm_sha256", "")
        if not (c and expected and wasm_sha):
            raise SystemExit("contract_account, expected_code_hash and wasm_sha256 must be set")
        # Let finality catch up with what was already sent (a no-op on a live
        # network, where it lags by about two blocks).
        target = rpc.call("block", {"finality": "optimistic"})["header"]["height"]
        deadline = time.time() + 60
        while (head := rpc.call("block", final())["header"]["height"]) < target and time.time() < deadline:
            time.sleep(0.2)

        # DEP-1.1 / VER-2 (now)
        problems = []
        if b58(bytes.fromhex(wasm_sha)) != expected:
            problems.append(f"wasm_sha256 {wasm_sha} is not base58-decodable to expected_code_hash {expected}")
        wasm = os.environ.get("APPROVAL_WASM")
        if wasm and hashlib.sha256(pathlib.Path(wasm).read_bytes()).hexdigest() != wasm_sha:
            problems.append(f"APPROVAL_WASM {wasm} is not wasm_sha256")
        acct = self.account(c, final())
        if acct is None:
            problems.append(f"{c} does not exist")
        else:
            if acct["code_hash"] != expected:
                problems.append(f"code_hash {acct['code_hash']} != expected {expected}")
            if acct.get("global_contract_account_id"):
                problems.append(f"uses global contract by account id {acct['global_contract_account_id']} (its owner can replace the code)")
            if acct.get("global_contract_hash") and acct["global_contract_hash"] != expected:
                problems.append(f"global contract hash {acct['global_contract_hash']} != expected")
        self.report("DEP-1.1", "FAIL" if problems else "PASS", "; ".join(problems) or f"code_hash {expected}")

        # DEP-1.2: the lock transaction
        b0 = None
        lock_tx = cfg.get("lock_tx_hash", "")
        if not lock_tx:
            self.report("DEP-1.2", "FAIL", "lock_tx_hash not configured")
        else:
            st = rpc.call("EXPERIMENTAL_tx_status", {"tx_hash": lock_tx, "sender_account_id": cfg.get("lock_tx_signer") or c, "wait_until": "FINAL"})
            tx = st["transaction"]
            names = [action_name(a) for a in tx["actions"]]
            b0 = self.height_of(st["transaction_outcome"]["block_hash"])
            exec_blocks = [self.height_of(o["block_hash"]) for o in st["receipts_outcome"]]
            done = max([b0] + exec_blocks)
            problems = []
            if tx["signer_id"] != c or tx["receiver_id"] != c:
                problems.append(f"signer/receiver {tx['signer_id']}/{tx['receiver_id']} != {c}")
            if "SuccessValue" not in st["status"]:
                problems.append(f"lock tx failed: {st['status']}")
            new = [a for a in tx["actions"] if action_name(a) == "FunctionCall" and a["FunctionCall"]["method_name"] == "new"]
            if "DeployContract" not in names or not new:
                problems.append(f"actions {names} lack DeployContract or new")
            deleted = {a["DeleteKey"]["public_key"] for a in tx["actions"] if action_name(a) == "DeleteKey"}
            before = {k["public_key"] for k in self.key_list(at_block(b0 - 1))}
            if not before <= deleted:
                problems.append(f"keys of C before b0 not deleted by the lock tx: {sorted(before - deleted)}")
            after = self.key_list(at_block(done + 1))
            if after:
                problems.append(f"{len(after)} access key(s) on C right after the lock: {[k['public_key'] for k in after]}")
            code_after = self.account(c, at_block(done + 1))
            if not code_after or code_after["code_hash"] != expected:
                problems.append("code right after the lock is not the expected code")
            self.report("DEP-1.2", "FAIL" if problems else "PASS",
                        "; ".join(problems) or f"b0={b0}: {names}, no keys on C at b0+1")

        # DEP-1.3: owner is a multisig/DAO
        owner = None
        try:
            owner = rpc.view(c, "get_owner", {}, final())
            oacct = self.account(owner, final())
            ch = oacct["code_hash"] if oacct else None
            if ch in cfg.get("owner_code_hashes", []):
                self.report("DEP-1.3", "PASS", f"owner {owner} runs accepted contract {ch}")
            elif cfg.get("allow_plain_owner"):
                self.report("DEP-1.3", "WARN", f"owner {owner} code_hash {ch} is not an accepted multisig/DAO (allow_plain_owner)")
            else:
                self.report("DEP-1.3", "FAIL", f"owner {owner} code_hash {ch} not in owner_code_hashes")
        except RpcError as e:
            self.report("DEP-1.3", "FAIL", f"get_owner: {e}")

        # Receipts to C since b0 (indexer)
        receipts = self.scan(b0, head) if b0 is not None else None

        # DEP-1.4: registered keys are DEP-1.4 function-call keys
        registry = None
        if receipts is None:
            self.report("DEP-1.4", "FAIL", "no indexer: the registered-key set can't be rebuilt (indexer = \"\")")
        else:
            registry = {}
            for r in receipts:
                if "SuccessValue" not in r["status"]:
                    continue
                for a in r["actions"]:
                    if action_name(a) != "FunctionCall":
                        continue
                    fc = a["FunctionCall"]
                    args = json.loads(base64.b64decode(fc["args"]) or b"{}")
                    m = fc["method_name"]
                    if m in ("add_agent", "add_approver"):
                        registry[args["public_key"]] = (args["account_id"], "agent" if m == "add_agent" else "approver")
                    elif m == "revoke_key":
                        registry.pop(args["public_key"], None)
            problems = []
            for key, (account, role) in sorted(registry.items()):
                perm = permission(self.access_key(account, key, final()))
                if not perm_ok(perm, c, role):
                    problems.append(f"{role} key {key} of {account}: {perm}")
                p = rpc.view(c, "get_principal", {"public_key": key}, final())
                if not p or p["account_id"] != account or p["role"] != role:
                    problems.append(f"indexer registry disagrees with get_principal({key}) = {p}")
            self.report("DEP-1.4", "FAIL" if problems else "PASS",
                        "; ".join(problems) or f"{len(registry)} registered key(s), all function-call keys scoped to C")

        # DEP-1.5: balance buffer
        if acct:
            free = int(acct["amount"]) - acct["storage_usage"] * YOCTO_PER_BYTE
            buf = int(float(cfg.get("balance_buffer_near", "1")) * 10**24)
            self.report("DEP-1.5", "PASS" if free >= buf else "FAIL",
                        f"free {free / 1e24:.4f} NEAR over storage, buffer {buf / 1e24:g} NEAR")
        else:
            self.report("DEP-1.5", "FAIL", "no account")

        # VER-3: no full-access key since b0, no forbidden receipts
        if b0 is None:
            self.report("VER-3", "FAIL", "no b0 (lock_tx_hash)")
        else:
            problems = []
            now_keys = [k for k in self.key_list(final()) if k["access_key"]["permission"] == "FullAccess"]
            if now_keys:
                problems.append(f"full-access key(s) on C now: {[k['public_key'] for k in now_keys]}")
            if self.account(c, final()) is None:
                problems.append("C does not exist now")
            if receipts is None:
                problems.append("no indexer: receipts to C since b0 not scanned")
            else:
                for r in receipts:
                    if r["tx"] == lock_tx:
                        continue
                    bad = [action_name(a) for a in r["actions"] if action_name(a) in FORBIDDEN]
                    if bad:
                        problems.append(f"{bad} on C at block {r['exec_block']} (tx {r['tx']})")
            self.report("VER-3", "FAIL" if problems else "PASS",
                        "; ".join(problems) or f"no full-access key and no deploy/add-key/delete receipt on C since b0={b0}")

        # Proofs (VER-5 loop at one block), then VER-2 and VER-8 per proof
        proofs = []
        try:
            frm = 0
            while True:
                page = rpc.view(c, "get_approvals", {"from_index": frm, "limit": 100}, at_block(head))
                if not page:
                    break
                proofs += page
                frm += len(page)
        except RpcError as e:
            self.report("VER-5", "FAIL", f"get_approvals: {e}")
        problems = []
        for p in proofs:
            at = self.account(c, at_block(p["approved_at_block"]))
            if not at or at["code_hash"] != expected:
                problems.append(f"proof {p['request_id']}: code_hash at block {p['approved_at_block']} is {at and at['code_hash']}")
        self.report("VER-2", "FAIL" if problems else "PASS",
                    "; ".join(problems) or f"code_hash = expected now and at all {len(proofs)} proof block(s)")

        problems = []
        if receipts is None and proofs:
            problems.append("no indexer: request/approval transactions not located")
        elif receipts is not None:
            req_tx, appr_tx = {}, {}
            for r in receipts:
                if "SuccessValue" not in r["status"]:
                    continue
                ret = json.loads(base64.b64decode(r["status"]["SuccessValue"]) or b"null")
                for a in r["actions"]:
                    if action_name(a) != "FunctionCall":
                        continue
                    m = a["FunctionCall"]["method_name"]
                    if m == "request_action":
                        req_tx[ret] = r
                    elif m == "approve":
                        appr_tx[ret["request_id"]] = r
            for p in proofs:
                i = p["request_id"]
                rq, ap = req_tx.get(i), appr_tx.get(i)
                if not rq or not ap:
                    problems.append(f"proof {i}: request or approval receipt not found")
                    continue
                ak = permission(self.access_key(p["agent_account_id"], p["agent_public_key"], at_block(rq["tx_block"])))
                pk = permission(self.access_key(p["approver_account_id"], p["approver_public_key"], at_block(ap["tx_block"])))
                self.facts.append(
                    f"ver8_obs({pl_atom(c)}, proof({pl_atom(c)}, {i}, {pl_atom(p['action'])}, "
                    f"{pl_atom(p['agent_account_id'])}, {pl_atom(p['agent_public_key'])}, "
                    f"{pl_atom(p['approver_account_id'])}, {pl_atom(p['approver_public_key'])}, {p['approved_at_ns']}), "
                    f"key({pl_atom(p['agent_account_id'])}, {pl_atom(p['agent_public_key'])}, {pl_perm(ak)}), "
                    f"key({pl_atom(p['approver_account_id'])}, {pl_atom(p['approver_public_key'])}, {pl_perm(pk)})).")
                if not perm_ok(ak, c, "agent"):
                    problems.append(f"proof {i}: agent key at block {rq['tx_block']} is {ak}")
                if not perm_ok(pk, c, "approver"):
                    problems.append(f"proof {i}: approver key at block {ap['tx_block']} is {pk}")
        self.report("VER-8", "FAIL" if problems else "PASS",
                    "; ".join(problems) or f"{len(proofs)} proof(s): both keys DEP-1.4 function-call keys at their tx blocks")
        return 1 if any(r["verdict"] == "FAIL" for r in self.results) else 0


def load_config(net: str) -> dict:
    data = tomllib.loads(STATUS.read_text())
    cfg = dict(data.get("deployment", {}).get(net, {}))
    if not cfg and net not in data.get("deployment", {}):
        raise SystemExit(f"no [deployment.{net}] in {STATUS}")
    for k in list(cfg) + ["rpc_url", "contract_account", "expected_code_hash", "wasm_sha256", "lock_tx_hash",
                           "lock_tx_signer", "indexer", "allow_plain_owner", "balance_buffer_near", "scan_max_blocks"]:
        v = os.environ.get("CHECK_" + k.upper())
        if v is not None:
            cfg[k] = {"true": True, "false": False}.get(v, v)
    if os.environ.get("CHECK_OWNER_CODE_HASHES"):
        cfg["owner_code_hashes"] = os.environ["CHECK_OWNER_CODE_HASHES"].split(",")
    if not cfg.get("rpc_url"):
        raise SystemExit(f"[deployment.{net}] rpc_url is empty")
    return cfg


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("net")
    ap.add_argument("--facts", help="write VER-8 observations as Prolog facts")
    ap.add_argument("--json", help="write the results as JSON")
    a = ap.parse_args()
    try:
        ch = Checker(load_config(a.net))
        code = ch.run()
    except SystemExit as e:
        print(f"check_deployment: {e}", file=sys.stderr)
        return 2
    if a.facts:
        pathlib.Path(a.facts).write_text("\n".join(ch.facts) + "\n")
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps(ch.results, indent=2) + "\n")
    print(f"check_deployment {a.net}: {'FAIL' if code else 'PASS'} ({ch.rpc.n} RPC calls)")
    return code


if __name__ == "__main__":
    sys.exit(main())
