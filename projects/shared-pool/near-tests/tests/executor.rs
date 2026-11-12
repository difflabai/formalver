//! The synthetic executor (crates/executor/src/lib.rs), alone and wired to
//! the pool (EX-1..EX-5).
//!
//! Alone: every call runs on the host path (`call_t::<Executor>`) and on the
//! wasm of both builds, from a stored state that is checked byte for byte
//! against a Borsh mirror of `Executor` (fields are private upstream).
//! Wired: `Net` runs the pool and executor wasm with a receipt router, so
//! `dispatch -> execute -> on_result`, `reconcile -> status -> on_result` and
//! `finish/confirm_not_executed -> settle` run as the runtime would chain
//! them.
//!
//! The end-to-end flows also check the pool's side of the chain (SH-3,
//! SH-6, SH-7). `ex5_settle_before_callback_is_absorbed` is pool-only: the
//! late-callback half of RT-RACE in the mocked runtime.
//!
// PROP: EX-1 EX-2 EX-3 EX-4 EX-5 SH-3 SH-6 SH-7 RT-RACE

mod common;
use common::*;
use near_sdk::borsh::{self, BorshDeserialize, BorshSerialize};
use near_sdk::serde_json::{self, json, Value};
use near_sdk::{env, AccountId};
use pool_core::Status;
use pool_executor::Executor;

/// The executor's account in these tests (recipe 0 of `open_config` names it).
const EX: &str = X1;

#[derive(BorshSerialize, BorshDeserialize, Clone, Debug, PartialEq)]
#[borsh(crate = "near_sdk::borsh")]
struct JobM {
    id: u32,
    recipe: u32,
    units: u32,
    status: String,
}

/// Borsh mirror of `Executor { lock, operator, jobs, mode }`.
#[derive(BorshSerialize, BorshDeserialize, Clone, Debug, PartialEq)]
#[borsh(crate = "near_sdk::borsh")]
struct ExecM {
    lock: AccountId,
    operator: AccountId,
    jobs: Vec<JobM>,
    mode: String,
}

fn job(id: u32, recipe: u32, units: u32, status: &str) -> JobM {
    JobM { id, recipe, units, status: status.into() }
}

fn fresh() -> ExecM {
    ExecM { lock: acct(POOL), operator: acct(OPERATOR), jobs: vec![], mode: "normal".into() }
}

fn decode(s: &Storage) -> ExecM {
    assert_eq!(s.len(), 1, "executor storage is one STATE key");
    let m: ExecM = borsh::from_slice(&s[STATE_KEY]).expect("Borsh mirror of Executor");
    assert_eq!(borsh::to_vec(&m).unwrap(), s[STATE_KEY], "mirror round trip");
    m
}

fn encode(m: &ExecM) -> Storage {
    let mut s = Storage::new();
    s.insert(STATE_KEY.to_vec(), borsh::to_vec(m).unwrap());
    s
}

fn ctx(who: &str) -> Ctx {
    Ctx::by(who, 100).on(EX)
}

/// One executor call on `path`.
struct XOut {
    /// JSON return (`null` for a Promise or unit), or the failure message as
    /// the path reports it (`None`: the Plain build reports none).
    result: Result<Value, Option<String>>,
    storage: Storage,
    calls: Vec<Call>,
    promise_return: Option<u64>,
    host_calls: Vec<&'static str>,
}

fn ex(path: Path, c: &Ctx, st: &Storage, method: &str, args: Value) -> XOut {
    match path {
        Path::Host => {
            let write = !matches!(method, "status" | "get_jobs");
            let m = method.to_string();
            let a = args.clone();
            let u = move |k: &str| a[k].as_u64().unwrap_or_else(|| panic!("arg {k}")) as u32;
            let out = call_t::<Executor, Value>(c, st.clone(), vec![], write, move |e| match m.as_str() {
                "execute" => json!(e.execute(u("id"), u("recipe"), u("units"))),
                "status" => json!(e.status(u("id"))),
                "finish" => {
                    drop(e.finish(u("id"), args["completed"].as_bool().unwrap()));
                    Value::Null
                }
                "confirm_not_executed" => {
                    drop(e.confirm_not_executed(u("id"), u("recipe"), u("units")));
                    Value::Null
                }
                "set_mode" => {
                    e.set_mode(args["mode"].as_str().unwrap().into());
                    Value::Null
                }
                "get_jobs" => serde_json::to_value(e.get_jobs()).unwrap(),
                other => panic!("no method {other}"),
            });
            assert!(out.logs.is_empty(), "the executor logs nothing");
            XOut {
                result: out.result.map_err(|f| Some(f.msg().to_string())),
                storage: out.storage,
                calls: calls_of(&out.receipts),
                promise_return: None,
                host_calls: vec![],
            }
        }
        Path::Wasm(b) => {
            let w = wasm(b, "pool_executor");
            let out = wasm_call(w, c, st.clone(), vec![], method, &serde_json::to_vec(&args).unwrap());
            assert!(out.forbidden.is_empty(), "{:?}", out.forbidden);
            assert!(out.logs.is_empty(), "the executor logs nothing");
            XOut {
                result: match &out.result {
                    Ok(Some(v)) => Ok(serde_json::from_slice(v).unwrap()),
                    Ok(None) => Ok(Value::Null),
                    Err(f) => Err(f.panic_msg.clone()),
                },
                storage: out.storage.clone(),
                calls: calls_of(&out.receipts),
                promise_return: out.promise_return,
                host_calls: out.host_calls,
            }
        }
    }
}

/// The call failed with a message containing `needle` (as far as the path
/// reports messages), changed nothing and sent nothing.
fn fails(path: Path, out: &XOut, before: &Storage, needle: &str, what: &str) {
    let m = out.result.as_ref().expect_err(what);
    assert_eq!(&out.storage, before, "{what}: failed call changed state");
    assert!(out.calls.is_empty());
    match path {
        Path::Wasm(Build::Plain) => assert_eq!(m, &None, "{what}"),
        _ => {
            let m = m.as_deref().unwrap_or_else(|| panic!("{what}: no message"));
            assert!(m.contains(needle), "{what}: {m:?} lacks {needle:?}");
        }
    }
}

fn ok(out: &XOut, what: &str) -> Value {
    out.result.clone().unwrap_or_else(|e| panic!("{what}: failed {e:?}"))
}

/// Deploys the executor on `path` (`new({lock: POOL, operator: OPERATOR})`
/// by the executor account) and checks the mirror.
fn deploy_ex(path: Path) -> Storage {
    let st = match path {
        Path::Host => {
            install(&ctx(EX), Storage::new(), vec![], &[]);
            let e = Executor::new(acct(POOL), acct(OPERATOR));
            env::state_write(&e);
            drop(e);
            take_storage()
        }
        Path::Wasm(b) => {
            let out = wasm_call(
                wasm(b, "pool_executor"),
                &ctx(EX),
                Storage::new(),
                vec![],
                "new",
                &serde_json::to_vec(&json!({ "lock": POOL, "operator": OPERATOR })).unwrap(),
            );
            assert!(out.result.is_ok(), "{:?}", out.result);
            out.storage
        }
    };
    assert_eq!(decode(&st), fresh());
    st
}

fn exec_args(id: u32, recipe: u32, units: u32) -> Value {
    json!({ "id": id, "recipe": recipe, "units": units })
}

// ---------------------------------------------------------------------------
// EX-1: only the lock executes
// ---------------------------------------------------------------------------

// PROP: EX-1
#[test]
fn ex1_only_the_lock_executes() {
    big_stack(|| {
        for path in paths() {
            let st = deploy_ex(path);
            for (pred, signer) in [(Z, Z), (OPERATOR, OPERATOR), (A1, A1), (EX, EX), (OWNER, POOL), (Z, POOL)] {
                let out = ex(path, &Ctx::new(pred, signer, 100_000_000_000).on(EX), &st, "execute", exec_args(0, 0, 1));
                fails(path, &out, &st, "only lock may execute", &format!("{path:?} execute by {pred}"));
            }
            // The lock's own receipt does, whoever signed the transaction.
            let out = ex(path, &Ctx::new(POOL, Z, 100_000_000_000).on(EX), &st, "execute", exec_args(0, 0, 1));
            assert_eq!(ok(&out, "execute by lock"), json!("active"));
            assert_eq!(decode(&out.storage).jobs, vec![job(0, 0, 1, "active")]);
            assert!(out.calls.is_empty(), "execute sends nothing");
            // status is a view anyone may call.
            for who in [Z, POOL, OPERATOR] {
                let s = ex(path, &ctx(who), &out.storage, "status", json!({ "id": 0 }));
                assert_eq!(ok(&s, "status"), json!("active"));
                assert_eq!(s.storage, out.storage);
                assert!(!s.host_calls.contains(&"storage_write"), "status (&self) wrote");
                let s = ex(path, &ctx(who), &out.storage, "status", json!({ "id": 1 }));
                assert_eq!(ok(&s, "status"), json!("unknown"));
            }
        }
    });
}

/// The executor's `new` is private and runs once; its mutating methods
/// reject deposits (near-sdk wrappers, wasm only).
// PROP: EX-1
#[test]
fn ex1_executor_wrappers() {
    big_stack(|| {
        for b in Build::all() {
            let w = wasm(b, "pool_executor");
            let input = serde_json::to_vec(&json!({ "lock": POOL, "operator": OPERATOR })).unwrap();
            let empty = Storage::new();
            for who in [POOL, OPERATOR, Z] {
                let out = wasm_call(w, &Ctx::new(who, EX, 100_000_000_000).on(EX), empty.clone(), vec![], "new", &input);
                assert_wasm_fail(b, &out, &Fail::Guest("Method new is private".into()), &empty, "executor new");
            }
            let st = deploy_ex(Path::Wasm(b));
            let hijack = serde_json::to_vec(&json!({ "lock": Z, "operator": Z })).unwrap();
            let out = wasm_call(w, &ctx(EX), st.clone(), vec![], "new", &hijack);
            assert_wasm_fail(b, &out, &Fail::Guest("The contract has already been initialized".into()), &st, "re-init");
            let mut active = fresh();
            active.jobs.push(job(0, 0, 1, "active"));
            let st = encode(&active);
            for (method, who, args) in [
                ("execute", POOL, exec_args(1, 0, 1)),
                ("finish", OPERATOR, json!({ "id": 0, "completed": true })),
                ("confirm_not_executed", OPERATOR, exec_args(1, 0, 1)),
                ("set_mode", OPERATOR, json!({ "mode": "reject" })),
            ] {
                let out = wasm_call(w, &ctx(who).with_deposit(1), st.clone(), vec![], method, &serde_json::to_vec(&args).unwrap());
                assert_wasm_fail(b, &out, &Fail::Guest(format!("Method {method} doesn't accept deposit")), &st, method);
                let out = wasm_call(w, &ctx(who), st.clone(), vec![], method, &serde_json::to_vec(&args).unwrap());
                assert!(out.result.is_ok(), "{method}: {:?}", out.result);
            }
        }
    });
}

// ---------------------------------------------------------------------------
// EX-2: a job is bound to its payload; execute is idempotent per id
// ---------------------------------------------------------------------------

// PROP: EX-2
#[test]
fn ex2_payload_binding_and_dedupe() {
    big_stack(|| {
        for path in paths() {
            let pool = Ctx::by(POOL, 100).on(EX);
            let mut st = deploy_ex(path);
            let out = ex(path, &pool, &st, "execute", exec_args(4, 1, 3));
            assert_eq!(ok(&out, "first"), json!("active"));
            st = out.storage;
            // Same payload: the recorded status, no second job.
            let again = ex(path, &pool, &st, "execute", exec_args(4, 1, 3));
            assert_eq!(ok(&again, "replay"), json!("active"));
            assert_eq!(again.storage, st);
            // Another payload under the same id: refused.
            for (r, u) in [(1, 4), (0, 3), (2, 2)] {
                let out = ex(path, &pool, &st, "execute", exec_args(4, r, u));
                fails(path, &out, &st, "payload mismatch", &format!("{path:?} ({r},{u})"));
            }
            // A replay returns the job's current status, in any mode.
            let fin = ex(path, &ctx(OPERATOR), &st, "finish", json!({ "id": 4, "completed": true }));
            ok(&fin, "finish");
            st = fin.storage;
            for mode in ["normal", "reject", "unknown", "panic"] {
                let m = ex(path, &ctx(OPERATOR), &st, "set_mode", json!({ "mode": mode }));
                let s = m.storage;
                let out = ex(path, &pool, &s, "execute", exec_args(4, 1, 3));
                assert_eq!(ok(&out, mode), json!("completed"), "{path:?} {mode}");
                assert_eq!(decode(&out.storage).jobs, vec![job(4, 1, 3, "completed")]);
            }
            // Modes for a new id.
            let with_mode = |st: &Storage, mode: &str| {
                let mut m = decode(st);
                m.mode = mode.into();
                encode(&m)
            };
            let s = with_mode(&st, "reject");
            let out = ex(path, &pool, &s, "execute", exec_args(5, 0, 1));
            assert_eq!(ok(&out, "reject"), json!("cancelled"));
            assert_eq!(decode(&out.storage).jobs[1], job(5, 0, 1, "cancelled"));
            let s = with_mode(&st, "unknown");
            let out = ex(path, &pool, &s, "execute", exec_args(5, 0, 1));
            assert_eq!(ok(&out, "unknown"), json!("unknown"));
            assert_eq!(decode(&out.storage).jobs[1], job(5, 0, 1, "active"));
            let s = with_mode(&st, "panic");
            let out = ex(path, &pool, &s, "execute", exec_args(5, 0, 1));
            fails(path, &out, &s, "injected failure", "panic mode");
            // At 256 jobs a new id is refused; known ids still answer.
            let mut full = fresh();
            full.jobs = (0..256).map(|i| job(i * 2, 0, 1, "active")).collect();
            let s = encode(&full);
            let out = ex(path, &pool, &s, "execute", exec_args(1, 0, 1));
            fails(path, &out, &s, "full", "full");
            let out = ex(path, &pool, &s, "execute", exec_args(510, 0, 1));
            assert_eq!(ok(&out, "known at full"), json!("active"));
            let out = ex(path, &ctx(OPERATOR), &s, "confirm_not_executed", exec_args(1, 0, 1));
            fails(path, &out, &s, "full", "confirm at full");
        }
    });
}

// ---------------------------------------------------------------------------
// EX-3: only the operator finishes, confirms non-execution, or sets the mode
// ---------------------------------------------------------------------------

// PROP: EX-3
#[test]
fn ex3_only_the_operator_attests() {
    big_stack(|| {
        for path in paths() {
            let mut m = fresh();
            m.jobs.push(job(0, 0, 1, "active"));
            let st = encode(&m);
            for (pred, signer) in [(POOL, POOL), (Z, Z), (EX, EX), (A1, OPERATOR), (OWNER, OWNER)] {
                let c = Ctx::new(pred, signer, 100_000_000_000).on(EX);
                for (method, args) in [
                    ("finish", json!({ "id": 0, "completed": true })),
                    ("finish", json!({ "id": 0, "completed": false })),
                    ("confirm_not_executed", exec_args(1, 0, 1)),
                    ("set_mode", json!({ "mode": "reject" })),
                ] {
                    let out = ex(path, &c, &st, method, args);
                    fails(path, &out, &st, "only independent operator", &format!("{path:?} {method} by {pred}"));
                }
            }
            for mode in ["normal", "reject", "unknown", "panic"] {
                let out = ex(path, &Ctx::new(OPERATOR, Z, 100_000_000_000).on(EX), &st, "set_mode", json!({ "mode": mode }));
                ok(&out, mode);
                assert_eq!(decode(&out.storage).mode, mode);
                assert_eq!(decode(&out.storage).jobs, m.jobs);
            }
            for bad in ["", "Normal", "normal ", "cancelled"] {
                let out = ex(path, &ctx(OPERATOR), &st, "set_mode", json!({ "mode": bad }));
                fails(path, &out, &st, "invalid mode", bad);
            }
        }
    });
}

// ---------------------------------------------------------------------------
// EX-4: a terminal outcome is never replaced by the other one
// ---------------------------------------------------------------------------

// PROP: EX-4
#[test]
fn ex4_terminal_conflict_rejected() {
    big_stack(|| {
        for path in paths() {
            let mut m = fresh();
            m.jobs = vec![job(0, 0, 1, "active"), job(1, 0, 2, "active"), job(2, 1, 1, "cancelled")];
            let st = encode(&m);
            let op = ctx(OPERATOR);
            let done = ex(path, &op, &st, "finish", json!({ "id": 0, "completed": true }));
            ok(&done, "complete 0");
            assert_eq!(decode(&done.storage).jobs[0].status, "completed");
            let gone = ex(path, &op, &st, "finish", json!({ "id": 1, "completed": false }));
            ok(&gone, "cancel 1");
            assert_eq!(decode(&gone.storage).jobs[1].status, "cancelled");
            // The same outcome again is accepted (and notifies again).
            let again = ex(path, &op, &done.storage, "finish", json!({ "id": 0, "completed": true }));
            ok(&again, "complete 0 again");
            assert_eq!(again.storage, done.storage);
            assert_eq!(again.calls.len(), 1);
            // The other outcome is refused.
            let out = ex(path, &op, &done.storage, "finish", json!({ "id": 0, "completed": false }));
            fails(path, &out, &done.storage, "terminal outcome conflict", "completed -> cancelled");
            let out = ex(path, &op, &gone.storage, "finish", json!({ "id": 1, "completed": true }));
            fails(path, &out, &gone.storage, "terminal outcome conflict", "cancelled -> completed");
            let out = ex(path, &op, &st, "finish", json!({ "id": 2, "completed": true }));
            fails(path, &out, &st, "terminal outcome conflict", "confirmed-not-executed -> completed");
            // Unknown jobs, and confirming non-execution of a job that exists.
            let out = ex(path, &op, &st, "finish", json!({ "id": 9, "completed": true }));
            fails(path, &out, &st, "unknown job", "finish unknown");
            for id in [0, 1, 2] {
                let out = ex(path, &op, &st, "confirm_not_executed", exec_args(id, 0, 1));
                fails(path, &out, &st, "job exists", "confirm existing");
            }
            let out = ex(path, &op, &st, "confirm_not_executed", exec_args(3, 1, 5));
            ok(&out, "confirm new");
            assert_eq!(decode(&out.storage).jobs[3], job(3, 1, 5, "cancelled"));
            // ...after which the lock's late execute replays "cancelled".
            let late = ex(path, &Ctx::by(POOL, 100).on(EX), &out.storage, "execute", exec_args(3, 1, 5));
            assert_eq!(ok(&late, "late execute"), json!("cancelled"));
        }
    });
}

// ---------------------------------------------------------------------------
// EX-5: notify calls lock.settle({id, completed})
// ---------------------------------------------------------------------------

// PROP: EX-5
#[test]
fn ex5_notify_calls_lock_settle() {
    big_stack(|| {
        for path in paths() {
            let mut m = fresh();
            m.jobs = vec![job(0, 0, 1, "active"), job(7, 1, 2, "active")];
            let st = encode(&m);
            let op = ctx(OPERATOR);
            for (id, completed) in [(0u32, true), (7, false)] {
                let out = ex(path, &op, &st, "finish", json!({ "id": id, "completed": completed }));
                ok(&out, "finish");
                assert_eq!(
                    out.calls,
                    vec![fcall(POOL, "settle", json!({ "id": id, "completed": completed }), 40, vec![])],
                    "{path:?}"
                );
                if let Path::Wasm(_) = path {
                    assert_eq!(out.promise_return, Some(0), "finish returns the settle promise");
                }
            }
            let out = ex(path, &op, &st, "confirm_not_executed", exec_args(3, 1, 1));
            ok(&out, "confirm");
            assert_eq!(out.calls, vec![fcall(POOL, "settle", json!({ "id": 3, "completed": false }), 40, vec![])]);
            // The lock is the account given at init, not the caller.
            let mut other = m.clone();
            other.lock = acct(Z);
            let out = ex(path, &op, &encode(&other), "finish", json!({ "id": 0, "completed": true }));
            assert_eq!(out.calls[0].receiver, Z);
        }
    });
}

// ---------------------------------------------------------------------------
// Pool + executor end to end (wasm, receipt router)
// ---------------------------------------------------------------------------

fn trace_methods(net: &Net, from: usize) -> Vec<(String, bool)> {
    net.trace[from..].iter().map(|(_, m, r, _)| (m.clone(), r.is_ok())).collect()
}

fn reconciled(net: &Net, idx: usize) -> Value {
    let (recv, method, r, logs) = &net.trace[idx];
    assert_eq!((recv.as_str(), method.as_str()), (POOL, "on_result"));
    assert!(r.is_ok());
    assert_eq!(logs.len(), 1);
    parse_event(&logs[0])["data"][0].clone()
}

fn submit_args(net: &Net, recipe: u32, units: u32) -> Value {
    json!({ "request": { "recipe": recipe, "units": units, "version": net.pool_state().version, "expires_at": net.now + 50 } })
}

// PROP: EX-5 SH-3 SH-6 SH-7
#[test]
fn ex5_end_to_end_normal_reject_unknown_panic() {
    big_stack(|| {
        for b in Build::all() {
            // normal: execute -> "active" -> Active; finish(true) -> settle -> Completed
            let mut net = Net::new(b, &open_config(), EX, 100);
            let a = submit_args(&net, 0, 2);
            assert!(net.tx(A1, POOL, "submit", a).result.is_ok());
            let n = net.trace.len();
            let d = net.tx(A1, POOL, "dispatch", json!({ "id": 0 }));
            assert!(d.result.is_ok());
            assert_eq!(
                trace_methods(&net, n),
                vec![("dispatch".into(), true), ("execute".into(), true), ("on_result".into(), true)]
            );
            assert_eq!(reconciled(&net, n + 2), json!({ "id": 0, "outcome": "active", "error": null }));
            assert_eq!(net.pool_state().records[0].status, Status::Active);
            assert_eq!(net.jobs(), json!([{ "id": 0, "recipe": 0, "units": 2, "status": "active" }]));
            let n = net.trace.len();
            assert!(net.tx(OPERATOR, EX, "finish", json!({ "id": 0, "completed": true })).result.is_ok());
            assert_eq!(trace_methods(&net, n), vec![("finish".into(), true), ("settle".into(), true)]);
            assert_eq!(net.pool_state().records[0].status, Status::Completed);
            let v = net.pool_state().version;
            // A second finish re-notifies; settle is idempotent.
            assert!(net.tx(OPERATOR, EX, "finish", json!({ "id": 0, "completed": true })).result.is_ok());
            assert!(net.trace.last().unwrap().2.is_ok());
            assert_eq!(net.pool_state().version, v);

            // reject: execute -> "cancelled" -> settle(false) inside on_result
            let mut net = Net::new(b, &open_config(), EX, 100);
            net.tx(OPERATOR, EX, "set_mode", json!({ "mode": "reject" }));
            let a = submit_args(&net, 0, 1);
            net.tx(A1, POOL, "submit", a);
            let n = net.trace.len();
            net.tx(A1, POOL, "dispatch", json!({ "id": 0 }));
            assert_eq!(reconciled(&net, n + 2), json!({ "id": 0, "outcome": "cancelled", "error": null }));
            assert_eq!(net.pool_state().records[0].status, Status::Cancelled);
            assert_eq!(net.jobs()[0]["status"], json!("cancelled"));

            // unknown: execute -> "unknown" (job active) -> Unknown; reconcile
            // by anyone -> status "active" -> Active; later reconciles are
            // no-ops (the version moves at most twice per record).
            let mut net = Net::new(b, &open_config(), EX, 100);
            net.tx(OPERATOR, EX, "set_mode", json!({ "mode": "unknown" }));
            let a = submit_args(&net, 0, 1);
            net.tx(A1, POOL, "submit", a);
            let v0 = net.pool_state().version;
            let n = net.trace.len();
            net.tx(A1, POOL, "dispatch", json!({ "id": 0 }));
            assert_eq!(reconciled(&net, n + 2)["outcome"], json!("unknown"));
            assert_eq!(net.pool_state().records[0].status, Status::Unknown);
            for i in 0..5 {
                let n = net.trace.len();
                assert!(net.tx(Z, POOL, "reconcile", json!({ "id": 0 })).result.is_ok());
                assert_eq!(
                    trace_methods(&net, n),
                    vec![("reconcile".into(), true), ("status".into(), true), ("on_result".into(), true)]
                );
                assert_eq!(reconciled(&net, n + 2)["outcome"], json!("active"));
                assert_eq!(net.pool_state().records[0].status, Status::Active, "reconcile {i}");
            }
            assert_eq!(net.pool_state().version, v0 + 3, "dispatch + Unknown + Active");
            net.tx(OPERATOR, EX, "finish", json!({ "id": 0, "completed": false }));
            assert_eq!(net.pool_state().records[0].status, Status::Cancelled);

            // panic: execute fails -> on_result(PromiseError) -> Unknown;
            // status says "unknown" (no job) -> stays Unknown;
            // confirm_not_executed -> settle(false) -> Cancelled.
            let mut net = Net::new(b, &open_config(), EX, 100);
            net.tx(OPERATOR, EX, "set_mode", json!({ "mode": "panic" }));
            let a = submit_args(&net, 0, 3);
            net.tx(A1, POOL, "submit", a);
            let n = net.trace.len();
            net.tx(A1, POOL, "dispatch", json!({ "id": 0 }));
            assert_eq!(
                trace_methods(&net, n),
                vec![("dispatch".into(), true), ("execute".into(), false), ("on_result".into(), true)]
            );
            assert_eq!(reconciled(&net, n + 2), json!({ "id": 0, "outcome": "unknown", "error": null }));
            let v = net.pool_state().version;
            net.tx(Z, POOL, "reconcile", json!({ "id": 0 }));
            assert_eq!(net.pool_state().records[0].status, Status::Unknown);
            assert_eq!(net.pool_state().version, v);
            assert_eq!(net.jobs(), json!([]));
            let n = net.trace.len();
            assert!(net.tx(OPERATOR, EX, "confirm_not_executed", exec_args(0, 0, 3)).result.is_ok());
            assert_eq!(trace_methods(&net, n), vec![("confirm_not_executed".into(), true), ("settle".into(), true)]);
            assert_eq!(net.pool_state().records[0].status, Status::Cancelled);
            assert_eq!(net.jobs(), json!([{ "id": 0, "recipe": 0, "units": 3, "status": "cancelled" }]));
        }
    });
}

/// The operator's settle may reach the pool before the dispatch callback
/// (different receipts): the late callback is then absorbed.
// PROP: SH-3 RT-RACE
#[test]
fn ex5_settle_before_callback_is_absorbed() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, open_config(), 100);
            s.ok(&Ctx::by(A2, 100), submit(1, 2, 0, 150));
            s.ok(&Ctx::by(A2, 101), Op::Dispatch { id: 0 });
            s.ok(&Ctx::by(X2, 101), Op::Settle { id: 0, completed: true });
            let v = s.pool.version;
            for late in [Some("active"), Some("unknown"), None, Some("completed")] {
                let r = s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: late.map(String::from) });
                assert_eq!(r.event()["error"], Value::Null);
            }
            let r = s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: Some("cancelled".into()) });
            assert_eq!(r.event()["error"], json!("InvalidState"));
            assert_eq!((s.status(0), s.pool.version), (Status::Completed, v));
        }
    });
}
