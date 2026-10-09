//! REF-5: trace validation of `tla/ApprovalCore.tla` against the real core
//! (strategy.md section 17.2). Plain mode only.
//!
//! Random call sequences run on the real core over `MemStore` (unbounded,
//! unlike the harness store). Each step records the call, the core's error
//! and `alpha` of the post-state. The test checks every step against the
//! Rust transcription in `tla.rs`, then writes the traces as a TLA+ module
//! (`TraceData.tla`); `tla/TraceCheck.tla` makes TLC accept each one as a
//! behaviour of `Spec` or report a deadlock at the first step it rejects.
//! Together these tie the `.tla` text, `tla.rs` and the core to each other.

use crate::ids::{Acct, Key, ACTIONS, NA, NK, OWNER};
use crate::spec::{Op, C};
use crate::src::{Rng, Src};
use crate::tla::{self, TOO_LONG};
use approval_core::{
    add_principal, approve, request_action, revoke_key, ApprovalError as E, BlockTime, Caller,
    MemStore, Role, Store,
};
use std::fmt::Write as _;

type M = MemStore<Acct, Key>;

/// Capacity of the abstract state: more than any trace's request count.
pub const CT: usize = 128;
pub type Abs = tla::T<CT>;

/// `alpha` over `MemStore` (unbounded, unlike the harness store).
pub fn alpha_mem(s: &M) -> Abs {
    let mut t = Abs::init();
    for k in 0..NK {
        if let Some(p) = s.principal(&Key(k)) {
            t.principals[k as usize] = tla::TP {
                reg: true,
                acct: p.account_id.0,
                role: p.role,
                from: p.active_from,
                pending: p.pending,
            };
        }
    }
    for (i, r) in s.requests.iter().enumerate() {
        let ap = r
            .approval
            .as_ref()
            .map(|x| (x.approval_index, x.approver_account_id.0, x.approver_key.0));
        t.requests[i] = tla::tr(
            r.agent_account_id.0,
            r.agent_key.0,
            tla::class(&r.action),
            ap,
        );
    }
    t.nr = s.requests.len();
    for (j, id) in s.approval_log.iter().enumerate() {
        t.log[j] = *id;
    }
    t.nl = s.approval_log.len();
    t
}

fn run_core(s: &mut M, op: &Op) -> Option<E> {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => add_principal(s, caller, key.clone(), acct.clone(), *role).err(),
        Op::Revoke { caller, key } => revoke_key(s, caller, key).err(),
        Op::Req { c, action, t } => request_action(s, c, action.clone(), *t).err(),
        Op::Appr { c, id, action, t } => approve(s, c, *id, action, *t).err(),
    }
}

fn action(rng: &mut Rng) -> String {
    match rng.below(10) {
        0 => String::new(),
        1 => crate::checks::LONG.to_string(),
        n => ACTIONS[(n % 3) as usize].to_string(),
    }
}

/// A random call, biased toward ones that pass their guards.
fn call(rng: &mut Rng, s: &M, step: u64) -> Op {
    let t = BlockTime {
        height: step,
        timestamp_ns: step,
    };
    let caller = |rng: &mut Rng| -> C {
        let k = rng.below(NK);
        let signer = match s.principal(&Key(k)) {
            Some(p) if rng.hint(85) => p.account_id.0,
            _ => rng.below(NA),
        };
        let predecessor = if rng.hint(92) { signer } else { rng.below(NA) };
        Caller {
            predecessor: Acct(predecessor),
            signer: Acct(signer),
            signer_key: Key(k),
        }
    };
    let admin = |rng: &mut Rng| {
        if rng.hint(90) {
            OWNER
        } else {
            Acct(rng.below(NA))
        }
    };
    match rng.below(10) {
        // Re-register a key to the account and role of one of its earlier
        // requests: the revival attempt TR-3 is about.
        0 if !s.requests.is_empty() => {
            let r = &s.requests[rng.below(s.requests.len().min(200) as u8) as usize];
            Op::Add {
                caller: admin(rng),
                key: r.agent_key.clone(),
                acct: r.agent_account_id.clone(),
                role: Role::Agent,
            }
        }
        0..=2 => Op::Add {
            caller: admin(rng),
            key: Key(rng.below(NK)),
            acct: Acct(rng.below(NA)),
            role: if rng.bool() {
                Role::Agent
            } else {
                Role::Approver
            },
        },
        3 => Op::Revoke {
            caller: admin(rng),
            key: Key(rng.below(NK)),
        },
        4..=6 => Op::Req {
            c: caller(rng),
            action: action(rng),
            t,
        },
        _ => {
            let c = caller(rng);
            let n = s.requests.len() as u64;
            // Mostly unapproved requests, where the guards are interesting.
            let open: Vec<u64> = (0..n)
                .filter(|i| s.requests[*i as usize].approval.is_none())
                .collect();
            let id = if !open.is_empty() && rng.hint(70) {
                open[rng.below(open.len().min(200) as u8) as usize]
            } else {
                rng.below((n.min(60) + 1) as u8) as u64
            };
            let action = match s.requests.get(id as usize) {
                Some(r) if rng.hint(85) => r.action.clone(),
                _ => action(rng),
            };
            Op::Appr { c, id, action, t }
        }
    }
}

pub struct Step {
    pub op: Op,
    pub err: Option<E>,
    pub post: Abs,
}

/// One trace of `len` calls from `Init` on the real core, checked step by
/// step against `tla.rs`'s operators.
pub fn trace(seed: u64, len: usize) -> Vec<Step> {
    let mut rng = Rng(seed | 1);
    let mut s: M = MemStore::new(OWNER);
    let mut t = alpha_mem(&s);
    assert!(tla::same(&t, &Abs::init()), "REF-5 Init");
    let mut out = Vec::with_capacity(len);
    for n in 0..len {
        let op = call(&mut rng, &s, n as u64);
        let err = run_core(&mut s, &op);
        let post = alpha_mem(&s);
        let want = tla::err(&t, &op);
        assert_eq!(err, want, "REF-5 error, step {n} of seed {seed}: {op:?}");
        let want_post = if want.is_none() {
            tla::next(&t, &op)
        } else {
            t
        };
        assert!(
            tla::same(&post, &want_post),
            "REF-5 post-state, step {n} of seed {seed}: {op:?}"
        );
        t = post;
        out.push(Step { op, err, post });
    }
    out
}

// ---------------------------------------------------------------------------
// TLA+ output
// ---------------------------------------------------------------------------

fn a(v: u8) -> String {
    if v == OWNER.0 {
        "\"o\"".into()
    } else {
        format!("\"a{v}\"")
    }
}

fn k(v: u8) -> String {
    format!("\"k{v}\"")
}

fn role(r: Role) -> &'static str {
    match r {
        Role::Agent => "\"Agent\"",
        Role::Approver => "\"Approver\"",
    }
}

fn payload(code: u8) -> String {
    match code {
        tla::EMPTY => "\"EMPTY\"".into(),
        TOO_LONG => "\"TOOLONG\"".into(),
        c => format!("\"p{c}\""),
    }
}

fn err_name(e: Option<E>) -> String {
    format!("\"{}\"", e.map_or("Ok".to_string(), |e| format!("{e:?}")))
}

fn abs_tla(t: &Abs) -> String {
    let mut s = String::from("[principals |-> ");
    let ps: Vec<String> = (0..NK)
        .map(|i| {
            let p = t.principals[i as usize];
            format!(
                "{} :> [reg |-> {}, acct |-> {}, role |-> {}, from |-> {}, pending |-> {}]",
                k(i),
                if p.reg { "TRUE" } else { "FALSE" },
                a(p.acct),
                role(p.role),
                p.from,
                p.pending
            )
        })
        .collect();
    write!(s, "({})", ps.join(" @@ ")).unwrap();
    let rs: Vec<String> = t.requests[..t.nr]
        .iter()
        .map(|r| {
            format!(
                "[acct |-> {}, key |-> {}, act |-> {}, appr |-> {}, aidx |-> {}, aacct |-> {}, akey |-> {}]",
                a(r.acct),
                k(r.key),
                payload(r.act),
                if r.appr { "TRUE" } else { "FALSE" },
                r.aidx,
                a(r.aacct),
                k(r.akey)
            )
        })
        .collect();
    write!(s, ", requests |-> <<{}>>", rs.join(", ")).unwrap();
    let ls: Vec<String> = t.log[..t.nl].iter().map(|i| i.to_string()).collect();
    write!(s, ", log |-> <<{}>>]", ls.join(", ")).unwrap();
    s
}

fn call_tla(op: &Op) -> String {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role: r,
        } => format!(
            "[op |-> \"add\", c |-> {}, k |-> {}, a |-> {}, r |-> {}",
            a(caller.0),
            k(key.0),
            a(acct.0),
            role(*r)
        ),
        Op::Revoke { caller, key } => {
            format!(
                "[op |-> \"revoke\", c |-> {}, k |-> {}",
                a(caller.0),
                k(key.0)
            )
        }
        Op::Req { c, action, .. } => format!(
            "[op |-> \"request\", p |-> {}, s |-> {}, k |-> {}, x |-> {}",
            a(c.predecessor.0),
            a(c.signer.0),
            k(c.signer_key.0),
            payload(tla::class(action))
        ),
        Op::Appr { c, id, action, .. } => format!(
            "[op |-> \"approve\", p |-> {}, s |-> {}, k |-> {}, i |-> {}, x |-> {}",
            a(c.predecessor.0),
            a(c.signer.0),
            k(c.signer_key.0),
            id,
            payload(tla::class(action))
        ),
    }
}

/// The `TraceData` module: `Traces`, a tuple of traces, each a tuple of
/// steps `[op, <args>, err, post]`.
pub fn module(traces: &[Vec<Step>]) -> String {
    let mut s = String::new();
    s.push_str("---------------------------- MODULE TraceData ----------------------------\n");
    s.push_str("\\* Generated by kani/src/trace.rs (REF-5). Do not edit.\n");
    s.push_str("EXTENDS TLC, Sequences\n\nTraces == <<\n");
    let ts: Vec<String> = traces
        .iter()
        .map(|t| {
            let steps: Vec<String> = t
                .iter()
                .map(|st| {
                    format!(
                        "    {}, err |-> {}, post |-> {}]",
                        call_tla(&st.op),
                        err_name(st.err),
                        abs_tla(&st.post)
                    )
                })
                .collect();
            format!("  <<\n{}\n  >>", steps.join(",\n"))
        })
        .collect();
    s.push_str(&ts.join(",\n"));
    s.push_str(
        "\n>>\n=============================================================================\n",
    );
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Checks the traces against `tla.rs` and writes `TraceData.tla` to
    /// `$REF5_OUT` (default `target/ref5`) for `run-tla.sh`.
    #[test]
    fn ref5_traces() {
        let n: u64 = std::env::var("REF5_TRACES")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(60);
        let len: usize = std::env::var("REF5_LEN")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(80);
        let traces: Vec<_> = (0..n).map(|i| trace(0xA5A5_0000 + i, len)).collect();
        // Non-vacuity: the traces exercise every error the TLA+ spec can
        // produce, an approval and a void request.
        let mut seen = std::collections::BTreeSet::new();
        let mut revival = 0;
        for t in &traces {
            let mut pre = Abs::init();
            for st in t {
                seen.insert(err_name(st.err));
                // TR-3 witness: approving a request whose key is registered
                // again, to the same account as Agent, under a later
                // registration. Only active_from rejects it.
                if let (Op::Appr { id, .. }, Some(E::AgentRevoked)) = (&st.op, st.err) {
                    let r = pre.requests[*id as usize];
                    let p = pre.principals[r.key as usize];
                    revival += (p.reg && p.role == Role::Agent && p.acct == r.acct) as u32;
                }
                pre = st.post;
            }
        }
        assert!(
            revival >= 5,
            "REF-5 traces attempt a revival only {revival} times"
        );
        for e in [
            "Ok",
            "NotOwner",
            "KeyAlreadyRegistered",
            "KeyNotRegistered",
            "IndirectCall",
            "UnknownKey",
            "WrongRole",
            "KeyAccountMismatch",
            "EmptyAction",
            "ActionTooLong",
            "RequestNotFound",
            "AlreadyApproved",
            "AgentRevoked",
            "ActionMismatch",
            "SelfApproval",
        ] {
            assert!(
                seen.contains(&format!("\"{e}\"")),
                "REF-5 traces never produce {e}"
            );
        }
        let dir = std::env::var("REF5_OUT").unwrap_or_else(|_| "target/ref5".into());
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(format!("{dir}/TraceData.tla"), module(&traces)).unwrap();
    }
}
