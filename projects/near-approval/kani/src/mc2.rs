//! MC-2 (strategy §5.11, P4 of §17.5): shared traces between the real core
//! and the Prolog requirements model. Plain mode only.
//!
//! One text format, the one `prolog/verification/graph_export.pl` and
//! `tools/scripts/mc3.py` use for stores: each line is
//! `<call>\t<result>\t<post-store>`, a line `#` ends a trace, and every
//! trace starts from `Init` with owner `o`. Accounts are `o, a1, a2, a3`,
//! keys `k0..k3`, actions `t1..t3` (the three `ACTIONS`), `empty` and
//! `too_long`.
//!
//! - `mc2_core_traces` writes REF-5's core traces (already checked against
//!   `tla.rs`) to `target/mc2/core.txt`; `prolog/verification/mc2.pl`
//!   replays them on `step/4`.
//! - `mc2_prolog_traces` replays `target/mc2/prolog.txt`, written by
//!   `mc2.pl` from `step/4`, on the real core, when that file exists.

use crate::ids::{Acct, Key, ACTIONS, OWNER};
use crate::spec::{Op, C};
use crate::tla::{self, TOO_LONG};
use crate::trace::{alpha_mem, trace, Abs};
use approval_core::{
    add_principal, approve, reject, request_action, revoke_key, ApprovalError as E, BlockTime,
    Caller, MemStore, Role,
};

type M = MemStore<Acct, Key>;

fn acct(v: u8) -> String {
    if v == 0 {
        "o".into()
    } else {
        format!("a{v}")
    }
}

fn role(r: Role) -> &'static str {
    match r {
        Role::Agent => "agent",
        Role::Approver => "approver",
    }
}

fn act(code: u8) -> String {
    match code {
        0 => "empty".into(),
        TOO_LONG => "too_long".into(),
        c => format!("t{c}"),
    }
}

fn act_of(a: &str) -> String {
    act(tla::class(a))
}

/// The store text of graph_export.pl.
pub fn text(t: &Abs) -> String {
    let mut ps: Vec<String> = t
        .principals
        .iter()
        .enumerate()
        .filter(|(_, p)| p.reg)
        .map(|(k, p)| {
            format!(
                "k{k},{},{},{},{},{}",
                acct(p.acct),
                role(p.role),
                p.rid,
                p.from,
                p.pending
            )
        })
        .collect();
    ps.sort();
    let rs: Vec<String> = t.requests[..t.nr]
        .iter()
        .map(|r| {
            let ap = if r.appr {
                format!("{}/{}/k{}/{}", r.aidx, acct(r.aacct), r.akey, r.arid)
            } else {
                "-".into()
            };
            let rj = if r.rj {
                format!("{}/k{}/{}", acct(r.racct), r.rkey, r.rrid)
            } else {
                "-".into()
            };
            format!(
                "{},k{},{},{},{ap},{rj}",
                acct(r.acct),
                r.key,
                r.rid,
                act(r.act)
            )
        })
        .collect();
    let mut v: Vec<u64> = t.revoked[..t.nv].to_vec();
    v.sort();
    let join = |xs: &[u64]| {
        xs.iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",")
    };
    format!(
        "{}|{}|{}|{}|{}",
        ps.join(";"),
        rs.join(";"),
        join(&t.log[..t.nl]),
        t.regs,
        join(&v)
    )
}

fn call_text(op: &Op) -> String {
    let c3 = |c: &C| {
        format!(
            "{},{},k{}",
            acct(c.predecessor.0),
            acct(c.signer.0),
            c.signer_key.0
        )
    };
    match op {
        Op::Add {
            caller,
            key,
            acct: a,
            role: r,
        } => {
            format!(
                "add,{},k{},{},{}",
                acct(caller.0),
                key.0,
                acct(a.0),
                role(*r)
            )
        }
        Op::Revoke { caller, key, .. } => format!("revoke,{},k{}", acct(caller.0), key.0),
        Op::Req { c, action, .. } => format!("request,{},{}", c3(c), act_of(action)),
        Op::Appr { c, id, action, .. } => format!("approve,{},{id},{}", c3(c), act_of(action)),
        Op::Rej { c, id, .. } => format!("reject,{},{id}", c3(c)),
    }
}

fn result_text(e: Option<E>) -> String {
    e.map_or("Ok".into(), |e| format!("{e:?}"))
}

fn dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/mc2")
}

#[test]
fn mc2_core_traces() {
    let n: u64 = std::env::var("MC2_TRACES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(60);
    let len: usize = std::env::var("MC2_LEN")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(80);
    let mut out = String::new();
    for i in 0..n {
        for st in trace(0x3C2_0000 + i, len) {
            out += &format!(
                "{}\t{}\t{}\n",
                call_text(&st.op),
                result_text(st.err),
                text(&st.post)
            );
        }
        out += "#\n";
    }
    std::fs::create_dir_all(dir()).unwrap();
    std::fs::write(dir().join("core.txt"), out).unwrap();
}

// ---------------------------------------------------------------------------
// Replaying the Prolog model's traces on the core
// ---------------------------------------------------------------------------

fn p_acct(s: &str) -> Acct {
    if s == "o" {
        OWNER
    } else {
        Acct(s.trim_start_matches('a').parse().expect("account"))
    }
}

fn p_key(s: &str) -> Key {
    Key(s.trim_start_matches('k').parse().expect("key"))
}

fn p_action(s: &str) -> String {
    match s {
        "empty" => String::new(),
        "too_long" => crate::checks::LONG.to_string(),
        t => ACTIONS[t.trim_start_matches('t').parse::<usize>().expect("action") - 1].to_string(),
    }
}

fn p_caller(f: &[&str]) -> C {
    Caller {
        predecessor: p_acct(f[0]),
        signer: p_acct(f[1]),
        signer_key: p_key(f[2]),
    }
}

fn p_call(s: &str, step: u64) -> Op {
    let f: Vec<&str> = s.split(',').collect();
    let t = BlockTime {
        height: step,
        timestamp_ns: step,
    };
    match f[0] {
        "add" => Op::Add {
            caller: p_acct(f[1]),
            key: p_key(f[2]),
            acct: p_acct(f[3]),
            role: if f[4] == "agent" {
                Role::Agent
            } else {
                Role::Approver
            },
        },
        "revoke" => Op::Revoke {
            caller: p_acct(f[1]),
            key: p_key(f[2]),
            t,
        },
        "request" => Op::Req {
            c: p_caller(&f[1..4]),
            action: p_action(f[4]),
            t,
        },
        "approve" => Op::Appr {
            c: p_caller(&f[1..4]),
            id: f[4].parse().expect("id"),
            action: p_action(f[5]),
            t,
        },
        "reject" => Op::Rej {
            c: p_caller(&f[1..4]),
            id: f[4].parse().expect("id"),
            t,
        },
        other => panic!("unknown call {other}"),
    }
}

fn run(s: &mut M, op: &Op) -> Option<E> {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => add_principal(s, caller, key.clone(), acct.clone(), *role).err(),
        Op::Revoke { caller, key, t } => revoke_key(s, caller, key, *t).err(),
        Op::Req { c, action, t } => request_action(s, c, action.clone(), *t).err(),
        Op::Appr { c, id, action, t } => approve(s, c, *id, action, *t).err(),
        Op::Rej { c, id, t } => reject(s, c, *id, *t).err(),
    }
}

#[test]
fn mc2_prolog_traces() {
    let path = dir().join("prolog.txt");
    let Ok(text_in) = std::fs::read_to_string(&path) else {
        eprintln!(
            "mc2: {} not found; run prolog/verification/mc2.pl first",
            path.display()
        );
        return;
    };
    let (mut traces, mut steps) = (0, 0);
    let mut s: M = MemStore::new(OWNER);
    let mut n = 0u64;
    for (lineno, line) in text_in.lines().enumerate() {
        if line == "#" {
            s = MemStore::new(OWNER);
            n = 0;
            traces += 1;
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        let op = p_call(f[0], n);
        let got = result_text(run(&mut s, &op));
        let post = text(&alpha_mem(&s));
        assert!(
            got == f[1] && post == f[2],
            "MC-2 line {}: {}\n  Prolog: {} -> {}\n  core:   {} -> {}",
            lineno + 1,
            f[0],
            f[1],
            f[2],
            got,
            post
        );
        n += 1;
        steps += 1;
    }
    eprintln!("mc2: {traces} Prolog traces, {steps} steps replayed on the core");
}
