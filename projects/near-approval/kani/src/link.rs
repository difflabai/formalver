//! LINK (strategy.md section 18.6, l2-oracle-proposal.md): `ghost::expect`
//! and `ghost::protocol` against the Lean transcription `cstep`
//! (lean/ApprovalLean/Delta.lean), on every footprint view of a bounded,
//! exhaustive domain. Plain mode only.
//!
//! `link_cases` writes one line per (view, call) to `target/link/cases.txt`
//! in `lean/ApprovalLean/DeltaText.lean`'s format, with `expect`'s error and
//! `protocol`'s calls; `approval-lean link` recomputes both with `cstep` and
//! must agree on every line. Each view is also run through the real core on
//! a `Sparse` holding exactly that view, which must make `protocol`'s calls
//! and return `expect`'s result (ST-8's plain twin on these views).
//!
//! The domain. A call reads at most: the owner, the signer key's principal,
//! the request at `id`, its agent key's principal and the three counters
//! (the footprint `K-ORACLE` frees). Up to renaming of identities, what the
//! code can observe of them is which are equal (ASM-IDENT), and of the
//! counters, how they compare with `u64::MAX`, `MAX_PENDING_PER_KEY` and
//! the request id. So, with owner `o`, signer `a1` and signer key `k0`:
//! - accounts take `o`, `a1`, `a2`: every equality pattern among the pairs
//!   the code compares (predecessor/signer, principal/signer,
//!   request/signer, agent principal/request);
//! - the request's key is `k0` (the signer's own) or `k1`, and the call's
//!   key `k0` or the unregistered `k2`;
//! - each principal is absent or any role and account, with `active_from`
//!   at or just above the id, and `pending` at 0 or 1 for decisions (the
//!   saturating decrement) and at 0, the cap - 1 or the cap for requests;
//! - the request is absent or any account, key, payload and decision state;
//! - ids are small or `u64::MAX - 1`; counters are small, `u64::MAX - 1` or
//!   `u64::MAX`.
//! Registration ids are fixed per key: they are only copied, never compared.

use crate::ghost::{expect, protocol, run, Call, Sparse};
use crate::ids::{Acct, Key, ACTIONS, OWNER};
use crate::spec::{Op, Req, C};
use crate::tla::{class, TOO_LONG};
use approval_core::{Approval, BlockTime, Caller, Principal, Rejection, Role, MAX_PENDING_PER_KEY};
use std::fmt::Write as _;

const MAXU: u64 = u64::MAX;
const T: BlockTime = BlockTime {
    height: 9,
    timestamp_ns: 9,
};

fn acct(a: &Acct) -> String {
    if a.0 == 0 {
        "o".into()
    } else {
        format!("a{}", a.0)
    }
}

fn key(k: &Key) -> String {
    format!("k{}", k.0)
}

fn role(r: Role) -> &'static str {
    match r {
        Role::Agent => "agent",
        Role::Approver => "approver",
    }
}

fn act(a: &str) -> String {
    match class(a) {
        0 => "empty".into(),
        TOO_LONG => "too_long".into(),
        c => format!("t{c}"),
    }
}

fn prin_text(k: &Key, p: &Principal<Acct>) -> String {
    format!(
        "{},{},{},{},{},{}",
        key(k),
        acct(&p.account_id),
        role(p.role),
        p.registration_id,
        p.active_from,
        p.pending
    )
}

fn req_text(r: &Req) -> String {
    let ap = r.approval.as_ref().map_or("-".into(), |d| {
        format!(
            "{}/{}/{}/{}",
            d.approval_index,
            acct(&d.approver_account_id),
            key(&d.approver_key),
            d.approver_registration_id
        )
    });
    let rj = r.rejection.as_ref().map_or("-".into(), |d| {
        format!(
            "{}/{}/{}",
            acct(&d.approver_account_id),
            key(&d.approver_key),
            d.approver_registration_id
        )
    });
    format!(
        "{},{},{},{},{},{ap},{rj}",
        r.id,
        acct(&r.agent_account_id),
        key(&r.agent_key),
        r.agent_registration_id,
        act(&r.action)
    )
}

fn call_text(c: &Call) -> String {
    match c {
        Call::IncrementRegistrationCount => "incG".into(),
        Call::InsertPrincipal(k, p) => format!("insP={}", prin_text(k, p)),
        Call::RemovePrincipal(k) => format!("rmP={}", key(k)),
        Call::PushRequest(r) => format!("pushR={}", req_text(r)),
        Call::ReplaceRequest(r) => format!("replR={}", req_text(r)),
        Call::PushApproval(i) => format!("pushA={i}"),
        Call::InsertRevocation(g, _) => format!("insRev={g}"),
    }
}

fn op_text(op: &Op) -> String {
    let c3 = |c: &C| {
        format!(
            "{},{},{}",
            acct(&c.predecessor),
            acct(&c.signer),
            key(&c.signer_key)
        )
    };
    match op {
        Op::Add {
            caller,
            key: k,
            acct: a,
            role: r,
        } => format!("add,{},{},{},{}", acct(caller), key(k), acct(a), role(*r)),
        Op::Revoke { caller, key: k, .. } => format!("revoke,{},{}", acct(caller), key(k)),
        Op::Req { c, action, .. } => format!("request,{},{}", c3(c), act(action)),
        Op::Appr { c, id, action, .. } => format!("approve,{},{id},{}", c3(c), act(action)),
        Op::Rej { c, id, .. } => format!("reject,{},{id}", c3(c)),
    }
}

/// One footprint view.
#[derive(Clone)]
struct View {
    prins: Vec<(Key, Principal<Acct>)>,
    req: Option<Req>,
    nr: u64,
    nl: u64,
    regs: u64,
}

impl View {
    fn text(&self) -> String {
        let ps: Vec<String> = self.prins.iter().map(|(k, p)| prin_text(k, p)).collect();
        let r = self.req.as_ref().map_or("-".into(), req_text);
        format!("{}|{r}|{}|{}|{}", ps.join(";"), self.nr, self.nl, self.regs)
    }

    fn store(&self) -> Sparse {
        let mut s = Sparse::new(OWNER);
        for (k, p) in &self.prins {
            s.principals.insert(k.clone(), p.clone());
        }
        if let Some(r) = &self.req {
            s.requests.insert(r.id, r.clone());
        }
        s.request_count = self.nr;
        s.approval_count = self.nl;
        s.registration_count = self.regs;
        s
    }
}

const ACCTS: [Acct; 3] = [OWNER, Acct(1), Acct(2)];
const ROLES: [Role; 2] = [Role::Agent, Role::Approver];

fn rid(k: &Key) -> u64 {
    7 + 2 * k.0 as u64
}

/// The principal options for key `k`: absent, or any account and role with
/// each `active_from` and `pending` given.
fn prins(k: Key, froms: &[u64], pendings: &[u32]) -> Vec<Option<(Key, Principal<Acct>)>> {
    let mut v = vec![None];
    for a in &ACCTS {
        for &r in &ROLES {
            for &f in froms {
                for &p in pendings {
                    v.push(Some((
                        k.clone(),
                        Principal {
                            account_id: a.clone(),
                            role: r,
                            registration_id: rid(&k),
                            active_from: f,
                            pending: p,
                        },
                    )));
                }
            }
        }
    }
    v
}

/// The request options at `id`: absent, or any account, key, payload and
/// decision state.
fn reqs(id: u64) -> Vec<Option<Req>> {
    let mut v = vec![None];
    for a in &ACCTS {
        for k in [Key(0), Key(1)] {
            for x in [ACTIONS[0], ACTIONS[1]] {
                for appr in [false, true] {
                    for rej in [false, true] {
                        v.push(Some(Req {
                            id,
                            agent_account_id: a.clone(),
                            agent_key: k.clone(),
                            agent_registration_id: rid(&k),
                            action: x.to_string(),
                            requested_at: T,
                            approval: appr.then(|| Approval {
                                approval_index: 4,
                                approver_account_id: Acct(2),
                                approver_key: Key(3),
                                approver_registration_id: 13,
                                approved_at: T,
                            }),
                            rejection: rej.then(|| Rejection {
                                approver_account_id: Acct(2),
                                approver_key: Key(3),
                                approver_registration_id: 13,
                                rejected_at: T,
                            }),
                        }));
                    }
                }
            }
        }
    }
    v
}

fn caller(pred: &Acct, k: &Key) -> C {
    Caller {
        predecessor: pred.clone(),
        signer: Acct(1),
        signer_key: k.clone(),
    }
}

fn with(v: &[&Option<(Key, Principal<Acct>)>]) -> Vec<(Key, Principal<Acct>)> {
    v.iter().filter_map(|p| (*p).clone()).collect()
}

/// Every (view, call) of the domain.
fn cases(mut f: impl FnMut(&View, &Op)) {
    let base = View {
        prins: vec![],
        req: None,
        nr: 3,
        nl: 2,
        regs: 4,
    };
    // add, revoke: the owner check, the key's presence, the registration
    // counter's limit.
    for p0 in &prins(Key(0), &[1], &[0]) {
        for regs in [4, MAXU - 1, MAXU] {
            for nr in [3, MAXU] {
                let v = View {
                    prins: with(&[p0]),
                    regs,
                    nr,
                    ..base.clone()
                };
                for c in &ACCTS[..2] {
                    for a in &ACCTS {
                        for &r in &ROLES {
                            f(
                                &v,
                                &Op::Add {
                                    caller: c.clone(),
                                    key: Key(0),
                                    acct: a.clone(),
                                    role: r,
                                },
                            );
                        }
                    }
                    f(
                        &v,
                        &Op::Revoke {
                            caller: c.clone(),
                            key: Key(0),
                            t: T,
                        },
                    );
                }
            }
        }
    }
    // request: authentication, the action's class, the pending cap, the
    // request counter's limit.
    let cap = MAX_PENDING_PER_KEY;
    for p0 in &prins(Key(0), &[1], &[0, cap - 1, cap]) {
        for nr in [3, MAXU - 1, MAXU] {
            let v = View {
                prins: with(&[p0]),
                nr,
                ..base.clone()
            };
            for pred in &ACCTS[1..] {
                for k in [Key(0), Key(2)] {
                    for x in ["", crate::checks::LONG, ACTIONS[0], ACTIONS[2]] {
                        f(
                            &v,
                            &Op::Req {
                                c: caller(pred, &k),
                                action: x.to_string(),
                                t: T,
                            },
                        );
                    }
                }
            }
        }
    }
    // approve, reject: authentication, the request's state, its agent's
    // registration, self-approval, the payload, the approval counter.
    for id in [2, MAXU - 1] {
        let ps0 = prins(Key(0), &[id, id + 1], &[0, 1]);
        let ps1 = prins(Key(1), &[id, id + 1], &[0, 1]);
        let rs = reqs(id);
        for p0 in &ps0 {
            for p1 in &ps1 {
                for r in &rs {
                    for nl in [2, MAXU] {
                        let v = View {
                            prins: with(&[p0, p1]),
                            req: r.clone(),
                            nr: id + 1,
                            nl,
                            ..base.clone()
                        };
                        for pred in &ACCTS[1..] {
                            for k in [Key(0), Key(2)] {
                                f(
                                    &v,
                                    &Op::Appr {
                                        c: caller(pred, &k),
                                        id,
                                        action: ACTIONS[0].to_string(),
                                        t: T,
                                    },
                                );
                                if nl == 2 {
                                    f(
                                        &v,
                                        &Op::Rej {
                                            c: caller(pred, &k),
                                            id,
                                            t: T,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

// PROP: LINK
#[test]
fn link_cases() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/link");
    std::fs::create_dir_all(&dir).unwrap();
    let mut out = std::io::BufWriter::new(std::fs::File::create(dir.join("cases.txt")).unwrap());
    let (mut n, mut oks) = (0u64, 0u64);
    cases(|v, op| {
        let s = v.store();
        let exp = expect(&s, op);
        let rec = protocol(&s, op, &exp);
        assert!(rec.n <= rec.c.len(), "protocol overflow on {}", op_text(op));
        // The real core on this exact view: ST-8's plain twin.
        let mut t = v.store();
        let got = run(&mut t, op);
        assert!(
            got == exp && t.calls == rec,
            "core differs from expect/protocol on {} {}",
            v.text(),
            op_text(op)
        );
        let calls: Vec<String> = rec.c[..rec.n]
            .iter()
            .map(|c| call_text(c.as_ref().unwrap()))
            .collect();
        let err = match exp.err() {
            None => "Ok".to_string(),
            Some(e) => format!("{e:?}"),
        };
        let mut line = String::new();
        writeln!(
            line,
            "{}\t{}\t{err}\t{}",
            v.text(),
            op_text(op),
            calls.join(";")
        )
        .unwrap();
        std::io::Write::write_all(&mut out, line.as_bytes()).unwrap();
        n += 1;
        oks += exp.is_ok() as u64;
    });
    std::io::Write::flush(&mut out).unwrap();
    // Every operation reaches Ok somewhere in the domain.
    assert!(oks > 0 && oks < n);
    eprintln!("LINK: {n} views written, {oks} Ok");
}
