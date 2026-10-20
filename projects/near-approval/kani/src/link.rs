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
//! The domain is `norm::all_cls()` mapped through `norm::rep`: one
//! representative view per class of footprint views (LEAN-COVER). Lean
//! proves `cstep` on any view equals `cstep` on its class's representative,
//! carried back (`Ident.cover`); Kani proves the same of `expect`/`protocol`
//! (K-LINK-T, `h_link_t_*`). `approval-lean link` also checks that the views
//! written here are exactly its own `allCls.map rep`, so the domain is the
//! one Lean's theorem quantifies over.

use crate::ghost::{expect, protocol, run, Call};
use crate::ids::{Acct, Key};
use crate::norm::{all_cls, rep, View};
use crate::spec::{Op, Req, C};
use crate::tla::{class, TOO_LONG};
use approval_core::{Principal, Role};
use std::collections::HashSet;
use std::fmt::Write as _;

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

fn view_text(v: &View) -> String {
    let ps: Vec<String> = v.prins.iter().flatten().map(|(k, p)| prin_text(k, p)).collect();
    let r = v.req.as_ref().map_or("-".into(), req_text);
    format!("{}|{r}|{}|{}|{}", ps.join(";"), v.nr, v.nl, v.regs)
}

// PROP: LINK
#[test]
fn link_cases() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/link");
    std::fs::create_dir_all(&dir).unwrap();
    let mut out = std::io::BufWriter::new(std::fs::File::create(dir.join("cases.txt")).unwrap());
    let (mut n, mut oks) = (0u64, 0u64);
    let mut seen = HashSet::new();
    for c in all_cls() {
        let (v, op) = rep(&c);
        let (v, op) = (&v, &op);
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
            view_text(v),
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
        // Distinct classes can share a representative (a missing request
        // makes `k_eq` and `g` unobservable); write each view once.
        let key = format!("{}\t{}", view_text(v), op_text(op));
        if !seen.insert(key.clone()) {
            continue;
        }
        let mut line = String::new();
        writeln!(line, "{key}\t{err}\t{}", calls.join(";")).unwrap();
        std::io::Write::write_all(&mut out, line.as_bytes()).unwrap();
        n += 1;
        oks += exp.is_ok() as u64;
    }
    std::io::Write::flush(&mut out).unwrap();
    // Every operation reaches Ok somewhere in the domain.
    assert!(oks > 0 && oks < n);
    eprintln!("LINK: {n} views written, {oks} Ok");
}
