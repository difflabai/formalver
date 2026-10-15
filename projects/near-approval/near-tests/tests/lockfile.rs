//! Lockfile rule (strategy.md section 9): every package present both in this
//! crate's `Cargo.lock` and in the mirror's `contracts/approval/Cargo.lock`
//! has the same version and checksum, so the tests run against the TCB the
//! deployed wasm is built from (near-sdk, borsh, serde_json, ...).
//!
//! Run as part of `cargo test --locked`; also usable alone:
//! `cargo test --locked --test lockfile`.

use std::collections::BTreeMap;
use std::path::Path;

/// `name -> [(version, checksum)]` from a Cargo.lock (v3/v4) file.
fn packages(path: &Path) -> BTreeMap<String, Vec<(String, String)>> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut out: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    for block in text.split("[[package]]").skip(1) {
        let field = |k: &str| {
            block
                .lines()
                .find_map(|l| l.strip_prefix(&format!("{k} = \"")))
                .map(|v| v.trim_end_matches('"').to_string())
        };
        let name = field("name").expect("package without a name");
        let version = field("version").expect("package without a version");
        let checksum = field("checksum").unwrap_or_else(|| "<path>".into());
        out.entry(name).or_default().push((version, checksum));
    }
    out
}

#[test]
fn shared_packages_match_the_mirror_lockfile() {
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    let ours = packages(&here.join("Cargo.lock"));
    let mirror = packages(&here.join("../source-mirror/contracts/approval/Cargo.lock"));
    let mut shared = 0;
    let mut bad = Vec::new();
    for (name, ours_v) in &ours {
        let Some(theirs) = mirror.get(name) else { continue };
        shared += 1;
        // A name may appear in several versions; each of ours must be one of
        // the mirror's, with the same checksum.
        for v in ours_v {
            if !theirs.contains(v) {
                bad.push(format!("{name}: ours {v:?}, mirror {theirs:?}"));
            }
        }
    }
    assert!(bad.is_empty(), "lockfile drift from the mirror:\n{}", bad.join("\n"));
    // The TCB packages of the strategy's Target table must be among them.
    for tcb in ["near-sdk", "near-sdk-macros", "borsh", "serde_json", "near-account-id", "approval-core"] {
        assert!(ours.contains_key(tcb) && mirror.contains_key(tcb), "{tcb} not in both lockfiles");
    }
    eprintln!("lockfile: {shared} shared packages, all equal");
}
