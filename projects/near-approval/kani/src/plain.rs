//! Plain mode: every harness body with the random source. **Not a proof.**
//! Each test also requires every cover it evaluated to have fired, the
//! plain-mode counterpart of Kani's cover check.

use crate::checks;
use crate::src::{take_covers, Rng};

fn run(name: &str, seed: u64, iters: u32, body: fn(&mut Rng)) {
    let _ = take_covers();
    let mut rng = Rng(seed | 1);
    for _ in 0..iters {
        body(&mut rng);
    }
    let covers = take_covers();
    let missed: Vec<_> = covers.iter().filter(|(_, (_, hit))| *hit == 0).collect();
    assert!(missed.is_empty(), "{name}: unsatisfied covers {missed:?}");
}

#[test]
fn h_init() {
    run("h_init", 1, 1, checks::init);
}

#[test]
fn h_step_add() {
    run("h_step_add", 0x9E37_79B9, 20_000, checks::step_add);
}

#[test]
fn h_step_revoke() {
    run("h_step_revoke", 0x85EB_CA6B, 20_000, checks::step_revoke);
}

#[test]
fn h_step_request() {
    run("h_step_request", 0xC2B2_AE35, 20_000, checks::step_request);
}

#[test]
fn h_step_approve() {
    run("h_step_approve", 0x27D4_EB2F, 40_000, checks::step_approve);
}

#[test]
fn h_step_reject() {
    run("h_step_reject", 0x7F4A_7C15, 40_000, checks::step_reject);
}

#[test]
fn h_raw_add() {
    run("h_raw_add", 0x1656_67B1, 20_000, checks::raw_add);
}

#[test]
fn h_raw_revoke() {
    run("h_raw_revoke", 0xD3A2_646C, 20_000, checks::raw_revoke);
}

#[test]
fn h_raw_request() {
    run("h_raw_request", 0xFD70_46C5, 40_000, checks::raw_request);
}

#[test]
fn h_raw_approve() {
    run("h_raw_approve", 0xB55A_4F09, 40_000, checks::raw_approve);
}

#[test]
fn h_raw_reject() {
    run("h_raw_reject", 0x94D0_49BB, 40_000, checks::raw_reject);
}

#[test]
fn h_read() {
    run("h_read", 0x5172_8A3D, 20_000, checks::read);
}

#[test]
fn h_bmc_from_init() {
    // With its _witness instance: one cover family, as under Kani.
    run("h_bmc_from_init", 0x6C8E_9CF5, 400_000, |r| {
        checks::bmc_from_init(r);
        checks::witness_revival(r);
    });
}

#[test]
fn h_ref_toolong() {
    run("h_ref_toolong", 0x4CF5_AD43, 20_000, checks::ref_toolong);
}

#[test]
#[should_panic(expected = "canary")]
fn h_canary() {
    run("h_canary", 0x2F0E_1A1B, 2_000, checks::canary);
}

#[test]
fn h_cut() {
    run("h_cut_add", 0x5851_F42D, 20_000, crate::cutoff::cut_add);
    run(
        "h_cut_revoke",
        0x4C95_7F2D,
        20_000,
        crate::cutoff::cut_revoke,
    );
    run(
        "h_cut_request",
        0x2545_F491,
        20_000,
        crate::cutoff::cut_request,
    );
    run(
        "h_cut_approve",
        0x9E37_79B1,
        40_000,
        crate::cutoff::cut_approve,
    );
    run(
        "h_cut_reject",
        0xBF58_476D,
        40_000,
        crate::cutoff::cut_reject,
    );
}

// ---------------------------------------------------------------------------
// M2: ghost stores (ghost.rs, ghost_checks.rs)
// ---------------------------------------------------------------------------

use crate::ghost_checks as g2;

#[test]
fn h_page_arith() {
    run("h_page_arith", 0x3C6E_F372, 20_000, g2::page_arith);
}

#[test]
fn h_proto() {
    run("h_proto_add", 0xA54F_F53A, 20_000, g2::proto_add);
    run("h_proto_revoke", 0x510E_527F, 20_000, g2::proto_revoke);
    run("h_proto_request", 0x9B05_688C, 40_000, g2::proto_request);
    run("h_proto_approve", 0x1F83_D9AB, 80_000, g2::proto_approve);
    run("h_proto_reject", 0x5BE0_CD19, 40_000, g2::proto_reject);
    run("h_oracle_approve", 0x0AC1_E001, 40_000, g2::oracle_approve);
    run("h_oracle_reject", 0x0AC1_E002, 40_000, g2::oracle_reject);
}

#[test]
fn h_count() {
    run("h_count_add", 0x6A09_E667, 10_000, g2::count_add);
    run("h_count_revoke", 0xBB67_AE85, 10_000, g2::count_revoke);
    run("h_count_request", 0x3C6E_F373, 10_000, g2::count_request);
    run("h_count_approve", 0xA54F_F53B, 20_000, g2::count_approve);
    run("h_count_reject", 0x510E_5271, 20_000, g2::count_reject);
}

#[test]
fn h_refine() {
    run("h_refine_add", 0x428A_2F98, 20_000, g2::refine_add);
    run("h_refine_revoke", 0x7137_4491, 20_000, g2::refine_revoke);
    run("h_refine_request", 0xB5C0_FBCF, 20_000, g2::refine_request);
    run("h_refine_approve", 0xE9B5_DBA5, 40_000, g2::refine_approve);
    run("h_refine_reject", 0x3956_C25B, 40_000, g2::refine_reject);
}

#[test]
fn h_store_laws() {
    run("h_store_laws_mem", 0x59F1_11F1, 20_000, g2::store_laws_mem);
    run(
        "h_store_laws_sparse",
        0x923F_82A4,
        20_000,
        g2::store_laws_sparse,
    );
    run("h_store_laws_arr", 0xAB1C_5ED5, 20_000, g2::store_laws_arr);
}

#[test]
fn h_action_len() {
    run("h_action_len", 0xD807_AA98, 200, g2::action_len);
}

/// RD-4 (plain only): the client loop over logs of up to 250 entries.
#[test]
fn client_enum() {
    run("client_enum", 0x1283_5B01, 3_000, g2::client_enum);
}

/// The `Sparse` header pins the contract source it transliterates: fails
/// when upstream `contract/src/lib.rs` changes (or `status.toml` records
/// another hash), until `ghost.rs` is re-checked and its hash updated.
/// Skipped only where the contract crate is absent entirely
/// (`run-mutants.sh` copies just the core).
#[test]
fn sparse_header_hash() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/..");
    let dir = format!("{root}/source-mirror/contracts/approval/contract");
    if !std::path::Path::new(&dir).is_dir() {
        eprintln!("sparse_header_hash: no {dir}, skipped");
        return;
    }
    let bytes = std::fs::read(format!("{dir}/src/lib.rs")).expect("contract/src/lib.rs");
    let got = sha256_hex(&bytes);
    assert_eq!(
        got,
        crate::ghost::CONTRACT_SHA256,
        "contract/src/lib.rs changed: re-transliterate ghost::Sparse, then update CONTRACT_SHA256 and the ghost.rs header"
    );
    let header = include_str!("ghost.rs");
    assert!(
        header.contains(&format!("//! sha256:   {got}")),
        "ghost.rs header sha256 differs from CONTRACT_SHA256"
    );
    if let Ok(status) = std::fs::read_to_string(format!("{root}/status.toml")) {
        assert!(
            status.contains(&format!("\"contract/src/lib.rs\" = \"{got}\"")),
            "status.toml [source_hashes] records another contract/src/lib.rs"
        );
    }
}

/// FIPS 180-4 SHA-256 (no dependencies in this crate).
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&((data.len() as u64) * 8).to_be_bytes());
    for block in msg.chunks(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let mut v = h;
        for i in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [
                t1.wrapping_add(t2),
                v[0],
                v[1],
                v[2],
                v[3].wrapping_add(t1),
                v[4],
                v[5],
                v[6],
            ];
        }
        for i in 0..8 {
            h[i] = h[i].wrapping_add(v[i]);
        }
    }
    h.iter().map(|x| format!("{x:08x}")).collect()
}

#[test]
fn sha256_known_answer() {
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}
