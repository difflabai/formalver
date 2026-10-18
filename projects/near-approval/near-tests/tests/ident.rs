//! ST-7, the checked half of ASM-IDENT: `PartialEq` on near-sdk's `AccountId`
//! and `PublicKey` is an equivalence that coincides with Borsh-byte equality,
//! so the core's `==` on identities (the only way it compares them, besides
//! `Clone`) and the store's `prefix ‖ borsh(key)` addressing agree.
//!
//! Both are derived over a single field (`AccountId(Box<str>)`,
//! `PublicKey { data: Vec<u8> }`) whose Borsh form is `u32 len ‖ bytes`, so the
//! claim holds by construction; this test pins it for the locked near-sdk so a
//! hand-written `PartialEq` or a new field shows up. The other half, that the
//! core needs nothing of `A`/`K` beyond `Clone` and `PartialEq`, is enforced by
//! the opaque identity newtypes in the Kani crate (a new bound breaks the build).
//!
//! Cases: edge identities (shortest/longest accounts, implicit accounts, keys of
//! every curve, keys equal except in one byte, the same tail under different
//! curves), then IDENT_PAIRS random pairs (default 200000), half of them built
//! equal by an independent route (parse of the printed form, Borsh round trip).
//!
// PROP: ST-7

use near_approval_near_tests::*;
use near_sdk::borsh;
use near_sdk::{AccountId, CurveType, PublicKey};

fn b<T: borsh::BorshSerialize>(x: &T) -> Vec<u8> {
    borsh::to_vec(x).unwrap()
}

/// `==` matches Borsh equality on this pair, symmetrically, and each side
/// equals its own clone and its own Borsh round trip.
fn check<T>(x: &T, y: &T)
where
    T: PartialEq + Clone + std::fmt::Debug + borsh::BorshSerialize + borsh::BorshDeserialize,
{
    assert_eq!(x == y, b(x) == b(y), "== vs borsh on {x:?} / {y:?}");
    assert_eq!(x == y, y == x, "symmetry on {x:?} / {y:?}");
    for z in [x, y] {
        assert!(z == z, "reflexivity on {z:?}");
        assert!(z.clone() == *z, "clone on {z:?}");
        let back: T = borsh::from_slice(&b(z)).unwrap();
        assert!(back == *z, "borsh round trip on {z:?}");
    }
}

const ACCT_CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789";

fn random_account(rng: &mut Rng) -> AccountId {
    loop {
        let parts = 1 + rng.below(3);
        let mut s = String::new();
        for i in 0..parts {
            if i > 0 {
                s.push(if rng.chance(80) { '.' } else { '-' });
            }
            let max = if rng.chance(10) { 30 } else { 4 };
            for _ in 0..1 + rng.below(max) {
                s.push(*rng.pick(ACCT_CHARS) as char);
            }
        }
        if let Ok(a) = s.parse() {
            return a;
        }
    }
}

fn random_key(rng: &mut Rng) -> PublicKey {
    let (curve, len) = match rng.below(10) {
        0 => (CurveType::MLDSA65, 1952),
        1..=4 => (CurveType::SECP256K1, 64),
        _ => (CurveType::ED25519, 32),
    };
    // Few distinct byte values so unequal keys often share long prefixes.
    let data = (0..len).map(|_| rng.below(3) as u8).collect();
    PublicKey::from_parts(curve, data).unwrap()
}

/// A key that equals `k` iff `flip` is false: either an independent rebuild
/// or the same bytes with one byte changed.
fn sibling_key(rng: &mut Rng, k: &PublicKey, flip: bool) -> PublicKey {
    if !flip {
        return match rng.below(2) {
            0 => pk_str(k).parse().unwrap(),
            _ => borsh::from_slice(&b(k)).unwrap(),
        };
    }
    let mut data = k.as_bytes()[1..].to_vec();
    let i = rng.below(data.len() as u64) as usize;
    data[i] ^= 1 + rng.below(255) as u8;
    PublicKey::from_parts(k.curve_type(), data).unwrap()
}

fn sibling_account(rng: &mut Rng, a: &AccountId) -> AccountId {
    match rng.below(2) {
        0 => a.as_str().parse().unwrap(),
        _ => borsh::from_slice(&b(a)).unwrap(),
    }
}

#[test]
fn st7_identity_eq_is_borsh_eq_edges() {
    let accts: Vec<AccountId> = [
        "aa",
        "a1",
        "a-b",
        "a.b",
        "near",
        "owner.near",
        "owner.nea",
        "owner.near.near",
        &"a".repeat(64),
        &"0".repeat(64),
        &"f".repeat(64),
        "0x1111111111111111111111111111111111111111",
    ]
    .iter()
    .map(|s| s.parse().unwrap())
    .chain([long_account('a'), long_account('b')])
    .collect();
    for x in &accts {
        for y in &accts {
            check(x, y);
        }
    }

    let mut ks = vec![ed25519(0), ed25519(1), secp256k1(0), secp256k1(1), mldsa65(0), mldsa65(1)];
    for k in [ed25519(7), secp256k1(7), mldsa65(7)] {
        let n = k.as_bytes().len() - 1;
        for i in [0, n / 2, n - 1] {
            let mut d = k.as_bytes()[1..].to_vec();
            d[i] = 8;
            ks.push(PublicKey::from_parts(k.curve_type(), d).unwrap());
        }
        ks.push(k);
    }
    // ed25519 and secp256k1 keys whose data starts with the same 32 bytes:
    // different curve byte and length, so unequal both ways.
    let tail = vec![5u8; 32];
    ks.push(PublicKey::from_parts(CurveType::ED25519, tail.clone()).unwrap());
    ks.push(PublicKey::from_parts(CurveType::SECP256K1, [tail.clone(), tail].concat()).unwrap());
    for x in &ks {
        for y in &ks {
            check(x, y);
        }
    }
}

#[test]
fn st7_identity_eq_is_borsh_eq_random() {
    let pairs = env_u64("IDENT_PAIRS", 200_000);
    let mut rng = Rng::new(env_u64("IDENT_SEED", 1));
    let (mut eq_a, mut eq_k) = (0u64, 0u64);
    for _ in 0..pairs {
        let a = random_account(&mut rng);
        let a2 = if rng.chance(50) { sibling_account(&mut rng, &a) } else { random_account(&mut rng) };
        eq_a += (a == a2) as u64;
        check(&a, &a2);

        let k = random_key(&mut rng);
        let k2 = match rng.below(3) {
            0 => sibling_key(&mut rng, &k, false),
            1 => sibling_key(&mut rng, &k, true),
            _ => random_key(&mut rng),
        };
        eq_k += (k == k2) as u64;
        check(&k, &k2);
    }
    // Both outcomes are exercised for both types.
    assert!(eq_a > pairs / 4 && eq_a < pairs, "equal account pairs: {eq_a}/{pairs}");
    assert!(eq_k > pairs / 4 && eq_k < pairs, "equal key pairs: {eq_k}/{pairs}");
    eprintln!("ST-7: {pairs} pairs, {eq_a} equal accounts, {eq_k} equal keys");
}
