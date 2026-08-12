// Rust runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using num-bigint: Baillie-PSW primality
// (strong Miller-Rabin base 2 + strong Lucas with Selfridge parameters) and the
// RSA modulus-hygiene detectors (perfect power, small factor, Fermat close
// primes). Reads the frozen corpus and reproduces every verdict byte-for-byte;
// exits 0 iff all match. Mirrors runners/go/verify_go.go and
// runners/typescript/verify_ts.mjs, which mirror the Python oracle.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::env;
use std::fs;
use std::process;

const SMALL_PRIMES: [u32; 54] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
    193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
];

fn big(v: i64) -> BigInt {
    BigInt::from(v)
}

// Integer square root (floor). num-integer's Roots gives floor sqrt for n >= 0,
// matching oracle.py's isqrt.
fn isqrt(n: &BigInt) -> BigInt {
    n.sqrt()
}

// True if n == a**b for integers a >= 2, b >= 2. A modulus of this form has a
// trivially-recoverable factor. Ported from oracle.is_perfect_power.
fn is_perfect_power(n: &BigInt) -> bool {
    if n < &big(4) {
        return false;
    }
    let bl = n.bits(); // bit length (u64)
    let two = big(2);
    for b in 2u64..=bl {
        let mut lo = big(2);
        let mut hi = BigInt::one() << ((bl / b) as usize + 1);
        let exp = b as u32;
        while lo <= hi {
            let mid: BigInt = (&lo + &hi) >> 1u32;
            let p: BigInt = (&mid).pow(exp);
            match p.cmp(n) {
                std::cmp::Ordering::Equal => return true,
                std::cmp::Ordering::Less => lo = &mid + &two - &big(1), // mid + 1
                std::cmp::Ordering::Greater => hi = &mid - &big(1),
            }
        }
    }
    false
}

// Strong (Miller-Rabin) probable-prime test of n to base a. Ported from
// oracle._mr_strong.
fn mr_strong(n: &BigInt, a: &BigInt) -> bool {
    if (n % a).is_zero() {
        return n == a;
    }
    let mut d = n - 1u32;
    let mut r: u64 = 0;
    while d.is_even() {
        d >>= 1u32;
        r += 1;
    }
    let n1 = n - 1u32;
    let mut x = a.modpow(&d, n);
    if x.is_one() || x == n1 {
        return true;
    }
    for _ in 0..r.saturating_sub(1) {
        x = (&x * &x) % n;
        if x == n1 {
            return true;
        }
    }
    false
}

// Jacobi symbol (a/n), n odd positive. Ported from oracle._jacobi.
fn jacobi(a_in: &BigInt, n_in: &BigInt) -> i32 {
    let mut a = a_in.mod_floor(n_in);
    let mut n = n_in.clone();
    let mut result: i32 = 1;
    while !a.is_zero() {
        while a.is_even() {
            a >>= 1;
            let m8 = (&n & big(7)).to_string(); // n % 8, n is odd positive
            let m8v: i64 = m8.parse().unwrap();
            if m8v == 3 || m8v == 5 {
                result = -result;
            }
        }
        std::mem::swap(&mut a, &mut n);
        if (&a & big(3)) == big(3) && (&n & big(3)) == big(3) {
            result = -result;
        }
        a = a.mod_floor(&n);
    }
    if n.is_one() {
        result
    } else {
        0
    }
}

// Strong Lucas probable-prime test with Selfridge parameters (the Lucas half of
// Baillie-PSW). Ported from oracle._lucas_strong.
fn lucas_strong(n: &BigInt) -> bool {
    // Selfridge D: first of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1.
    let mut d_sel = big(5);
    let mut mag: i64 = 5;
    loop {
        let j = jacobi(&d_sel, n);
        if j == -1 {
            break;
        }
        if j == 0 && d_sel.abs() != *n {
            return false; // D shares a factor with n
        }
        mag += 2;
        // magnitudes 5,7,9,11,13,... carry signs +,-,+,-,+,...
        d_sel = if (((mag - 5) / 2) % 2) == 0 {
            big(mag)
        } else {
            big(-mag)
        };
    }
    let p = BigInt::one();
    let q = (BigInt::one() - &d_sel) / big(4);

    // decompose n+1 = d * 2^s with d odd
    let mut d = n + 1u32;
    let mut s: u64 = 0;
    while d.is_even() {
        d >>= 1u32;
        s += 1;
    }

    // U_d, V_d, Q^d mod n via binary expansion of d (MSB first).
    let (mut u, mut v, mut qk) = (BigInt::zero(), big(2), BigInt::one());
    for ch in d.to_str_radix(2).chars() {
        let new_u = (&u * &v).mod_floor(n);
        let new_v = (&v * &v - big(2) * &qk).mod_floor(n);
        u = new_u;
        v = new_v;
        qk = (&qk * &qk).mod_floor(n);
        if ch == '1' {
            let mut nu = &p * &u + &v;
            let mut nv = &d_sel * &u + &p * &v;
            if nu.is_odd() {
                nu += n;
            }
            if nv.is_odd() {
                nv += n;
            }
            u = (nu / big(2)).mod_floor(n);
            v = (nv / big(2)).mod_floor(n);
            qk = (&qk * &q).mod_floor(n);
        }
    }

    if u.is_zero() || v.is_zero() {
        return true;
    }
    for _ in 0..s.saturating_sub(1) {
        v = (&v * &v - big(2) * &qk).mod_floor(n);
        qk = (&qk * &qk).mod_floor(n);
        if v.is_zero() {
            return true;
        }
    }
    false
}

// Baillie-PSW: the ground-truth primality test. Ported from oracle.is_prime.
fn is_prime(n: &BigInt) -> bool {
    if n < &big(2) {
        return false;
    }
    for p in SMALL_PRIMES {
        let bp = big(p as i64);
        if n == &bp {
            return true;
        }
        if (n % &bp).is_zero() {
            return false;
        }
    }
    if !mr_strong(n, &big(2)) {
        return false;
    }
    if is_perfect_power(n) {
        return false;
    }
    lucas_strong(n)
}

// Smallest prime factor of n below `bound` exists? Trial division, mirroring the
// Go/TS ports (early break when p*p > n gives the same answer as oracle's sieve
// walk up to bound).
fn has_small_factor(n: &BigInt, bound: i64) -> bool {
    let bnd = big(bound);
    let two = big(2);
    let mut p = big(2);
    while p <= bnd {
        if &p * &p > *n {
            break;
        }
        if (n % &p).is_zero() {
            return true;
        }
        if p == two {
            p += 1u32;
        } else {
            p += 2u32;
        }
    }
    false
}

// Fermat factorisation, bounded. True if close primes (|p-q| small) are found
// within max_steps. Ported from oracle.fermat_close_factor.
fn fermat_close(n: &BigInt, max_steps: u64) -> bool {
    if n.is_even() {
        return true;
    }
    let mut a = isqrt(n);
    if &a * &a < *n {
        a += 1u32;
    }
    for _ in 0..max_steps {
        let b2 = &a * &a - n;
        if !b2.is_negative() {
            let b = isqrt(&b2);
            if &b * &b == b2 {
                return true;
            }
        }
        a += 1u32;
    }
    false
}

fn allowed_bits(bits: u64) -> bool {
    bits == 2048 || bits == 3072 || bits == 4096
}

fn allowed_e(e: i64) -> bool {
    e == 3 || e == 65537
}

// Accept/reject an RSA public key (n, e). Reject reasons ordered most-structural
// first. Ported from oracle.rsa_modulus_verdict.
fn rsa_verdict(n: &BigInt, e: i64) -> (bool, &'static str) {
    if *n <= big(3) || n.is_even() {
        return (false, "modulus_not_odd_or_too_small");
    }
    if is_perfect_power(n) {
        return (false, "modulus_perfect_power");
    }
    if has_small_factor(n, 1_000_000) {
        return (false, "modulus_small_factor");
    }
    if fermat_close(n, 1 << 16) {
        return (false, "modulus_close_primes");
    }
    if !allowed_bits(n.bits()) {
        return (false, "modulus_bit_length_not_allowed");
    }
    if !allowed_e(e) {
        return (false, "public_exponent_not_allowed");
    }
    if e % 2 == 0 || e < 3 {
        return (false, "public_exponent_invalid");
    }
    (true, "ok")
}

// Batch common-factor (Mining-your-Ps-and-Qs): per-key verdict is "shares a
// prime with another key in the set". True iff there is some j != i with a
// nontrivial common GCD 1 < gcd(n_i, n_j) < n_i. Ported from
// oracle.batch_common_factor_verdicts.
fn batch_common_factor_verdicts(moduli: &[BigInt]) -> Vec<bool> {
    let mut out = Vec::with_capacity(moduli.len());
    for (i, ni) in moduli.iter().enumerate() {
        let mut shared = false;
        for (j, nj) in moduli.iter().enumerate() {
            if i == j {
                continue;
            }
            let g = ni.gcd(nj);
            if g > BigInt::one() && &g < ni {
                shared = true;
                break;
            }
        }
        out.push(shared);
    }
    out
}

// The three prime-order curves' domain parameters (p, a, b), copied EXACTLY from
// oracle.EC_CURVES. p256/p384 use a = p - 3; secp256k1 uses a = 0, b = 7.
fn hexbig(s: &str) -> BigInt {
    BigInt::parse_bytes(s.as_bytes(), 16).unwrap_or_else(|| panic!("bad hex: {s}"))
}

fn ec_curve_params(curve: &str) -> (BigInt, BigInt, BigInt) {
    match curve {
        "p256" => (
            hexbig("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"),
            hexbig("ffffffff00000001000000000000000000000000fffffffffffffffffffffffc"),
            hexbig("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"),
        ),
        "p384" => (
            hexbig("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff"),
            hexbig("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc"),
            hexbig("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef"),
        ),
        "secp256k1" => (
            hexbig("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
            BigInt::zero(),
            big(7),
        ),
        other => panic!("unknown curve: {other}"),
    }
}

// Accept/reject an affine EC public point (x, y) on a named prime-order curve.
// Reject out-of-range coordinates and off-curve points. Ported from
// oracle.ec_key_verdict.
fn ec_key_verdict(curve: &str, x: &BigInt, y: &BigInt) -> (bool, &'static str) {
    let (p, a, b) = ec_curve_params(curve);
    if x.is_negative() || *x >= p || y.is_negative() || *y >= p {
        return (false, "coordinate_out_of_range");
    }
    let lhs = y * y;
    let rhs = x * x * x + &a * x + &b;
    if (lhs - rhs).mod_floor(&p) != BigInt::zero() {
        return (false, "not_on_curve");
    }
    (true, "ok")
}

fn parse_int(s: &str) -> BigInt {
    BigInt::parse_bytes(s.as_bytes(), 10).unwrap_or_else(|| panic!("bad integer: {s}"))
}

fn main() {
    let path = env::args()
        .nth(1)
        .or_else(|| env::var("ALGOVOI_KEYHYGIENE").ok())
        .unwrap_or_else(|| {
            eprintln!("no corpus path (arg 1 or ALGOVOI_KEYHYGIENE)");
            process::exit(2);
        });

    let raw = fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("cannot read corpus: {e}");
        process::exit(2);
    });
    let corpus: serde_json::Value = serde_json::from_str(&raw).unwrap_or_else(|e| {
        eprintln!("cannot parse corpus: {e}");
        process::exit(2);
    });

    let empty: Vec<serde_json::Value> = Vec::new();
    let primality = corpus["primality"].as_array().unwrap_or(&empty);
    let rsa = corpus["rsa_modulus_hygiene"].as_array().unwrap_or(&empty);
    let batch = corpus["batch_common_factor"].as_array().unwrap_or(&empty);
    let ec = corpus["ec_key_hygiene"].as_array().unwrap_or(&empty);

    let mut failures: Vec<String> = Vec::new();

    for (i, c) in primality.iter().enumerate() {
        let value = c["value"].as_str().expect("primality value");
        let expect = c["expect_prime"].as_bool().expect("expect_prime");
        let note = c["note"].as_str().unwrap_or("");
        let got = is_prime(&parse_int(value));
        if got != expect {
            failures.push(format!(
                "primality[{i}] {note}: got prime={got} want {expect}"
            ));
        }
    }

    for (i, c) in rsa.iter().enumerate() {
        let n = parse_int(c["n"].as_str().expect("rsa n"));
        let e = c["e"].as_i64().expect("rsa e");
        let expect_accept = c["expect_accept"].as_bool().expect("expect_accept");
        let reason = c["reason"].as_str().expect("reason");
        let note = c["note"].as_str().unwrap_or("");
        let (accept, got_reason) = rsa_verdict(&n, e);
        if accept != expect_accept || got_reason != reason {
            failures.push(format!(
                "rsa[{i}] {note}: got ({accept},{got_reason}) want ({expect_accept},{reason})"
            ));
        }
    }

    let moduli: Vec<BigInt> = batch
        .iter()
        .map(|c| parse_int(c["n"].as_str().expect("batch n")))
        .collect();
    let verdicts = batch_common_factor_verdicts(&moduli);
    for (i, c) in batch.iter().enumerate() {
        let expect = c["shares_factor"].as_bool().expect("shares_factor");
        let note = c["note"].as_str().unwrap_or("");
        let got = verdicts[i];
        if got != expect {
            failures.push(format!(
                "batch_common_factor[{i}] {note}: got shares={got} want {expect}"
            ));
        }
    }

    for (i, c) in ec.iter().enumerate() {
        let curve = c["curve"].as_str().expect("ec curve");
        let x = parse_int(c["x"].as_str().expect("ec x"));
        let y = parse_int(c["y"].as_str().expect("ec y"));
        let expect_valid = c["expect_valid"].as_bool().expect("expect_valid");
        let reason = c["reason"].as_str().expect("ec reason");
        let note = c["note"].as_str().unwrap_or("");
        let (valid, got_reason) = ec_key_verdict(curve, &x, &y);
        if valid != expect_valid || got_reason != reason {
            failures.push(format!(
                "ec_key_hygiene[{i}] {note}: got ({valid},{got_reason}) want ({expect_valid},{reason})"
            ));
        }
    }

    let total = primality.len() + rsa.len() + batch.len() + ec.len();
    if !failures.is_empty() {
        println!("FAIL: {}/{} cases diverged", failures.len(), total);
        for f in &failures {
            println!("  - {f}");
        }
        process::exit(1);
    }
    println!("rust: {total}/{total} cases matched");
}
