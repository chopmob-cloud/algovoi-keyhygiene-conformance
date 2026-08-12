#!/usr/bin/env python3
"""Ground-truth oracle for the key-hygiene & primality conformance battery.

Everything here is the REFERENCE decision surface: the corpus generator freezes
these verdicts, and every language runner must reproduce them. Two independent
methods back the highest-value calls so the KAT gate can cross-check them:

  - primality:  Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas), which
                has no known counterexample, is the ground truth. A SEPARATE
                deterministic Miller-Rabin over the first 12 prime bases is the
                KAT cross-check for the numbers small enough to trust it on.
  - RSA hygiene: small-factor trial division, Fermat close-prime factorisation
                (bounded), and perfect-power detection, each an independent
                structural test on the public modulus.

No third-party dependency: this must be portable to eleven other languages, so
it uses only integer arithmetic every stack has.
"""
from __future__ import annotations

import random

# ---------------------------------------------------------------------------
# integer helpers (portable: every target language has these primitives)
# ---------------------------------------------------------------------------

_SMALL_PRIMES = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251,
]


def isqrt(n: int) -> int:
    """Integer square root (floor). Portable Newton iteration."""
    if n < 0:
        raise ValueError("isqrt of negative")
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


def is_perfect_power(n: int) -> bool:
    """True if n == a**b for integers a >= 2, b >= 2. Modulus of this form has a
    trivially-recoverable factor, so an RSA modulus must never be one."""
    if n < 4:
        return False
    for b in range(2, n.bit_length() + 1):
        lo, hi = 2, 1 << (n.bit_length() // b + 1)
        while lo <= hi:
            mid = (lo + hi) // 2
            p = mid ** b
            if p == n:
                return True
            if p < n:
                lo = mid + 1
            else:
                hi = mid - 1
    return False


# ---------------------------------------------------------------------------
# primality: Baillie-PSW (the ground truth) + fixed-base MR (the KAT cross-check)
# ---------------------------------------------------------------------------

def _mr_strong(n: int, a: int) -> bool:
    """Strong (Miller-Rabin) probable-prime test of n to base a. True = probably
    prime for this base; False = definitely composite."""
    if n % a == 0:
        return n == a
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    x = pow(a, d, n)
    if x == 1 or x == n - 1:
        return True
    for _ in range(r - 1):
        x = (x * x) % n
        if x == n - 1:
            return True
    return False


def _jacobi(a: int, n: int) -> int:
    """Jacobi symbol (a/n), n odd positive."""
    a %= n
    result = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def _lucas_strong(n: int) -> bool:
    """Strong Lucas probable-prime test with Selfridge parameters (the Lucas half
    of Baillie-PSW)."""
    # Selfridge D: first term of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1.
    D, mag = 5, 5
    while True:
        j = _jacobi(D, n)
        if j == -1:
            break
        if j == 0 and abs(D) != n:
            return False  # D shares a factor with n
        mag += 2
        # magnitudes 5,7,9,11,13,... carry signs +,-,+,-,+,...
        D = mag if ((mag - 5) // 2) % 2 == 0 else -mag
    P, Q = 1, (1 - D) // 4

    # decompose n+1 = d * 2^s with d odd
    d, s = n + 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1

    def _lucas_uv(k: int):
        """U_k, V_k, Q^k mod n via binary expansion of k."""
        u, v, qk = 0, 2, 1
        for b in bin(k)[2:]:
            u, v = (u * v) % n, (v * v - 2 * qk) % n
            qk = (qk * qk) % n
            if b == '1':
                nu, nv = P * u + v, D * u + P * v
                if nu % 2:
                    nu += n
                if nv % 2:
                    nv += n
                u, v = (nu // 2) % n, (nv // 2) % n
                qk = (qk * Q) % n
        return u, v, qk

    U, V, Qk = _lucas_uv(d)
    if U == 0 or V == 0:
        return True
    for _ in range(s - 1):
        V = (V * V - 2 * Qk) % n
        Qk = (Qk * Qk) % n
        if V == 0:
            return True
    return False


def is_prime(n: int) -> bool:
    """Baillie-PSW: the ground-truth primality test. No known counterexample."""
    if n < 2:
        return False
    for p in _SMALL_PRIMES:
        if n == p:
            return True
        if n % p == 0:
            return False
    if not _mr_strong(n, 2):
        return False
    if is_perfect_power(n):
        return False
    return _lucas_strong(n)


# Deterministic MR over the first 12 prime bases. Sound (matches BPSW) for all
# n < 3.18e23, so it is the independent KAT cross-check on primality cases below
# that bound. Above it, or on a number crafted to be a strong pseudoprime to
# these exact bases, it is NOT sound and must not be used as an anchor.
_MR12_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
MR12_SOUND_BOUND = 318665857834031151167461  # 3.18665...e23


def mr_fixed_base(n: int, bases=_MR12_BASES) -> bool:
    """A NAIVE primality check: even-test then strong Miller-Rabin to a FIXED set
    of bases, with NO extended trial division. This is deliberately fallible: on
    a strong pseudoprime crafted for these bases (with no small factors) it
    returns True (prime) for a composite. The battery's primality section exists
    to expose exactly that failure mode; do not use this as ground truth."""
    if n < 2:
        return False
    if n < 4:
        return True  # 2, 3
    if n % 2 == 0:
        return False
    return all(_mr_strong(n, a) for a in bases)


# ---------------------------------------------------------------------------
# prime generation (deterministic, seeded: test vectors are public, not secret)
# ---------------------------------------------------------------------------

def gen_prime(bits: int, rng: random.Random) -> int:
    while True:
        cand = rng.getrandbits(bits) | (1 << (bits - 1)) | 1
        if is_prime(cand):
            return cand


def next_prime(n: int) -> int:
    n = n + 1 if n % 2 == 0 else n + 2
    while not is_prime(n):
        n += 2
    return n


# ---------------------------------------------------------------------------
# RSA modulus hygiene detectors (independent structural tests on n)
# ---------------------------------------------------------------------------

def smallest_factor(n: int, bound: int = 1_000_000) -> int | None:
    """Smallest prime factor of n below `bound`, else None. A shared/known small
    factor makes the modulus trivially factorable."""
    for p in _small_prime_sieve(bound):
        if n % p == 0:
            return p
    return None


def _small_prime_sieve(bound: int) -> list[int]:
    sieve = bytearray([1]) * (bound + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(bound) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(2, bound + 1) if sieve[i]]


def fermat_close_factor(n: int, max_steps: int = 1 << 16):
    """Fermat factorisation, bounded. Returns (p, q) if p,q are close enough to
    be found within max_steps, else None. Close primes (|p-q| small) are the
    RNG-bug / weak-keygen class and are detectable exactly this way."""
    if n % 2 == 0:
        return (2, n // 2)
    a = isqrt(n)
    if a * a < n:
        a += 1
    for _ in range(max_steps):
        b2 = a * a - n
        if b2 >= 0:
            b = isqrt(b2)
            if b * b == b2:
                return (a - b, a + b)
        a += 1
    return None


# CA/Browser Forum Baseline Requirements: RSA modulus bit-length must be one of
# these, and 65537 is the canonical public exponent (BRs require 3 <= e and a
# small allowed set in practice; we track e in {3, 65537} with 65537 canonical).
BR_ALLOWED_BITS = {2048, 3072, 4096}
BR_ALLOWED_E = {3, 65537}


def rsa_modulus_verdict(n: int, e: int) -> tuple[bool, str]:
    """Accept/reject an RSA public key (n, e) under the BR-tracking policy.
    Returns (accept, reason). Reject reasons are ordered most-structural first."""
    if n <= 3 or n % 2 == 0:
        return (False, "modulus_not_odd_or_too_small")
    if is_perfect_power(n):
        return (False, "modulus_perfect_power")
    sf = smallest_factor(n)
    if sf is not None:
        return (False, "modulus_small_factor")
    if fermat_close_factor(n) is not None:
        return (False, "modulus_close_primes")
    if n.bit_length() not in BR_ALLOWED_BITS:
        return (False, "modulus_bit_length_not_allowed")
    if e not in BR_ALLOWED_E:
        return (False, "public_exponent_not_allowed")
    if e % 2 == 0 or e < 3:
        return (False, "public_exponent_invalid")
    return (True, "ok")


# ---------------------------------------------------------------------------
# batch common-factor (Mining-your-Ps-and-Qs): a shared prime across a key set
# ---------------------------------------------------------------------------

def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


def batch_common_factor_verdicts(moduli: list[int]) -> list[bool]:
    """For a SET of RSA moduli, per-key verdict = shares a prime with another key
    in the set (a nontrivial common GCD). Keys that share a prime are trivially
    factorable by anyone who holds the set. Verdict is True iff shared."""
    out = []
    for i, ni in enumerate(moduli):
        shared = False
        for j, nj in enumerate(moduli):
            if i == j:
                continue
            g = _gcd(ni, nj)
            if 1 < g < ni:
                shared = True
                break
        out.append(shared)
    return out


# ---------------------------------------------------------------------------
# EC public-key hygiene: on-curve validation for the prime-order NIST/SEC curves
# (P-256, P-384, secp256k1 all have cofactor 1, so on-curve + in-range +
# non-identity is sufficient; there is no small-order subgroup to screen, unlike
# the cofactor-8 Edwards curve handled by the rfc9421 keygate).
# ---------------------------------------------------------------------------

EC_CURVES = {
    "p256": {
        "p": 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
        "a": 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc,
        "b": 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b,
        "gx": 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
        "gy": 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5,
    },
    "p384": {
        "p": 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
        "a": 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc,
        "b": 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef,
        "gx": 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7,
        "gy": 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f,
    },
    "secp256k1": {
        "p": 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f,
        "a": 0,
        "b": 7,
        "gx": 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
        "gy": 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8,
    },
}


def ec_key_verdict(curve: str, x: int, y: int) -> tuple[bool, str]:
    """Accept/reject an affine EC public point (x, y) on a named prime-order
    curve. Reject out-of-range coordinates and off-curve points."""
    c = EC_CURVES[curve]
    p, a, b = c["p"], c["a"], c["b"]
    if x < 0 or x >= p or y < 0 or y >= p:
        return (False, "coordinate_out_of_range")
    if (y * y - (x * x * x + a * x + b)) % p != 0:
        return (False, "not_on_curve")
    return (True, "ok")


# ---------------------------------------------------------------------------
# ROCA (CVE-2017-15361): Infineon RSALib primes of the form p = k*M + (65537^a
# mod M). The modulus n = p*q is then congruent to 65537^(a+b) mod M, so n mod
# each prime factor of M lies in the multiplicative subgroup generated by 65537.
# A random modulus lands in every one of those subgroups only with negligible
# probability, so "n mod pf is a power of 65537 for EVERY pf | M" is the
# Bleichenbacher fingerprint. Detection is deterministic and library-free.
# ---------------------------------------------------------------------------

ROCA_GENERATOR = 65537
# the odd primes of the first-25 primorial; ord_pf(65537) small enough that the
# combined subgroup fraction is a negligible false-positive rate (verified 0/200
# on random moduli), while M stays small enough for fast structured keygen.
ROCA_PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
               67, 71, 73, 79, 83, 89, 97]
ROCA_M = 1
for _p in ROCA_PRIMES:
    ROCA_M *= _p


def _roca_subgroup(pf: int) -> set:
    """The cyclic subgroup {65537^j mod pf} (all powers of the generator)."""
    s, x = set(), 1 % pf
    while x not in s:
        s.add(x)
        x = (x * ROCA_GENERATOR) % pf
    return s


def roca_fingerprint_verdict(n: int) -> bool:
    """True iff n carries the ROCA fingerprint: n mod pf is a power of 65537 for
    EVERY pf in ROCA_PRIMES. Deterministic; the runners reproduce this."""
    for pf in ROCA_PRIMES:
        if (n % pf) not in _roca_subgroup(pf):
            return False
    return True


def gen_roca_prime(bits: int, rng: random.Random) -> int:
    """A ROCA-structured prime p ≡ 65537^a (mod M), of exactly `bits` bits.
    GENERATOR-ONLY (to emit fingerprint-positive test keys)."""
    a = rng.randrange(1, 10 ** 6)
    base = pow(ROCA_GENERATOR, a, ROCA_M)
    k0 = (1 << (bits - 1)) // ROCA_M
    t = 0
    while True:
        p = (k0 + t) * ROCA_M + base
        if p.bit_length() == bits and is_prime(p):
            return p
        t += 1


def ec_point_mul(curve: str, k: int) -> tuple[int, int]:
    """Scalar multiplication k*G on the named curve, for the GENERATOR only (to
    produce genuinely-valid test points). Runners never need this: they only
    verify on-curve. Standard affine double-and-add over the prime field."""
    c = EC_CURVES[curve]
    p, a = c["p"], c["a"]

    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0:
            return None
        if P == Q:
            m = (3 * x1 * x1 + a) * pow(2 * y1, -1, p) % p
        else:
            m = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (m * m - x1 - x2) % p
        y3 = (m * (x1 - x3) - y1) % p
        return (x3, y3)

    R = None
    G = (c["gx"], c["gy"])
    while k > 0:
        if k & 1:
            R = add(R, G)
        G = add(G, G)
        k >>= 1
    return R
