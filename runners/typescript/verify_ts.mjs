// TypeScript/Node reference runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using native BigInt: Baillie-PSW primality
// and the RSA hygiene detectors. Reads the frozen corpus and reproduces every
// verdict; exits 0 iff all match. Consensus with the Python runner (and the ten
// others) means every stack agrees on every verdict byte-for-byte.
import { readFileSync } from "node:fs";

const TWO = 2n;

function isqrt(n) {
  if (n < 0n) throw new Error("isqrt negative");
  if (n < 2n) return n;
  let x = 1n << ((BigInt(n.toString(2).length) + 1n) / 2n);
  for (;;) {
    const y = (x + n / x) / 2n;
    if (y >= x) return x;
    x = y;
  }
}

function bitLength(n) {
  return n <= 0n ? 0 : n.toString(2).length;
}

function isPerfectPower(n) {
  if (n < 4n) return false;
  const bl = bitLength(n);
  for (let b = 2; b <= bl; b++) {
    let lo = 2n, hi = 1n << BigInt(Math.floor(bl / b) + 1);
    while (lo <= hi) {
      const mid = (lo + hi) / 2n;
      const p = mid ** BigInt(b);
      if (p === n) return true;
      if (p < n) lo = mid + 1n; else hi = mid - 1n;
    }
  }
  return false;
}

function powmod(base, exp, mod) {
  let result = 1n;
  base %= mod;
  while (exp > 0n) {
    if (exp & 1n) result = (result * base) % mod;
    base = (base * base) % mod;
    exp >>= 1n;
  }
  return result;
}

const SMALL_PRIMES = [2n,3n,5n,7n,11n,13n,17n,19n,23n,29n,31n,37n,41n,43n,47n,53n,
  59n,61n,67n,71n,73n,79n,83n,89n,97n,101n,103n,107n,109n,113n,127n,131n,137n,
  139n,149n,151n,157n,163n,167n,173n,179n,181n,191n,193n,197n,199n,211n,223n,
  227n,229n,233n,239n,241n,251n];

function mrStrong(n, a) {
  a = ((a % n) + n) % n;
  if (a === 0n) return true;
  let d = n - 1n, r = 0n;
  while ((d & 1n) === 0n) { d >>= 1n; r++; }
  let x = powmod(a, d, n);
  if (x === 1n || x === n - 1n) return true;
  for (let i = 0n; i < r - 1n; i++) {
    x = (x * x) % n;
    if (x === n - 1n) return true;
  }
  return false;
}

function jacobi(a, n) {
  a = ((a % n) + n) % n;
  let result = 1;
  while (a !== 0n) {
    while ((a & 1n) === 0n) {
      a >>= 1n;
      const m8 = n % 8n;
      if (m8 === 3n || m8 === 5n) result = -result;
    }
    [a, n] = [n, a];
    if (a % 4n === 3n && n % 4n === 3n) result = -result;
    a %= n;
  }
  return n === 1n ? result : 0;
}

function lucasStrong(n) {
  let D = 5n, mag = 5n;
  for (;;) {
    const j = jacobi(D, n);
    if (j === -1) break;
    if (j === 0 && (D < 0n ? -D : D) !== n) return false;
    mag += 2n;
    D = (((mag - 5n) / 2n) % 2n === 0n) ? mag : -mag;
  }
  const P = 1n, Q = (1n - D) / 4n;
  let d = n + 1n, s = 0n;
  while ((d & 1n) === 0n) { d >>= 1n; s++; }

  // U_d, V_d, Q^d mod n via binary expansion
  let u = 0n, v = 2n, qk = 1n;
  const bits = d.toString(2);
  for (const c of bits) {
    [u, v] = [(u * v) % n, ((v * v - 2n * qk) % n + n) % n];
    qk = (qk * qk) % n;
    if (c === "1") {
      let nu = P * u + v, nv = D * u + P * v;
      if (nu & 1n) nu += n;
      if (nv & 1n) nv += n;
      u = ((nu / 2n) % n + n) % n;
      v = ((nv / 2n) % n + n) % n;
      qk = (qk * Q % n + n) % n;
    }
  }
  if (u === 0n || v === 0n) return true;
  for (let i = 0n; i < s - 1n; i++) {
    v = ((v * v - 2n * qk) % n + n) % n;
    qk = (qk * qk) % n;
    if (v === 0n) return true;
  }
  return false;
}

function isPrime(n) {
  if (n < 2n) return false;
  for (const p of SMALL_PRIMES) {
    if (n === p) return true;
    if (n % p === 0n) return false;
  }
  if (!mrStrong(n, 2n)) return false;
  if (isPerfectPower(n)) return false;
  return lucasStrong(n);
}

function smallestFactor(n, bound = 1000000n) {
  for (let p = 2n; p <= bound; p += (p === 2n ? 1n : 2n)) {
    if (p * p > n) break;
    if (n % p === 0n) return p;
  }
  return null;
}

function fermatClose(n, maxSteps = 1 << 16) {
  if (n % 2n === 0n) return [2n, n / 2n];
  let a = isqrt(n);
  if (a * a < n) a += 1n;
  for (let i = 0; i < maxSteps; i++) {
    const b2 = a * a - n;
    if (b2 >= 0n) {
      const b = isqrt(b2);
      if (b * b === b2) return [a - b, a + b];
    }
    a += 1n;
  }
  return null;
}

const BR_ALLOWED_BITS = new Set([2048, 3072, 4096]);
const BR_ALLOWED_E = new Set([3n, 65537n]);

function rsaVerdict(n, e) {
  if (n <= 3n || n % 2n === 0n) return [false, "modulus_not_odd_or_too_small"];
  if (isPerfectPower(n)) return [false, "modulus_perfect_power"];
  if (smallestFactor(n) !== null) return [false, "modulus_small_factor"];
  if (fermatClose(n) !== null) return [false, "modulus_close_primes"];
  if (!BR_ALLOWED_BITS.has(bitLength(n))) return [false, "modulus_bit_length_not_allowed"];
  if (!BR_ALLOWED_E.has(e)) return [false, "public_exponent_not_allowed"];
  if (e % 2n === 0n || e < 3n) return [false, "public_exponent_invalid"];
  return [true, "ok"];
}

// ---------------------------------------------------------------------------
// batch common-factor (Mining-your-Ps-and-Qs): a shared prime across a key set
// ---------------------------------------------------------------------------

function gcd(a, b) {
  while (b) {
    [a, b] = [b, a % b];
  }
  return a;
}

function batchCommonFactorVerdicts(moduli) {
  const out = [];
  for (let i = 0; i < moduli.length; i++) {
    const ni = moduli[i];
    let shared = false;
    for (let j = 0; j < moduli.length; j++) {
      if (i === j) continue;
      const g = gcd(ni, moduli[j]);
      if (g > 1n && g < ni) { shared = true; break; }
    }
    out.push(shared);
  }
  return out;
}

// ---------------------------------------------------------------------------
// EC public-key hygiene: on-curve validation for the prime-order NIST/SEC curves.
// (p,a,b) copied EXACTLY from oracle.EC_CURVES; non-negative modulo throughout.
// ---------------------------------------------------------------------------

const EC_CURVES = {
  p256: {
    p: 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn,
    a: 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffcn,
    b: 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn,
  },
  p384: {
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffn,
    a: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffcn,
    b: 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aefn,
  },
  secp256k1: {
    p: 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn,
    a: 0n,
    b: 7n,
  },
};

function ecKeyVerdict(curve, x, y) {
  const { p, a, b } = EC_CURVES[curve];
  if (x < 0n || x >= p || y < 0n || y >= p) return [false, "coordinate_out_of_range"];
  const lhs = ((y * y) % p + p) % p;
  const rhs = ((x * x * x + a * x + b) % p + p) % p;
  if (((lhs - rhs) % p + p) % p !== 0n) return [false, "not_on_curve"];
  return [true, "ok"];
}

// ---------------------------------------------------------------------------
// ROCA (CVE-2017-15361): Infineon RSALib primes p = k*M + (g^a mod M) leave the
// modulus n = p*q congruent to g^(a+b) mod M, so n mod each prime factor pf of M
// lands in the multiplicative subgroup generated by g (= 65537). The fingerprint
// is "n mod pf is a power of g for EVERY pf". Generator and prime list come from
// the corpus policy. BigInt throughout for the modular arithmetic on n.
// ---------------------------------------------------------------------------

function rocaSubgroup(pf, g) {
  // { g^j mod pf : j = 0,1,2,... } built by iterating until a value repeats.
  const s = new Set();
  let x = 1n % pf;
  while (!s.has(x)) {
    s.add(x);
    x = (x * g) % pf;
  }
  return s;
}

function rocaFingerprintVerdict(n, g, primes) {
  for (const pf of primes) {
    if (!rocaSubgroup(pf, g).has(n % pf)) return false;
  }
  return true;
}

function main() {
  const path = process.argv[2] || process.env.ALGOVOI_KEYHYGIENE;
  const corpus = JSON.parse(readFileSync(path, "utf-8"));
  const failures = [];

  (corpus.primality || []).forEach((c, i) => {
    const got = isPrime(BigInt(c.value));
    if (got !== c.expect_prime) failures.push(`primality[${i}] ${c.note}: got prime=${got} want ${c.expect_prime}`);
  });
  (corpus.rsa_modulus_hygiene || []).forEach((c, i) => {
    const [accept, reason] = rsaVerdict(BigInt(c.n), BigInt(c.e));
    if (accept !== c.expect_accept || reason !== c.reason)
      failures.push(`rsa[${i}] ${c.note}: got (${accept},${reason}) want (${c.expect_accept},${c.reason})`);
  });

  const batch = corpus.batch_common_factor || [];
  if (batch.length) {
    const moduli = batch.map((c) => BigInt(c.n));
    const verdicts = batchCommonFactorVerdicts(moduli);
    batch.forEach((c, i) => {
      if (verdicts[i] !== c.shares_factor)
        failures.push(`batch_common_factor[${i}] ${c.note}: got shares=${verdicts[i]} want ${c.shares_factor}`);
    });
  }
  (corpus.ec_key_hygiene || []).forEach((c, i) => {
    const [valid, reason] = ecKeyVerdict(c.curve, BigInt(c.x), BigInt(c.y));
    if (valid !== c.expect_valid || reason !== c.reason)
      failures.push(`ec_key_hygiene[${i}] ${c.note}: got (${valid},${reason}) want (${c.expect_valid},${c.reason})`);
  });

  const rocaG = BigInt((corpus.policy || {}).roca_generator);
  const rocaPrimes = ((corpus.policy || {}).roca_primes || []).map((p) => BigInt(p));
  (corpus.roca_fingerprint || []).forEach((c, i) => {
    const got = rocaFingerprintVerdict(BigInt(c.n), rocaG, rocaPrimes);
    if (got !== c.roca_vulnerable)
      failures.push(`roca_fingerprint[${i}] ${c.note}: got roca=${got} want ${c.roca_vulnerable}`);
  });

  const total = (corpus.primality || []).length + (corpus.rsa_modulus_hygiene || []).length
    + (corpus.batch_common_factor || []).length + (corpus.ec_key_hygiene || []).length
    + (corpus.roca_fingerprint || []).length;
  if (failures.length) {
    console.log(`FAIL: ${failures.length}/${total} cases diverged`);
    failures.slice(0, 20).forEach((f) => console.log("  -", f));
    process.exit(1);
  }
  console.log(`typescript: ${total}/${total} cases matched`);
}

main();
