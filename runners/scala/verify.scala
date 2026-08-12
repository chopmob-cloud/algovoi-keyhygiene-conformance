//> using scala "3.3.3"
//> using dep "org.json:json:20240303"

// Scala runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using scala.math.BigInt (java.math.BigInteger):
// Baillie-PSW primality (strong Miller-Rabin base 2 + strong Lucas, implemented
// here -- NOT isProbablePrime) and the RSA hygiene detectors (perfect power,
// small factor, close primes). Reads the frozen corpus and reproduces every
// verdict byte-for-byte; exits 0 iff all match.

import java.nio.file.{Files, Paths}
import org.json.JSONObject
import scala.collection.mutable.ArrayBuffer

// ---------------------------------------------------------------------------
// integer helpers
// ---------------------------------------------------------------------------

val SMALL_PRIMES: Array[BigInt] = Array(
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
  239, 241, 251
).map(BigInt(_))

// Integer square root (floor), via java.math.BigInteger.sqrt (exact).
def isqrt(n: BigInt): BigInt = BigInt(n.bigInteger.sqrt())

// True if n == a**b for integers a >= 2, b >= 2 (binary search per exponent).
def isPerfectPower(n: BigInt): Boolean =
  if n < 4 then false
  else
    val bl = n.bitLength
    var b = 2
    var found = false
    while b <= bl && !found do
      var lo = BigInt(2)
      var hi = BigInt(1) << (bl / b + 1)
      while lo <= hi && !found do
        val mid = (lo + hi) / 2
        val p = mid.pow(b)
        val c = p.compare(n)
        if c == 0 then found = true
        else if c < 0 then lo = mid + 1
        else hi = mid - 1
      b += 1
    found

// ---------------------------------------------------------------------------
// primality: Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas)
// ---------------------------------------------------------------------------

// Strong (Miller-Rabin) probable-prime test of n to base a.
def mrStrong(n: BigInt, a: BigInt): Boolean =
  if n % a == 0 then n == a
  else
    var d = n - 1
    var r = 0
    while d % 2 == 0 do
      d = d / 2
      r += 1
    var x = a.modPow(d, n)
    if x == 1 || x == n - 1 then true
    else
      var i = 0
      var res = false
      var cont = true
      while cont && i < r - 1 do
        x = (x * x) % n
        if x == n - 1 then
          res = true
          cont = false
        i += 1
      res

// Jacobi symbol (a/n), n odd positive.
def jacobi(aIn: BigInt, nIn: BigInt): Int =
  var a = ((aIn % nIn) + nIn) % nIn
  var n = nIn
  var result = 1
  while a != 0 do
    while a % 2 == 0 do
      a = a / 2
      val m8 = (n % 8).toInt
      if m8 == 3 || m8 == 5 then result = -result
    val t = a; a = n; n = t
    if a % 4 == 3 && n % 4 == 3 then result = -result
    a = a % n
  if n == 1 then result else 0

// Strong Lucas probable-prime test with Selfridge parameters (Lucas half of BPSW).
def lucasStrong(n: BigInt): Boolean =
  // reduce to non-negative residue mod n (matches Python's % semantics)
  def m(x: BigInt): BigInt =
    val r = x % n
    if r.signum < 0 then r + n else r

  // Selfridge D: first term of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1.
  var D = BigInt(5)
  var mag = 5
  var searching = true
  var earlyComposite = false
  while searching do
    val j = jacobi(D, n)
    if j == -1 then searching = false
    else if j == 0 && D.abs != n then
      searching = false
      earlyComposite = true
    else
      mag += 2
      D = if ((mag - 5) / 2) % 2 == 0 then BigInt(mag) else BigInt(-mag)
  if earlyComposite then false
  else
    val P = BigInt(1)
    val Q = (BigInt(1) - D) / 4

    // decompose n+1 = d * 2^s with d odd
    var d = n + 1
    var s = 0
    while d % 2 == 0 do
      d = d / 2
      s += 1

    // U_d, V_d, Q^d mod n via binary expansion of d
    var u = BigInt(0)
    var v = BigInt(2)
    var qk = BigInt(1)
    val bits = d.toString(2)
    var idx = 0
    while idx < bits.length do
      val ch = bits.charAt(idx)
      u = m(u * v)
      v = m(v * v - 2 * qk)
      qk = m(qk * qk)
      if ch == '1' then
        var nu = P * u + v
        var nv = D * u + P * v
        if nu % 2 != 0 then nu += n
        if nv % 2 != 0 then nv += n
        u = m(nu / 2)
        v = m(nv / 2)
        qk = m(qk * Q)
      idx += 1

    if u == 0 || v == 0 then true
    else
      var i = 0
      var res = false
      var cont = true
      while cont && i < s - 1 do
        v = m(v * v - 2 * qk)
        qk = m(qk * qk)
        if v == 0 then
          res = true
          cont = false
        i += 1
      res

// Baillie-PSW: the ground-truth primality test.
def isPrime(n: BigInt): Boolean =
  if n < 2 then false
  else
    var verdict: Option[Boolean] = None
    var k = 0
    while verdict.isEmpty && k < SMALL_PRIMES.length do
      val p = SMALL_PRIMES(k)
      if n == p then verdict = Some(true)
      else if n % p == 0 then verdict = Some(false)
      k += 1
    verdict match
      case Some(b) => b
      case None =>
        if !mrStrong(n, 2) then false
        else if isPerfectPower(n) then false
        else lucasStrong(n)

// ---------------------------------------------------------------------------
// RSA modulus hygiene detectors
// ---------------------------------------------------------------------------

// Smallest factor of n below `bound` exists? (trial division: 2, then odds)
def smallestFactorExists(n: BigInt, bound: Long = 1000000L): Boolean =
  val b = BigInt(bound)
  var p = BigInt(2)
  var found = false
  var stop = false
  while !stop && p <= b do
    if p * p > n then stop = true
    else if n % p == 0 then
      found = true
      stop = true
    else p = if p == 2 then p + 1 else p + 2
  found

// Fermat factorisation, bounded. True if p,q close enough to be found in maxSteps.
def fermatClose(n: BigInt, maxSteps: Int = 1 << 16): Boolean =
  if n % 2 == 0 then true
  else
    var a = isqrt(n)
    if a * a < n then a += 1
    var i = 0
    var found = false
    while i < maxSteps && !found do
      val b2 = a * a - n
      if b2.signum >= 0 then
        val b = isqrt(b2)
        if b * b == b2 then found = true
      a += 1
      i += 1
    found

val BR_ALLOWED_BITS: Set[Int] = Set(2048, 3072, 4096)
val BR_ALLOWED_E: Set[Int] = Set(3, 65537)

// Accept/reject an RSA public key (n, e). Reject reasons ordered most-structural first.
def rsaVerdict(n: BigInt, e: Int): (Boolean, String) =
  if n <= 3 || n % 2 == 0 then (false, "modulus_not_odd_or_too_small")
  else if isPerfectPower(n) then (false, "modulus_perfect_power")
  else if smallestFactorExists(n) then (false, "modulus_small_factor")
  else if fermatClose(n) then (false, "modulus_close_primes")
  else if !BR_ALLOWED_BITS.contains(n.bitLength) then (false, "modulus_bit_length_not_allowed")
  else if !BR_ALLOWED_E.contains(e) then (false, "public_exponent_not_allowed")
  else if e % 2 == 0 || e < 3 then (false, "public_exponent_invalid")
  else (true, "ok")

// ---------------------------------------------------------------------------
// batch common-factor (Mining-your-Ps-and-Qs): shared prime across a key set
// ---------------------------------------------------------------------------

// For a SET of moduli, a key's verdict is True iff it shares a nontrivial prime
// with another key in the set: some j != i with 1 < gcd(n_i, n_j) < n_i.
def batchCommonFactorVerdicts(moduli: Array[BigInt]): Array[Boolean] =
  val out = Array.fill(moduli.length)(false)
  var i = 0
  while i < moduli.length do
    val ni = moduli(i)
    var j = 0
    var shared = false
    while j < moduli.length && !shared do
      if j != i then
        val g = ni.gcd(moduli(j))
        if g > 1 && g < ni then shared = true
      j += 1
    out(i) = shared
    i += 1
  out

// ---------------------------------------------------------------------------
// EC public-key hygiene: on-curve validation for prime-order NIST/SEC curves.
// (p, a, b) EXACTLY from oracle.EC_CURVES; hex copied verbatim.
// ---------------------------------------------------------------------------

// curve -> (p, a, b)
val EC_CURVES: Map[String, (BigInt, BigInt, BigInt)] = Map(
  "p256" -> (
    BigInt("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff", 16),
    BigInt("ffffffff00000001000000000000000000000000fffffffffffffffffffffffc", 16),
    BigInt("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b", 16)
  ),
  "p384" -> (
    BigInt("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff", 16),
    BigInt("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc", 16),
    BigInt("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef", 16)
  ),
  "secp256k1" -> (
    BigInt("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16),
    BigInt("0", 16),
    BigInt("7", 16)
  )
)

// Accept/reject an affine EC public point (x, y) on a named prime-order curve.
// BigInt.mod is non-negative, matching Python's % on a positive modulus.
def ecVerdict(curve: String, x: BigInt, y: BigInt): (Boolean, String) =
  val (p, a, b) = EC_CURVES(curve)
  if x < 0 || x >= p || y < 0 || y >= p then (false, "coordinate_out_of_range")
  else if (y * y - (x.pow(3) + a * x + b)).mod(p) != 0 then (false, "not_on_curve")
  else (true, "ok")

// ---------------------------------------------------------------------------
// ROCA fingerprint (CVE-2017-15361): Infineon RSALib primes of the form
// p = k*M + (g^a mod M) with g = 65537 and M the product of the policy primes.
// The modulus n = p*q is then congruent to g^(a+b) mod M, so n mod every prime
// factor pf of M lies in the multiplicative subgroup generated by g mod pf. A
// modulus is fingerprint-positive iff n mod pf is a power of g for EVERY pf.
// Deterministic and library-free; g and the prime list come from policy.
// ---------------------------------------------------------------------------

// The cyclic subgroup { g^j mod pf } (all powers of the generator), as Longs.
def rocaSubgroup(pf: Long, g: Long): Set[Long] =
  val s = scala.collection.mutable.Set[Long]()
  var x: Long = 1L % pf
  while !s.contains(x) do
    s.add(x)
    x = (x * g) % pf
  s.toSet

// True iff n mod pf is a power of g for EVERY pf in `primes` (ROCA fingerprint).
def rocaVerdict(n: BigInt, g: Long, primes: Array[Long]): Boolean =
  primes.forall { pf =>
    val r = n.mod(BigInt(pf)).toLong
    rocaSubgroup(pf, g).contains(r)
  }

// ---------------------------------------------------------------------------
// runner
// ---------------------------------------------------------------------------

@main def verify(args: String*): Unit =
  val path =
    if args.nonEmpty then args(0)
    else sys.env.getOrElse("ALGOVOI_KEYHYGIENE", "")
  if path.isEmpty then
    System.err.println("no corpus path given (args(0) or ALGOVOI_KEYHYGIENE)")
    sys.exit(2)

  val text = Files.readString(Paths.get(path))
  val root = new JSONObject(text)

  val failures = ArrayBuffer[String]()

  val prim = root.optJSONArray("primality")
  val primLen = if prim == null then 0 else prim.length
  for i <- 0 until primLen do
    val c = prim.getJSONObject(i)
    val got = isPrime(BigInt(c.getString("value")))
    val want = c.getBoolean("expect_prime")
    if got != want then
      failures += s"primality[$i] ${c.optString("note")}: got prime=$got want $want"

  val rsa = root.optJSONArray("rsa_modulus_hygiene")
  val rsaLen = if rsa == null then 0 else rsa.length
  for i <- 0 until rsaLen do
    val c = rsa.getJSONObject(i)
    val (accept, reason) = rsaVerdict(BigInt(c.getString("n")), c.getInt("e"))
    val wantAccept = c.getBoolean("expect_accept")
    val wantReason = c.getString("reason")
    if accept != wantAccept || reason != wantReason then
      failures += s"rsa[$i] ${c.optString("note")}: got ($accept,$reason) want ($wantAccept,$wantReason)"

  val batch = root.optJSONArray("batch_common_factor")
  val batchLen = if batch == null then 0 else batch.length
  val batchModuli = Array.tabulate(batchLen)(i => BigInt(batch.getJSONObject(i).getString("n")))
  val batchVerdicts = batchCommonFactorVerdicts(batchModuli)
  for i <- 0 until batchLen do
    val c = batch.getJSONObject(i)
    val got = batchVerdicts(i)
    val want = c.getBoolean("shares_factor")
    if got != want then
      failures += s"batch_common_factor[$i] ${c.optString("note")}: got shares=$got want $want"

  val ec = root.optJSONArray("ec_key_hygiene")
  val ecLen = if ec == null then 0 else ec.length
  for i <- 0 until ecLen do
    val c = ec.getJSONObject(i)
    val (valid, reason) = ecVerdict(c.getString("curve"), BigInt(c.getString("x")), BigInt(c.getString("y")))
    val wantValid = c.getBoolean("expect_valid")
    val wantReason = c.getString("reason")
    if valid != wantValid || reason != wantReason then
      failures += s"ec_key_hygiene[$i] ${c.optString("note")}: got ($valid,$reason) want ($wantValid,$wantReason)"

  val roca = root.optJSONArray("roca_fingerprint")
  val rocaLen = if roca == null then 0 else roca.length
  if rocaLen > 0 then
    val policy = root.getJSONObject("policy")
    val rocaG = policy.getLong("roca_generator")
    val primesArr = policy.getJSONArray("roca_primes")
    val rocaPrimes = Array.tabulate(primesArr.length)(i => primesArr.getLong(i))
    for i <- 0 until rocaLen do
      val c = roca.getJSONObject(i)
      val got = rocaVerdict(BigInt(c.getString("n")), rocaG, rocaPrimes)
      val want = c.getBoolean("roca_vulnerable")
      if got != want then
        failures += s"roca_fingerprint[$i] ${c.optString("note")}: got roca=$got want $want"

  val total = primLen + rsaLen + batchLen + ecLen + rocaLen
  if failures.nonEmpty then
    println(s"FAIL: ${failures.length}/$total cases diverged")
    failures.take(20).foreach(f => println("  - " + f))
    sys.exit(1)
  else
    println(s"scala: $total/$total cases matched")
    sys.exit(0)
