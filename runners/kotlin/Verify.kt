// Kotlin runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using java.math.BigInteger: Baillie-PSW
// primality (strong Miller-Rabin base 2 + strong Lucas, implemented here — NOT
// BigInteger.isProbablePrime, which uses random bases) and the RSA hygiene
// detectors (perfect power, small factor, close primes). Reads the frozen
// corpus and reproduces every verdict byte-for-byte; exits 0 iff all match.
//
// Compile/run:
//   kotlinc Verify.kt -cp json.jar -include-runtime -d v.jar \
//     && java -cp v.jar:json.jar VerifyKt <corpus_path>
import org.json.JSONObject
import java.io.File
import java.math.BigInteger
import kotlin.system.exitProcess

private val ZERO: BigInteger = BigInteger.ZERO
private val ONE: BigInteger = BigInteger.ONE
private val TWO: BigInteger = BigInteger.valueOf(2)
private val THREE: BigInteger = BigInteger.valueOf(3)
private val FOUR: BigInteger = BigInteger.valueOf(4)

private val SMALL_PRIMES: List<BigInteger> = longArrayOf(
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251
).map { BigInteger.valueOf(it) }

// ---------------------------------------------------------------------------
// integer helpers
// ---------------------------------------------------------------------------

// Integer square root (floor). BigInteger.sqrt() is exact and available on JDK 9+.
private fun isqrt(n: BigInteger): BigInteger = n.sqrt()

// True if n == a**b for integers a >= 2, b >= 2. Mirrors oracle.is_perfect_power:
// binary search on the base for every exponent b in [2, bitLength].
private fun isPerfectPower(n: BigInteger): Boolean {
    if (n < FOUR) return false
    val bl = n.bitLength()
    for (b in 2..bl) {
        var lo = TWO
        var hi = ONE.shiftLeft(bl / b + 1)
        while (lo <= hi) {
            val mid = lo.add(hi).shiftRight(1)
            val p = mid.pow(b)
            val c = p.compareTo(n)
            when {
                c == 0 -> return true
                c < 0 -> lo = mid.add(ONE)
                else -> hi = mid.subtract(ONE)
            }
        }
    }
    return false
}

// ---------------------------------------------------------------------------
// primality: Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas)
// ---------------------------------------------------------------------------

// Strong (Miller-Rabin) probable-prime test of n to base a. Mirrors oracle._mr_strong.
private fun mrStrong(n: BigInteger, a: BigInteger): Boolean {
    if (n.mod(a).signum() == 0) return n == a
    var d = n.subtract(ONE)
    var r = 0
    while (!d.testBit(0)) {
        d = d.shiftRight(1)
        r += 1
    }
    var x = a.modPow(d, n)
    val nMinus1 = n.subtract(ONE)
    if (x == ONE || x == nMinus1) return true
    for (i in 0 until r - 1) {
        x = x.multiply(x).mod(n)
        if (x == nMinus1) return true
    }
    return false
}

// Jacobi symbol (a/n), n odd positive. Mirrors oracle._jacobi.
private fun jacobi(aIn: BigInteger, nIn: BigInteger): Int {
    var a = aIn.mod(nIn)
    var n = nIn
    var result = 1
    while (a.signum() != 0) {
        while (!a.testBit(0)) {
            a = a.shiftRight(1)
            val m8 = n.mod(BigInteger.valueOf(8)).toInt()
            if (m8 == 3 || m8 == 5) result = -result
        }
        val tmp = a
        a = n
        n = tmp
        if (a.mod(FOUR).toInt() == 3 && n.mod(FOUR).toInt() == 3) result = -result
        a = a.mod(n)
    }
    return if (n == ONE) result else 0
}

// Strong Lucas probable-prime test with Selfridge parameters. Mirrors
// oracle._lucas_strong (the Lucas half of Baillie-PSW).
private fun lucasStrong(n: BigInteger): Boolean {
    // Selfridge D: first term of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1.
    var d0 = 5L
    var mag = 5L
    var dBig = BigInteger.valueOf(d0)
    while (true) {
        val j = jacobi(dBig, n)
        if (j == -1) break
        if (j == 0 && dBig.abs() != n) return false // D shares a factor with n
        mag += 2
        // magnitudes 5,7,9,11,... carry signs +,-,+,-,...
        d0 = if (((mag - 5) / 2) % 2 == 0L) mag else -mag
        dBig = BigInteger.valueOf(d0)
    }
    val d = dBig
    val p = ONE
    val q = ONE.subtract(d).divide(FOUR) // (1 - D) / 4, exact (D === 1 mod 4)

    // decompose n+1 = dd * 2^s with dd odd
    var dd = n.add(ONE)
    var s = 0
    while (!dd.testBit(0)) {
        dd = dd.shiftRight(1)
        s += 1
    }

    // U_dd, V_dd, Q^dd mod n via binary expansion (MSB first) of dd.
    var u = ZERO
    var v = TWO
    var qk = ONE
    val bits = dd.toString(2)
    for (ch in bits) {
        val nu0 = u.multiply(v).mod(n)
        val nv0 = v.multiply(v).subtract(TWO.multiply(qk)).mod(n)
        u = nu0
        v = nv0
        qk = qk.multiply(qk).mod(n)
        if (ch == '1') {
            var nu = p.multiply(u).add(v)
            var nv = d.multiply(u).add(p.multiply(v))
            if (nu.testBit(0)) nu = nu.add(n)
            if (nv.testBit(0)) nv = nv.add(n)
            u = nu.shiftRight(1).mod(n)
            v = nv.shiftRight(1).mod(n)
            qk = qk.multiply(q).mod(n)
        }
    }

    if (u.signum() == 0 || v.signum() == 0) return true
    for (i in 0 until s - 1) {
        v = v.multiply(v).subtract(TWO.multiply(qk)).mod(n)
        qk = qk.multiply(qk).mod(n)
        if (v.signum() == 0) return true
    }
    return false
}

// Baillie-PSW: the ground-truth primality test. Mirrors oracle.is_prime.
private fun isPrime(n: BigInteger): Boolean {
    if (n < TWO) return false
    for (pr in SMALL_PRIMES) {
        if (n == pr) return true
        if (n.mod(pr).signum() == 0) return false
    }
    if (!mrStrong(n, TWO)) return false
    if (isPerfectPower(n)) return false
    return lucasStrong(n)
}

// ---------------------------------------------------------------------------
// RSA modulus hygiene detectors
// ---------------------------------------------------------------------------

// Smallest prime factor of n below `bound`, else null. Mirrors the validated
// Go/TS trial-division ports (2, then odds, early-out when p*p > n).
private fun smallestFactor(n: BigInteger, bound: Long = 1_000_000L): BigInteger? {
    var p = TWO
    val boundBig = BigInteger.valueOf(bound)
    while (p <= boundBig) {
        if (p.multiply(p) > n) break
        if (n.mod(p).signum() == 0) return p
        p = if (p == TWO) THREE else p.add(TWO)
    }
    return null
}

// Fermat factorisation, bounded. Returns true if close factors are found within
// maxSteps. Mirrors oracle.fermat_close_factor.
private fun fermatClose(n: BigInteger, maxSteps: Int = 1 shl 16): Boolean {
    if (!n.testBit(0)) return true // even
    var a = isqrt(n)
    if (a.multiply(a) < n) a = a.add(ONE)
    var steps = 0
    while (steps < maxSteps) {
        val b2 = a.multiply(a).subtract(n)
        if (b2.signum() >= 0) {
            val b = isqrt(b2)
            if (b.multiply(b) == b2) return true
        }
        a = a.add(ONE)
        steps += 1
    }
    return false
}

private val BR_ALLOWED_BITS = setOf(2048, 3072, 4096)
private val BR_ALLOWED_E = setOf(3, 65537)

// Accept/reject an RSA public key (n, e). Mirrors oracle.rsa_modulus_verdict,
// reject reasons ordered most-structural first.
private fun rsaVerdict(n: BigInteger, e: Int): Pair<Boolean, String> {
    if (n <= THREE || !n.testBit(0)) return Pair(false, "modulus_not_odd_or_too_small")
    if (isPerfectPower(n)) return Pair(false, "modulus_perfect_power")
    if (smallestFactor(n) != null) return Pair(false, "modulus_small_factor")
    if (fermatClose(n)) return Pair(false, "modulus_close_primes")
    if (n.bitLength() !in BR_ALLOWED_BITS) return Pair(false, "modulus_bit_length_not_allowed")
    if (e !in BR_ALLOWED_E) return Pair(false, "public_exponent_not_allowed")
    if (e % 2 == 0 || e < 3) return Pair(false, "public_exponent_invalid")
    return Pair(true, "ok")
}

// ---------------------------------------------------------------------------

fun main(args: Array<String>) {
    val path = if (args.isNotEmpty()) args[0] else System.getenv("ALGOVOI_KEYHYGIENE")
    if (path == null) {
        System.err.println("no corpus path (arg[0] or ALGOVOI_KEYHYGIENE)")
        exitProcess(2)
    }
    val root = JSONObject(File(path).readText())
    val failures = ArrayList<String>()

    val primality = root.optJSONArray("primality")
    val primalityCount = primality?.length() ?: 0
    if (primality != null) {
        for (i in 0 until primality.length()) {
            val c = primality.getJSONObject(i)
            val note = c.optString("note")
            val got = isPrime(BigInteger(c.getString("value")))
            val want = c.getBoolean("expect_prime")
            if (got != want) {
                failures.add("primality[$i] $note: got prime=$got want $want")
            }
        }
    }

    val rsa = root.optJSONArray("rsa_modulus_hygiene")
    val rsaCount = rsa?.length() ?: 0
    if (rsa != null) {
        for (i in 0 until rsa.length()) {
            val c = rsa.getJSONObject(i)
            val note = c.optString("note")
            val (accept, reason) = rsaVerdict(BigInteger(c.getString("n")), c.getInt("e"))
            val wantAccept = c.getBoolean("expect_accept")
            val wantReason = c.getString("reason")
            if (accept != wantAccept || reason != wantReason) {
                failures.add("rsa[$i] $note: got ($accept,$reason) want ($wantAccept,$wantReason)")
            }
        }
    }

    val total = primalityCount + rsaCount
    if (failures.isNotEmpty()) {
        println("FAIL: ${failures.size}/$total cases diverged")
        for (f in failures.take(20)) println("  - $f")
        exitProcess(1)
    }
    println("kotlin: $total/$total cases matched")
    exitProcess(0)
}
