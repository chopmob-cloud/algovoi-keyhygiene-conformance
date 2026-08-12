// Java runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using java.math.BigInteger: Baillie-PSW
// primality (strong Miller-Rabin base 2 + strong Lucas, implemented directly, NOT
// BigInteger.isProbablePrime which uses random bases) and the RSA hygiene
// detectors (perfect power, small factor, close primes). Reads the frozen corpus
// and reproduces every verdict byte-for-byte; exits 0 iff all match.
//
// Build/run:
//   javac -cp json.jar Verify.java && java -cp .:json.jar Verify <corpus_path>
//   (on Windows the classpath separator is ';')

import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.json.JSONArray;
import org.json.JSONObject;

public class Verify {

    private static final BigInteger ZERO = BigInteger.ZERO;
    private static final BigInteger ONE = BigInteger.ONE;
    private static final BigInteger TWO = BigInteger.valueOf(2);
    private static final BigInteger THREE = BigInteger.valueOf(3);
    private static final BigInteger FOUR = BigInteger.valueOf(4);

    private static final int[] SMALL_PRIMES = {
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
        157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
        239, 241, 251,
    };

    // -----------------------------------------------------------------------
    // integer helpers
    // -----------------------------------------------------------------------

    // Integer square root (floor), matching oracle.isqrt semantics.
    private static BigInteger isqrt(BigInteger n) {
        if (n.signum() < 0) throw new ArithmeticException("isqrt of negative");
        return n.sqrt();
    }

    // True if n == a**b for integers a >= 2, b >= 2. Mirrors oracle.is_perfect_power.
    private static boolean isPerfectPower(BigInteger n) {
        if (n.compareTo(FOUR) < 0) return false;
        int bl = n.bitLength();
        for (int b = 2; b <= bl; b++) {
            BigInteger lo = TWO;
            BigInteger hi = ONE.shiftLeft(bl / b + 1);
            while (lo.compareTo(hi) <= 0) {
                BigInteger mid = lo.add(hi).shiftRight(1);
                BigInteger p = mid.pow(b);
                int c = p.compareTo(n);
                if (c == 0) return true;
                if (c < 0) lo = mid.add(ONE);
                else hi = mid.subtract(ONE);
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // primality: Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas)
    // -----------------------------------------------------------------------

    // Strong (Miller-Rabin) probable-prime test of n to base a. Mirrors oracle._mr_strong.
    private static boolean mrStrong(BigInteger n, BigInteger a) {
        if (n.mod(a).signum() == 0) return n.equals(a);
        BigInteger d = n.subtract(ONE);
        int r = 0;
        while (!d.testBit(0)) {
            d = d.shiftRight(1);
            r += 1;
        }
        BigInteger nMinus1 = n.subtract(ONE);
        BigInteger x = a.modPow(d, n);
        if (x.equals(ONE) || x.equals(nMinus1)) return true;
        for (int i = 0; i < r - 1; i++) {
            x = x.multiply(x).mod(n);
            if (x.equals(nMinus1)) return true;
        }
        return false;
    }

    // Jacobi symbol (a/n), n odd positive. Mirrors oracle._jacobi.
    private static int jacobi(BigInteger a, BigInteger n) {
        a = a.mod(n);
        int result = 1;
        while (a.signum() != 0) {
            while (!a.testBit(0)) {
                a = a.shiftRight(1);
                int m8 = n.mod(BigInteger.valueOf(8)).intValue();
                if (m8 == 3 || m8 == 5) result = -result;
            }
            BigInteger tmp = a;
            a = n;
            n = tmp;
            if (a.mod(FOUR).intValue() == 3 && n.mod(FOUR).intValue() == 3) result = -result;
            a = a.mod(n);
        }
        return n.equals(ONE) ? result : 0;
    }

    // Strong Lucas probable-prime test with Selfridge parameters. Mirrors oracle._lucas_strong.
    private static boolean lucasStrong(BigInteger n) {
        // Selfridge D: first term of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1.
        long D = 5, mag = 5;
        while (true) {
            int j = jacobi(BigInteger.valueOf(D), n);
            if (j == -1) break;
            if (j == 0 && BigInteger.valueOf(Math.abs(D)).compareTo(n) != 0) return false;
            mag += 2;
            D = (((mag - 5) / 2) % 2 == 0) ? mag : -mag;
        }
        BigInteger Dbig = BigInteger.valueOf(D);
        BigInteger P = ONE;
        BigInteger Q = ONE.subtract(Dbig).divide(FOUR); // (1 - D) / 4, exact

        // decompose n+1 = d * 2^s with d odd
        BigInteger dd = n.add(ONE);
        int s = 0;
        while (!dd.testBit(0)) {
            dd = dd.shiftRight(1);
            s += 1;
        }

        // U_d, V_d, Q^d mod n via binary expansion of d.
        BigInteger u = ZERO, v = TWO, qk = ONE;
        String bits = dd.toString(2);
        for (int i = 0; i < bits.length(); i++) {
            char bch = bits.charAt(i);
            BigInteger nu2 = u.multiply(v).mod(n);
            BigInteger nv2 = v.multiply(v).subtract(TWO.multiply(qk)).mod(n);
            u = nu2;
            v = nv2;
            qk = qk.multiply(qk).mod(n);
            if (bch == '1') {
                BigInteger nu = P.multiply(u).add(v);
                BigInteger nv = Dbig.multiply(u).add(P.multiply(v));
                if (nu.testBit(0)) nu = nu.add(n);
                if (nv.testBit(0)) nv = nv.add(n);
                u = nu.shiftRight(1).mod(n);
                v = nv.shiftRight(1).mod(n);
                qk = qk.multiply(Q).mod(n);
            }
        }
        // Python's % yields a non-negative result; BigInteger.mod already does.
        if (u.signum() == 0 || v.signum() == 0) return true;
        for (int i = 0; i < s - 1; i++) {
            v = v.multiply(v).subtract(TWO.multiply(qk)).mod(n);
            qk = qk.multiply(qk).mod(n);
            if (v.signum() == 0) return true;
        }
        return false;
    }

    // Baillie-PSW ground-truth primality. Mirrors oracle.is_prime.
    private static boolean isPrime(BigInteger n) {
        if (n.compareTo(TWO) < 0) return false;
        for (int p : SMALL_PRIMES) {
            BigInteger pb = BigInteger.valueOf(p);
            if (n.equals(pb)) return true;
            if (n.mod(pb).signum() == 0) return false;
        }
        if (!mrStrong(n, TWO)) return false;
        if (isPerfectPower(n)) return false;
        return lucasStrong(n);
    }

    // -----------------------------------------------------------------------
    // RSA modulus hygiene detectors
    // -----------------------------------------------------------------------

    // Smallest prime factor of n below `bound`, else null. Mirrors oracle.smallest_factor
    // (trial division; the Go/TS ports also early-out when p*p > n).
    private static BigInteger smallestFactor(BigInteger n, long bound) {
        for (long pl = 2; pl <= bound; pl += (pl == 2 ? 1 : 2)) {
            BigInteger p = BigInteger.valueOf(pl);
            if (p.multiply(p).compareTo(n) > 0) break;
            if (n.mod(p).signum() == 0) return p;
        }
        return null;
    }

    // Fermat factorisation, bounded. True if close factors found within maxSteps.
    // Mirrors oracle.fermat_close_factor (we only need presence, like the Go/TS ports).
    private static boolean fermatClose(BigInteger n, int maxSteps) {
        if (!n.testBit(0)) return true; // even
        BigInteger a = isqrt(n);
        if (a.multiply(a).compareTo(n) < 0) a = a.add(ONE);
        for (int i = 0; i < maxSteps; i++) {
            BigInteger b2 = a.multiply(a).subtract(n);
            if (b2.signum() >= 0) {
                BigInteger b = isqrt(b2);
                if (b.multiply(b).equals(b2)) return true;
            }
            a = a.add(ONE);
        }
        return false;
    }

    private static boolean allowedBits(int bits) {
        return bits == 2048 || bits == 3072 || bits == 4096;
    }

    private static boolean allowedE(long e) {
        return e == 3 || e == 65537;
    }

    // Accept/reject an RSA public key (n, e). Mirrors oracle.rsa_modulus_verdict.
    // Returns a String[]{acceptFlag, reason}.
    private static Object[] rsaVerdict(BigInteger n, long e) {
        if (n.compareTo(THREE) <= 0 || !n.testBit(0)) {
            return new Object[]{false, "modulus_not_odd_or_too_small"};
        }
        if (isPerfectPower(n)) {
            return new Object[]{false, "modulus_perfect_power"};
        }
        if (smallestFactor(n, 1_000_000L) != null) {
            return new Object[]{false, "modulus_small_factor"};
        }
        if (fermatClose(n, 1 << 16)) {
            return new Object[]{false, "modulus_close_primes"};
        }
        if (!allowedBits(n.bitLength())) {
            return new Object[]{false, "modulus_bit_length_not_allowed"};
        }
        if (!allowedE(e)) {
            return new Object[]{false, "public_exponent_not_allowed"};
        }
        if (e % 2 == 0 || e < 3) {
            return new Object[]{false, "public_exponent_invalid"};
        }
        return new Object[]{true, "ok"};
    }

    // -----------------------------------------------------------------------
    // batch common-factor (Mining-your-Ps-and-Qs): a shared prime across a set
    // -----------------------------------------------------------------------

    // For a SET of moduli, per-key verdict = shares a nontrivial common factor
    // with another key in the set. Mirrors oracle.batch_common_factor_verdicts:
    // key i is shared iff there exists j != i with 1 < gcd(n_i, n_j) < n_i.
    private static boolean[] batchCommonFactorVerdicts(BigInteger[] moduli) {
        boolean[] out = new boolean[moduli.length];
        for (int i = 0; i < moduli.length; i++) {
            boolean shared = false;
            for (int j = 0; j < moduli.length; j++) {
                if (i == j) continue;
                BigInteger g = moduli[i].gcd(moduli[j]);
                if (g.compareTo(ONE) > 0 && g.compareTo(moduli[i]) < 0) {
                    shared = true;
                    break;
                }
            }
            out[i] = shared;
        }
        return out;
    }

    // -----------------------------------------------------------------------
    // EC public-key hygiene: on-curve validation for prime-order NIST/SEC curves
    // (P-256, P-384, secp256k1 all have cofactor 1). Curve (p, a, b) values are
    // copied verbatim from oracle.EC_CURVES via new BigInteger(hex, 16).
    // -----------------------------------------------------------------------

    private static final class Curve {
        final BigInteger p, a, b;
        Curve(String p, String a, String b) {
            this.p = new BigInteger(p, 16);
            this.a = new BigInteger(a, 16);
            this.b = new BigInteger(b, 16);
        }
    }

    private static Curve curveFor(String name) {
        switch (name) {
            case "p256":
                return new Curve(
                    "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
                    "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc",
                    "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b");
            case "p384":
                return new Curve(
                    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
                    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc",
                    "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef");
            case "secp256k1":
                return new Curve(
                    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
                    "0",
                    "7");
            default:
                throw new IllegalArgumentException("unknown curve: " + name);
        }
    }

    // Accept/reject an affine EC public point (x, y) on a named prime-order
    // curve. Mirrors oracle.ec_key_verdict. Returns Object[]{validFlag, reason}.
    private static Object[] ecKeyVerdict(String curveName, BigInteger x, BigInteger y) {
        Curve c = curveFor(curveName);
        BigInteger p = c.p, a = c.a, b = c.b;
        if (x.signum() < 0 || x.compareTo(p) >= 0 || y.signum() < 0 || y.compareTo(p) >= 0) {
            return new Object[]{false, "coordinate_out_of_range"};
        }
        // y^2 - (x^3 + a*x + b) mod p; BigInteger.mod is already non-negative.
        BigInteger rhs = x.pow(3).add(a.multiply(x)).add(b);
        BigInteger lhs = y.multiply(y);
        if (lhs.subtract(rhs).mod(p).signum() != 0) {
            return new Object[]{false, "not_on_curve"};
        }
        return new Object[]{true, "ok"};
    }

    // -----------------------------------------------------------------------
    // ROCA (CVE-2017-15361) fingerprint: Infineon RSALib primes p = k*M +
    // (g^a mod M), so n = p*q is congruent to g^(a+b) mod M and n mod each
    // prime factor pf of M lies in the subgroup generated by g. Mirrors
    // oracle.roca_fingerprint_verdict / oracle._roca_subgroup. g and the prime
    // list are read from policy at runtime; no network, deterministic.
    // -----------------------------------------------------------------------

    // The cyclic subgroup {g^j mod pf}. Mirrors oracle._roca_subgroup: seed with
    // 1 % pf, then multiply by g mod pf until a value repeats.
    private static java.util.Set<Long> rocaSubgroup(long g, long pf) {
        java.util.Set<Long> s = new java.util.HashSet<>();
        long x = 1 % pf;
        while (!s.contains(x)) {
            s.add(x);
            x = (x * g) % pf;
        }
        return s;
    }

    // True iff n carries the ROCA fingerprint: n mod pf is a power of g for
    // EVERY pf in the prime list. Mirrors oracle.roca_fingerprint_verdict.
    private static boolean rocaVerdict(BigInteger n, long g, long[] primes) {
        for (long pf : primes) {
            long r = n.mod(BigInteger.valueOf(pf)).longValue();
            if (!rocaSubgroup(g, pf).contains(r)) {
                return false;
            }
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // driver
    // -----------------------------------------------------------------------

    public static void main(String[] args) throws Exception {
        String path = (args.length > 0) ? args[0] : System.getenv("ALGOVOI_KEYHYGIENE");
        if (path == null || path.isEmpty()) {
            System.err.println("no corpus path (arg[0] or ALGOVOI_KEYHYGIENE)");
            System.exit(2);
        }
        String raw = new String(Files.readAllBytes(Paths.get(path)), java.nio.charset.StandardCharsets.UTF_8);
        JSONObject corpus = new JSONObject(raw);

        List<String> failures = new ArrayList<>();

        JSONArray prim = corpus.optJSONArray("primality");
        int primCount = (prim == null) ? 0 : prim.length();
        for (int i = 0; i < primCount; i++) {
            JSONObject c = prim.getJSONObject(i);
            boolean got = isPrime(new BigInteger(c.getString("value")));
            boolean want = c.getBoolean("expect_prime");
            if (got != want) {
                failures.add(String.format("primality[%d] %s: got prime=%b want %b",
                        i, c.optString("note"), got, want));
            }
        }

        JSONArray rsa = corpus.optJSONArray("rsa_modulus_hygiene");
        int rsaCount = (rsa == null) ? 0 : rsa.length();
        for (int i = 0; i < rsaCount; i++) {
            JSONObject c = rsa.getJSONObject(i);
            BigInteger n = new BigInteger(c.getString("n"));
            long e = c.getLong("e");
            Object[] verdict = rsaVerdict(n, e);
            boolean accept = (Boolean) verdict[0];
            String reason = (String) verdict[1];
            boolean wantAccept = c.getBoolean("expect_accept");
            String wantReason = c.getString("reason");
            if (accept != wantAccept || !reason.equals(wantReason)) {
                failures.add(String.format("rsa[%d] %s: got (%b,%s) want (%b,%s)",
                        i, c.optString("note"), accept, reason, wantAccept, wantReason));
            }
        }

        JSONArray batch = corpus.optJSONArray("batch_common_factor");
        int batchCount = (batch == null) ? 0 : batch.length();
        if (batchCount > 0) {
            BigInteger[] moduli = new BigInteger[batchCount];
            for (int i = 0; i < batchCount; i++) {
                moduli[i] = new BigInteger(batch.getJSONObject(i).getString("n"));
            }
            boolean[] verdicts = batchCommonFactorVerdicts(moduli);
            for (int i = 0; i < batchCount; i++) {
                JSONObject c = batch.getJSONObject(i);
                boolean got = verdicts[i];
                boolean want = c.getBoolean("shares_factor");
                if (got != want) {
                    failures.add(String.format("batch_common_factor[%d] %s: got shares=%b want %b",
                            i, c.optString("note"), got, want));
                }
            }
        }

        JSONArray ec = corpus.optJSONArray("ec_key_hygiene");
        int ecCount = (ec == null) ? 0 : ec.length();
        for (int i = 0; i < ecCount; i++) {
            JSONObject c = ec.getJSONObject(i);
            Object[] verdict = ecKeyVerdict(
                    c.getString("curve"),
                    new BigInteger(c.getString("x")),
                    new BigInteger(c.getString("y")));
            boolean valid = (Boolean) verdict[0];
            String reason = (String) verdict[1];
            boolean wantValid = c.getBoolean("expect_valid");
            String wantReason = c.getString("reason");
            if (valid != wantValid || !reason.equals(wantReason)) {
                failures.add(String.format("ec_key_hygiene[%d] %s: got (%b,%s) want (%b,%s)",
                        i, c.optString("note"), valid, reason, wantValid, wantReason));
            }
        }

        JSONObject policy = corpus.optJSONObject("policy");
        long rocaGen = policy.getLong("roca_generator");
        JSONArray rocaPrimeArr = policy.getJSONArray("roca_primes");
        long[] rocaPrimes = new long[rocaPrimeArr.length()];
        for (int i = 0; i < rocaPrimes.length; i++) {
            rocaPrimes[i] = rocaPrimeArr.getLong(i);
        }

        JSONArray roca = corpus.optJSONArray("roca_fingerprint");
        int rocaCount = (roca == null) ? 0 : roca.length();
        for (int i = 0; i < rocaCount; i++) {
            JSONObject c = roca.getJSONObject(i);
            boolean got = rocaVerdict(new BigInteger(c.getString("n")), rocaGen, rocaPrimes);
            boolean want = c.getBoolean("roca_vulnerable");
            if (got != want) {
                failures.add(String.format("roca_fingerprint[%d] %s: got roca=%b want %b",
                        i, c.optString("note"), got, want));
            }
        }

        int total = primCount + rsaCount + batchCount + ecCount + rocaCount;
        if (!failures.isEmpty()) {
            System.out.printf("FAIL: %d/%d cases diverged%n", failures.size(), total);
            int shown = Math.min(failures.size(), 20);
            for (int i = 0; i < shown; i++) {
                System.out.println("  - " + failures.get(i));
            }
            System.exit(1);
        }
        System.out.printf("java: %d/%d cases matched%n", total, total);
        System.exit(0);
    }
}
