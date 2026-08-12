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

        int total = primCount + rsaCount;
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
