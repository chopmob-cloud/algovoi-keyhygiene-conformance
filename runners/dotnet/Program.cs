// .NET reference runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using System.Numerics.BigInteger:
// Baillie-PSW primality (strong Miller-Rabin base 2 + strong Lucas) and the RSA
// hygiene detectors (perfect power, small factor, close primes). Reads the frozen
// corpus and reproduces every verdict byte-for-byte; exits 0 iff all match.
//
// .NET ships no stdlib primality test, so BPSW is implemented here directly,
// mirroring oracle.py's is_prime / _mr_strong / _jacobi / _lucas_strong /
// is_perfect_power and rsa_modulus_verdict.

using System.Numerics;
using System.Text.Json;

namespace Algovoi.KeyHygiene;

internal static class Program
{
    // ---------------------------------------------------------------------
    // integer helpers
    // ---------------------------------------------------------------------

    // Bit length matching Python's int.bit_length() for positive n:
    // floor(log2(n)) + 1, and 0 for n == 0.
    private static int BitLength(BigInteger n)
    {
        if (n.Sign == 0) return 0;
        if (n.Sign < 0) n = -n;
        return (int)n.GetBitLength();
    }

    // Integer square root (floor), portable Newton iteration (mirrors oracle.isqrt).
    private static BigInteger Isqrt(BigInteger n)
    {
        if (n < 0) throw new ArgumentException("isqrt of negative");
        if (n < 2) return n;
        BigInteger x = BigInteger.One << ((BitLength(n) + 1) / 2);
        while (true)
        {
            BigInteger y = (x + n / x) / 2;
            if (y >= x) return x;
            x = y;
        }
    }

    // True if n == a**b for integers a >= 2, b >= 2.
    private static bool IsPerfectPower(BigInteger n)
    {
        if (n < 4) return false;
        int bl = BitLength(n);
        for (int b = 2; b <= bl; b++)
        {
            BigInteger lo = 2;
            BigInteger hi = BigInteger.One << (bl / b + 1);
            while (lo <= hi)
            {
                BigInteger mid = (lo + hi) / 2;
                BigInteger p = BigInteger.Pow(mid, b);
                if (p == n) return true;
                if (p < n) lo = mid + 1;
                else hi = mid - 1;
            }
        }
        return false;
    }

    // ---------------------------------------------------------------------
    // primality: Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas)
    // ---------------------------------------------------------------------

    private static readonly int[] SmallPrimes =
    {
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
        157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
        239, 241, 251,
    };

    // Strong (Miller-Rabin) probable-prime test of n to base a.
    private static bool MrStrong(BigInteger n, BigInteger a)
    {
        if (n % a == 0) return n == a;
        BigInteger d = n - 1;
        int r = 0;
        while ((d & 1) == 0) { d >>= 1; r++; }
        BigInteger x = BigInteger.ModPow(a, d, n);
        if (x == 1 || x == n - 1) return true;
        for (int i = 0; i < r - 1; i++)
        {
            x = (x * x) % n;
            if (x == n - 1) return true;
        }
        return false;
    }

    // Jacobi symbol (a/n), n odd positive.
    private static int Jacobi(BigInteger a, BigInteger n)
    {
        a = ((a % n) + n) % n;
        int result = 1;
        while (a != 0)
        {
            while ((a & 1) == 0)
            {
                a >>= 1;
                BigInteger m8 = n % 8;
                if (m8 == 3 || m8 == 5) result = -result;
            }
            (a, n) = (n, a);
            if (a % 4 == 3 && n % 4 == 3) result = -result;
            a %= n;
        }
        return n == 1 ? result : 0;
    }

    // Strong Lucas probable-prime test with Selfridge parameters.
    private static bool LucasStrong(BigInteger n)
    {
        BigInteger d0 = 5, mag = 5;
        while (true)
        {
            int j = Jacobi(d0, n);
            if (j == -1) break;
            if (j == 0 && BigInteger.Abs(d0) != n) return false; // shares a factor with n
            mag += 2;
            // magnitudes 5,7,9,11,13,... carry signs +,-,+,-,+,...
            d0 = (((mag - 5) / 2) % 2 == 0) ? mag : -mag;
        }
        BigInteger D = d0;
        BigInteger P = 1;
        BigInteger Q = (1 - D) / 4;

        // decompose n+1 = d * 2^s with d odd
        BigInteger d = n + 1;
        int s = 0;
        while ((d & 1) == 0) { d >>= 1; s++; }

        // U_d, V_d, Q^d mod n via binary expansion of d (MSB first)
        BigInteger u = 0, v = 2, qk = 1;
        string bits = ToBinary(d);
        foreach (char c in bits)
        {
            BigInteger nu0 = (u * v) % n;
            BigInteger nv0 = ((v * v - 2 * qk) % n + n) % n;
            u = nu0;
            v = nv0;
            qk = (qk * qk) % n;
            if (c == '1')
            {
                BigInteger nu = P * u + v;
                BigInteger nv = D * u + P * v;
                if ((nu & 1) != 0) nu += n;
                if ((nv & 1) != 0) nv += n;
                u = ((nu / 2) % n + n) % n;
                v = ((nv / 2) % n + n) % n;
                qk = ((qk * Q) % n + n) % n;
            }
        }
        if (u == 0 || v == 0) return true;
        for (int i = 0; i < s - 1; i++)
        {
            v = ((v * v - 2 * qk) % n + n) % n;
            qk = (qk * qk) % n;
            if (v == 0) return true;
        }
        return false;
    }

    // Binary string (MSB first) of a positive BigInteger, mirroring Python bin(k)[2:].
    private static string ToBinary(BigInteger k)
    {
        if (k.Sign == 0) return "0";
        var sb = new System.Text.StringBuilder();
        for (int i = BitLength(k) - 1; i >= 0; i--)
            sb.Append(((k >> i) & 1) == 1 ? '1' : '0');
        return sb.ToString();
    }

    // Baillie-PSW: the ground-truth primality test.
    private static bool IsPrime(BigInteger n)
    {
        if (n < 2) return false;
        foreach (int p in SmallPrimes)
        {
            if (n == p) return true;
            if (n % p == 0) return false;
        }
        if (!MrStrong(n, 2)) return false;
        if (IsPerfectPower(n)) return false;
        return LucasStrong(n);
    }

    // ---------------------------------------------------------------------
    // RSA modulus hygiene detectors
    // ---------------------------------------------------------------------

    private static BigInteger? SmallestFactor(BigInteger n, BigInteger bound)
    {
        for (BigInteger p = 2; p <= bound; p += (p == 2 ? 1 : 2))
        {
            if (p * p > n) break;
            if (n % p == 0) return p;
        }
        return null;
    }

    private static bool FermatClose(BigInteger n, int maxSteps)
    {
        if (n % 2 == 0) return true;
        BigInteger a = Isqrt(n);
        if (a * a < n) a += 1;
        for (int i = 0; i < maxSteps; i++)
        {
            BigInteger b2 = a * a - n;
            if (b2 >= 0)
            {
                BigInteger b = Isqrt(b2);
                if (b * b == b2) return true;
            }
            a += 1;
        }
        return false;
    }

    private static readonly HashSet<int> BrAllowedBits = new() { 2048, 3072, 4096 };
    private static readonly HashSet<int> BrAllowedE = new() { 3, 65537 };

    private static (bool accept, string reason) RsaVerdict(BigInteger n, int e)
    {
        if (n <= 3 || n % 2 == 0) return (false, "modulus_not_odd_or_too_small");
        if (IsPerfectPower(n)) return (false, "modulus_perfect_power");
        if (SmallestFactor(n, 1_000_000) is not null) return (false, "modulus_small_factor");
        if (FermatClose(n, 1 << 16)) return (false, "modulus_close_primes");
        if (!BrAllowedBits.Contains(BitLength(n))) return (false, "modulus_bit_length_not_allowed");
        if (!BrAllowedE.Contains(e)) return (false, "public_exponent_not_allowed");
        if (e % 2 == 0 || e < 3) return (false, "public_exponent_invalid");
        return (true, "ok");
    }

    // ---------------------------------------------------------------------
    // driver
    // ---------------------------------------------------------------------

    private static int Main(string[] args)
    {
        string? path = args.Length > 0 ? args[0] : Environment.GetEnvironmentVariable("ALGOVOI_KEYHYGIENE");
        if (string.IsNullOrEmpty(path))
        {
            Console.Error.WriteLine("no corpus path (arg[0] or ALGOVOI_KEYHYGIENE)");
            return 2;
        }

        JsonDocument doc;
        try
        {
            doc = JsonDocument.Parse(File.ReadAllBytes(path));
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine("cannot read/parse corpus: " + ex.Message);
            return 2;
        }

        var failures = new List<string>();
        JsonElement root = doc.RootElement;

        if (root.TryGetProperty("primality", out JsonElement primality))
        {
            int i = 0;
            foreach (JsonElement c in primality.EnumerateArray())
            {
                string note = c.TryGetProperty("note", out var nt) ? (nt.GetString() ?? "") : "";
                BigInteger value = BigInteger.Parse(c.GetProperty("value").GetString()!);
                bool expect = c.GetProperty("expect_prime").GetBoolean();
                bool got = IsPrime(value);
                if (got != expect)
                    failures.Add($"primality[{i}] {note}: got prime={got} want {expect}");
                i++;
            }
        }

        if (root.TryGetProperty("rsa_modulus_hygiene", out JsonElement rsa))
        {
            int i = 0;
            foreach (JsonElement c in rsa.EnumerateArray())
            {
                string note = c.TryGetProperty("note", out var nt) ? (nt.GetString() ?? "") : "";
                BigInteger n = BigInteger.Parse(c.GetProperty("n").GetString()!);
                int e = c.GetProperty("e").GetInt32();
                bool expectAccept = c.GetProperty("expect_accept").GetBoolean();
                string reason = c.GetProperty("reason").GetString() ?? "";
                var (accept, gotReason) = RsaVerdict(n, e);
                if (accept != expectAccept || gotReason != reason)
                    failures.Add($"rsa[{i}] {note}: got ({accept},{gotReason}) want ({expectAccept},{reason})");
                i++;
            }
        }

        int total = 0;
        if (root.TryGetProperty("primality", out var p2)) total += p2.GetArrayLength();
        if (root.TryGetProperty("rsa_modulus_hygiene", out var r2)) total += r2.GetArrayLength();

        if (failures.Count > 0)
        {
            Console.WriteLine($"FAIL: {failures.Count}/{total} cases diverged");
            foreach (string f in failures.Take(20)) Console.WriteLine("  - " + f);
            return 1;
        }

        Console.WriteLine($"dotnet: {total}/{total} cases matched");
        return 0;
    }
}
