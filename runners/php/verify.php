<?php
// PHP runner for the keyhygiene battery.
//
// Independent port of tools/oracle.py using the GMP extension for big integers:
// Baillie-PSW primality (strong Miller-Rabin base 2 + strong Lucas, with the
// perfect-power screen between them, exactly as oracle.is_prime) and the RSA
// modulus hygiene detectors (perfect power, small factor, Fermat close-primes).
// Reads the frozen corpus and reproduces every reference verdict; prints
// "php: N/N cases matched" and exits 0 iff all match, else exits 1.
//
// Invocation: php runners/php/verify.php <corpus_path>
//
// GMP is REQUIRED. gmp_prob_prime is deliberately NOT used (it is a different
// algorithm); the BPSW ground truth is implemented here with gmp primitives.

declare(strict_types=1);

if (!extension_loaded('gmp')) {
    fwrite(STDERR, "the GMP extension is required (php -m must list gmp)\n");
    exit(2);
}

// ---------------------------------------------------------------------------
// integer helpers
// ---------------------------------------------------------------------------

// First 54 primes (2..251). Mirrors oracle._SMALL_PRIMES.
const SMALL_PRIMES = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251,
];

/** True bit length of a positive GMP integer (matches Python n.bit_length()). */
function bit_length(GMP $n): int
{
    if (gmp_cmp($n, 0) <= 0) {
        return 0;
    }
    return strlen(gmp_strval($n, 2));
}

/** Integer floor square root. gmp_sqrt is the floor sqrt, matching oracle.isqrt. */
function isqrt(GMP $n): GMP
{
    return gmp_sqrt($n);
}

/** True if n == a**b for integers a >= 2, b >= 2. Mirrors oracle.is_perfect_power. */
function is_perfect_power(GMP $n): bool
{
    if (gmp_cmp($n, 4) < 0) {
        return false;
    }
    $bl = bit_length($n);
    for ($b = 2; $b <= $bl; $b++) {
        $lo = gmp_init(2);
        $hi = gmp_pow(gmp_init(2), intdiv($bl, $b) + 1);
        while (gmp_cmp($lo, $hi) <= 0) {
            $mid = gmp_div_q(gmp_add($lo, $hi), 2); // floor div; both positive
            $p = gmp_pow($mid, $b);
            $c = gmp_cmp($p, $n);
            if ($c === 0) {
                return true;
            }
            if ($c < 0) {
                $lo = gmp_add($mid, 1);
            } else {
                $hi = gmp_sub($mid, 1);
            }
        }
    }
    return false;
}

// ---------------------------------------------------------------------------
// primality: Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas)
// ---------------------------------------------------------------------------

/** Strong (Miller-Rabin) probable-prime test of n to base a. Mirrors oracle._mr_strong. */
function mr_strong(GMP $n, int $a): bool
{
    if (gmp_cmp(gmp_mod($n, $a), 0) === 0) {
        return gmp_cmp($n, $a) === 0;
    }
    $d = gmp_sub($n, 1);
    $r = 0;
    while (gmp_cmp(gmp_mod($d, 2), 0) === 0) {
        $d = gmp_div_q($d, 2);
        $r++;
    }
    $nm1 = gmp_sub($n, 1);
    $x = gmp_powm(gmp_init($a), $d, $n);
    if (gmp_cmp($x, 1) === 0 || gmp_cmp($x, $nm1) === 0) {
        return true;
    }
    for ($i = 0; $i < $r - 1; $i++) {
        $x = gmp_mod(gmp_mul($x, $x), $n);
        if (gmp_cmp($x, $nm1) === 0) {
            return true;
        }
    }
    return false;
}

/**
 * Jacobi symbol (a/n), n odd positive. Mirrors oracle._jacobi exactly. gmp_mod
 * returns a non-negative residue just as Python's % does for positive modulus,
 * so this reproduces the reference for negative a (as arises in the Lucas step).
 */
function jacobi_symbol(GMP $a, GMP $n): int
{
    $a = gmp_mod($a, $n);
    $result = 1;
    while (gmp_cmp($a, 0) !== 0) {
        while (gmp_cmp(gmp_mod($a, 2), 0) === 0) {
            $a = gmp_div_q($a, 2);
            $m8 = gmp_intval(gmp_mod($n, 8));
            if ($m8 === 3 || $m8 === 5) {
                $result = -$result;
            }
        }
        $tmp = $a;
        $a = $n;
        $n = $tmp;
        if (gmp_intval(gmp_mod($a, 4)) === 3 && gmp_intval(gmp_mod($n, 4)) === 3) {
            $result = -$result;
        }
        $a = gmp_mod($a, $n);
    }
    return gmp_cmp($n, 1) === 0 ? $result : 0;
}

/** Strong Lucas probable-prime test with Selfridge parameters. Mirrors oracle._lucas_strong. */
function lucas_strong(GMP $n): bool
{
    // Selfridge D: first term of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1.
    $D = gmp_init(5);
    $mag = 5;
    while (true) {
        $j = jacobi_symbol($D, $n);
        if ($j === -1) {
            break;
        }
        if ($j === 0 && gmp_cmp(gmp_abs($D), $n) !== 0) {
            return false; // D shares a factor with n
        }
        $mag += 2;
        // magnitudes 5,7,9,11,13,... carry signs +,-,+,-,+,...
        $D = (intdiv($mag - 5, 2) % 2 === 0) ? gmp_init($mag) : gmp_init(-$mag);
    }
    $P = gmp_init(1);
    $Q = gmp_div_q(gmp_sub(1, $D), 4); // (1 - D) / 4; exact for Selfridge D

    // decompose n+1 = d * 2^s with d odd
    $d = gmp_add($n, 1);
    $s = 0;
    while (gmp_cmp(gmp_mod($d, 2), 0) === 0) {
        $d = gmp_div_q($d, 2);
        $s++;
    }

    // U_d, V_d, Q^d mod n via binary expansion of d (MSB first)
    $u = gmp_init(0);
    $v = gmp_init(2);
    $qk = gmp_init(1);
    $bits = gmp_strval($d, 2);
    $len = strlen($bits);
    for ($i = 0; $i < $len; $i++) {
        $nu = gmp_mod(gmp_mul($u, $v), $n);
        $nv = gmp_mod(gmp_sub(gmp_mul($v, $v), gmp_mul(2, $qk)), $n);
        $u = $nu;
        $v = $nv;
        $qk = gmp_mod(gmp_mul($qk, $qk), $n);
        if ($bits[$i] === '1') {
            $tu = gmp_add(gmp_mul($P, $u), $v);           // P*u + v
            $tv = gmp_add(gmp_mul($D, $u), gmp_mul($P, $v)); // D*u + P*v
            if (gmp_cmp(gmp_mod($tu, 2), 0) !== 0) {
                $tu = gmp_add($tu, $n);
            }
            if (gmp_cmp(gmp_mod($tv, 2), 0) !== 0) {
                $tv = gmp_add($tv, $n);
            }
            $u = gmp_mod(gmp_div_q($tu, 2), $n);
            $v = gmp_mod(gmp_div_q($tv, 2), $n);
            $qk = gmp_mod(gmp_mul($qk, $Q), $n);
        }
    }

    if (gmp_cmp($u, 0) === 0 || gmp_cmp($v, 0) === 0) {
        return true;
    }
    for ($i = 0; $i < $s - 1; $i++) {
        $v = gmp_mod(gmp_sub(gmp_mul($v, $v), gmp_mul(2, $qk)), $n);
        $qk = gmp_mod(gmp_mul($qk, $qk), $n);
        if (gmp_cmp($v, 0) === 0) {
            return true;
        }
    }
    return false;
}

/** Baillie-PSW: the ground-truth primality test. Mirrors oracle.is_prime. */
function is_prime(GMP $n): bool
{
    if (gmp_cmp($n, 2) < 0) {
        return false;
    }
    foreach (SMALL_PRIMES as $p) {
        if (gmp_cmp($n, $p) === 0) {
            return true;
        }
        if (gmp_cmp(gmp_mod($n, $p), 0) === 0) {
            return false;
        }
    }
    if (!mr_strong($n, 2)) {
        return false;
    }
    if (is_perfect_power($n)) {
        return false;
    }
    return lucas_strong($n);
}

// ---------------------------------------------------------------------------
// RSA modulus hygiene detectors
// ---------------------------------------------------------------------------

/** True if n has a prime factor below `bound` (default 1_000_000). Mirrors oracle.smallest_factor. */
function has_small_factor(GMP $n, int $bound = 1000000): bool
{
    for ($p = 2; $p <= $bound; $p += ($p === 2 ? 1 : 2)) {
        if (gmp_cmp(gmp_mul($p, $p), $n) > 0) {
            break;
        }
        if (gmp_cmp(gmp_mod($n, $p), 0) === 0) {
            return true;
        }
    }
    return false;
}

/** Bounded Fermat factorisation; true if close primes are found. Mirrors oracle.fermat_close_factor. */
function fermat_close(GMP $n, int $maxSteps = 65536): bool
{
    if (gmp_cmp(gmp_mod($n, 2), 0) === 0) {
        return true; // (2, n/2)
    }
    $a = isqrt($n);
    if (gmp_cmp(gmp_mul($a, $a), $n) < 0) {
        $a = gmp_add($a, 1);
    }
    for ($i = 0; $i < $maxSteps; $i++) {
        $b2 = gmp_sub(gmp_mul($a, $a), $n);
        if (gmp_cmp($b2, 0) >= 0) {
            $b = isqrt($b2);
            if (gmp_cmp(gmp_mul($b, $b), $b2) === 0) {
                return true;
            }
        }
        $a = gmp_add($a, 1);
    }
    return false;
}

const BR_ALLOWED_BITS = [2048, 3072, 4096];
const BR_ALLOWED_E = [3, 65537];

/**
 * Accept/reject an RSA public key (n, e). Mirrors oracle.rsa_modulus_verdict.
 * Reject reasons are ordered most-structural first. Returns [accept, reason].
 */
function rsa_modulus_verdict(GMP $n, int $e): array
{
    if (gmp_cmp($n, 3) <= 0 || gmp_cmp(gmp_mod($n, 2), 0) === 0) {
        return [false, 'modulus_not_odd_or_too_small'];
    }
    if (is_perfect_power($n)) {
        return [false, 'modulus_perfect_power'];
    }
    if (has_small_factor($n)) {
        return [false, 'modulus_small_factor'];
    }
    if (fermat_close($n)) {
        return [false, 'modulus_close_primes'];
    }
    if (!in_array(bit_length($n), BR_ALLOWED_BITS, true)) {
        return [false, 'modulus_bit_length_not_allowed'];
    }
    if (!in_array($e, BR_ALLOWED_E, true)) {
        return [false, 'public_exponent_not_allowed'];
    }
    if ($e % 2 === 0 || $e < 3) {
        return [false, 'public_exponent_invalid'];
    }
    return [true, 'ok'];
}

// ---------------------------------------------------------------------------
// batch common-factor (Mining-your-Ps-and-Qs): a shared prime across a key set
// ---------------------------------------------------------------------------

/**
 * For a SET of RSA moduli, per-key verdict = shares a prime with another key in
 * the set (a nontrivial common GCD). Mirrors oracle.batch_common_factor_verdicts:
 * verdict[i] is true iff there exists j != i with 1 < gcd(n_i, n_j) < n_i.
 * Returns an array of bool aligned to the input order.
 *
 * @param GMP[] $moduli
 * @return bool[]
 */
function batch_common_factor_verdicts(array $moduli): array
{
    $out = [];
    $count = count($moduli);
    for ($i = 0; $i < $count; $i++) {
        $ni = $moduli[$i];
        $shared = false;
        for ($j = 0; $j < $count; $j++) {
            if ($i === $j) {
                continue;
            }
            $g = gmp_gcd($ni, $moduli[$j]);
            if (gmp_cmp($g, 1) > 0 && gmp_cmp($g, $ni) < 0) {
                $shared = true;
                break;
            }
        }
        $out[] = $shared;
    }
    return $out;
}

// ---------------------------------------------------------------------------
// EC public-key hygiene: on-curve validation for the prime-order NIST/SEC curves
// (P-256, P-384, secp256k1 all have cofactor 1, so on-curve + in-range is
// sufficient). Curve (p, a, b) parameters are copied verbatim from
// oracle.EC_CURVES (p256/p384: a = p-3; secp256k1: a = 0, b = 7).
// ---------------------------------------------------------------------------

/** Named prime-order curves: p, a, b exactly as oracle.EC_CURVES. */
function ec_curves(): array
{
    static $curves = null;
    if ($curves === null) {
        $curves = [
            'p256' => [
                'p' => gmp_init('0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff', 16),
                'a' => gmp_init('0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc', 16),
                'b' => gmp_init('0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b', 16),
            ],
            'p384' => [
                'p' => gmp_init('0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff', 16),
                'a' => gmp_init('0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc', 16),
                'b' => gmp_init('0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef', 16),
            ],
            'secp256k1' => [
                'p' => gmp_init('0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16),
                'a' => gmp_init(0),
                'b' => gmp_init(7),
            ],
        ];
    }
    return $curves;
}

/**
 * Accept/reject an affine EC public point (x, y) on a named prime-order curve.
 * Mirrors oracle.ec_key_verdict: reject out-of-range coordinates and off-curve
 * points. gmp_mod returns a non-negative residue, matching Python's %.
 * Returns [valid, reason].
 */
function ec_key_verdict(string $curve, GMP $x, GMP $y): array
{
    $c = ec_curves()[$curve];
    $p = $c['p'];
    $a = $c['a'];
    $b = $c['b'];
    if (gmp_cmp($x, 0) < 0 || gmp_cmp($x, $p) >= 0 || gmp_cmp($y, 0) < 0 || gmp_cmp($y, $p) >= 0) {
        return [false, 'coordinate_out_of_range'];
    }
    // y^2 - (x^3 + a*x + b) mod p
    $lhs = gmp_mul($y, $y);
    $rhs = gmp_add(gmp_add(gmp_pow($x, 3), gmp_mul($a, $x)), $b);
    if (gmp_cmp(gmp_mod(gmp_sub($lhs, $rhs), $p), 0) !== 0) {
        return [false, 'not_on_curve'];
    }
    return [true, 'ok'];
}

// ---------------------------------------------------------------------------
// driver
// ---------------------------------------------------------------------------

function main(array $argv): int
{
    $path = $argv[1] ?? getenv('ALGOVOI_KEYHYGIENE');
    if (!$path) {
        fwrite(STDERR, "usage: php verify.php <corpus_path>\n");
        return 2;
    }
    $raw = @file_get_contents($path);
    if ($raw === false) {
        fwrite(STDERR, "cannot read corpus: $path\n");
        return 2;
    }
    $corpus = json_decode($raw, true);
    if (!is_array($corpus)) {
        fwrite(STDERR, "cannot parse corpus JSON\n");
        return 2;
    }

    $failures = [];

    $primality = $corpus['primality'] ?? [];
    foreach ($primality as $i => $c) {
        $got = is_prime(gmp_init((string) $c['value'], 10));
        if ($got !== (bool) $c['expect_prime']) {
            $failures[] = sprintf(
                "primality[%d] %s: got prime=%s want %s",
                $i,
                $c['note'] ?? '',
                $got ? 'true' : 'false',
                $c['expect_prime'] ? 'true' : 'false'
            );
        }
    }

    $rsa = $corpus['rsa_modulus_hygiene'] ?? [];
    foreach ($rsa as $i => $c) {
        [$accept, $reason] = rsa_modulus_verdict(gmp_init((string) $c['n'], 10), (int) $c['e']);
        if ($accept !== (bool) $c['expect_accept'] || $reason !== $c['reason']) {
            $failures[] = sprintf(
                "rsa[%d] %s: got (%s,%s) want (%s,%s)",
                $i,
                $c['note'] ?? '',
                $accept ? 'true' : 'false',
                $reason,
                $c['expect_accept'] ? 'true' : 'false',
                $c['reason']
            );
        }
    }

    $batch = $corpus['batch_common_factor'] ?? [];
    if (count($batch) > 0) {
        $moduli = [];
        foreach ($batch as $c) {
            $moduli[] = gmp_init((string) $c['n'], 10);
        }
        $verdicts = batch_common_factor_verdicts($moduli);
        foreach ($batch as $i => $c) {
            if ($verdicts[$i] !== (bool) $c['shares_factor']) {
                $failures[] = sprintf(
                    "batch_common_factor[%d] %s: got shares=%s want %s",
                    $i,
                    $c['note'] ?? '',
                    $verdicts[$i] ? 'true' : 'false',
                    $c['shares_factor'] ? 'true' : 'false'
                );
            }
        }
    }

    $ec = $corpus['ec_key_hygiene'] ?? [];
    foreach ($ec as $i => $c) {
        [$valid, $reason] = ec_key_verdict(
            (string) $c['curve'],
            gmp_init((string) $c['x'], 10),
            gmp_init((string) $c['y'], 10)
        );
        if ($valid !== (bool) $c['expect_valid'] || $reason !== $c['reason']) {
            $failures[] = sprintf(
                "ec_key_hygiene[%d] %s: got (%s,%s) want (%s,%s)",
                $i,
                $c['note'] ?? '',
                $valid ? 'true' : 'false',
                $reason,
                $c['expect_valid'] ? 'true' : 'false',
                $c['reason']
            );
        }
    }

    $total = count($primality) + count($rsa) + count($batch) + count($ec);
    if (count($failures) > 0) {
        printf("FAIL: %d/%d cases diverged\n", count($failures), $total);
        foreach (array_slice($failures, 0, 20) as $f) {
            echo "  - $f\n";
        }
        return 1;
    }
    printf("php: %d/%d cases matched\n", $total, $total);
    return 0;
}

exit(main($argv));
