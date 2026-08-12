/* C runner for the keyhygiene battery.
 *
 * Independent port of tools/oracle.py using GMP for big integers and jansson
 * for JSON. It reproduces the reference decision surface exactly:
 *
 *   - primality:  Baillie-PSW (small-prime trial division, strong Miller-Rabin
 *                 base 2, perfect-power rejection, strong Lucas with Selfridge
 *                 parameters). NOT mpz_probab_prime_p, which is a different
 *                 algorithm; the whole point of the battery is a byte-faithful
 *                 BPSW reproduction that agrees with the Go/TS/Python ports.
 *   - RSA hygiene: perfect power, small-factor trial division, bounded Fermat
 *                 close-prime factorisation, bit-length and public-exponent
 *                 policy, in the exact reject-reason order oracle.py uses.
 *
 * Reads the frozen corpus and reproduces every verdict; exits 0 iff all match.
 *
 * Build (in the gcc:14-bookworm cell with libgmp-dev + libjansson-dev):
 *   cc -O2 -w -o v verify.c $(pkg-config --cflags --libs jansson) -lgmp && ./v <corpus_path>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <jansson.h>

/* ------------------------------------------------------------------------- */
/* integer helpers                                                           */
/* ------------------------------------------------------------------------- */

/* first 54 primes (2..251), mirroring oracle._SMALL_PRIMES */
static const unsigned long SMALL_PRIMES[] = {
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251};
static const size_t SMALL_PRIMES_N = sizeof(SMALL_PRIMES) / sizeof(SMALL_PRIMES[0]);

/* True if n == a**b for integers a >= 2, b >= 2. Faithful to
 * oracle.is_perfect_power: a per-exponent binary search, exact integer only. */
static int is_perfect_power(const mpz_t n)
{
    if (mpz_cmp_ui(n, 4) < 0)
        return 0;
    size_t bl = mpz_sizeinbase(n, 2); /* n > 0 => number of bits == bit_length */
    mpz_t lo, hi, mid, p;
    mpz_inits(lo, hi, mid, p, NULL);
    int found = 0;
    for (unsigned long b = 2; b <= bl && !found; b++) {
        mpz_set_ui(lo, 2);
        mpz_set_ui(hi, 1);
        mpz_mul_2exp(hi, hi, (mp_bitcnt_t)(bl / b) + 1); /* hi = 1 << (bl//b + 1) */
        while (mpz_cmp(lo, hi) <= 0) {
            mpz_add(mid, lo, hi);
            mpz_fdiv_q_2exp(mid, mid, 1); /* (lo+hi)//2, both >= 0 */
            mpz_pow_ui(p, mid, b);
            int c = mpz_cmp(p, n);
            if (c == 0) {
                found = 1;
                break;
            } else if (c < 0) {
                mpz_add_ui(lo, mid, 1);
            } else {
                mpz_sub_ui(hi, mid, 1);
            }
        }
    }
    mpz_clears(lo, hi, mid, p, NULL);
    return found;
}

/* Strong (Miller-Rabin) probable-prime test of n to base a. True = probably
 * prime for this base; False = definitely composite. Mirrors oracle._mr_strong. */
static int mr_strong(const mpz_t n, unsigned long a)
{
    /* if n % a == 0: return n == a */
    if (mpz_divisible_ui_p(n, a))
        return mpz_cmp_ui(n, a) == 0;

    mpz_t d, x, nm1, base;
    mpz_inits(d, x, nm1, base, NULL);
    mpz_sub_ui(nm1, n, 1);
    mpz_set(d, nm1);
    unsigned long r = 0;
    while (mpz_even_p(d)) {
        mpz_fdiv_q_2exp(d, d, 1);
        r++;
    }
    mpz_set_ui(base, a);
    mpz_powm(x, base, d, n); /* a^d mod n */

    int result = 0;
    if (mpz_cmp_ui(x, 1) == 0 || mpz_cmp(x, nm1) == 0) {
        result = 1;
    } else {
        for (unsigned long i = 0; i + 1 < r; i++) { /* range(r-1) */
            mpz_mul(x, x, x);
            mpz_mod(x, x, n);
            if (mpz_cmp(x, nm1) == 0) {
                result = 1;
                break;
            }
        }
    }
    mpz_clears(d, x, nm1, base, NULL);
    return result;
}

/* Jacobi symbol (a/n), n odd positive. Faithful to oracle._jacobi (handles a<0
 * via the leading reduction a %= n, giving a value in [0, n)). */
static int jacobi_sym(const mpz_t a_in, const mpz_t n_in)
{
    mpz_t a, n;
    mpz_inits(a, n, NULL);
    mpz_set(n, n_in);
    mpz_mod(a, a_in, n); /* a %= n, result >= 0 */
    int result = 1;
    while (mpz_sgn(a) != 0) {
        while (mpz_even_p(a)) {
            mpz_fdiv_q_2exp(a, a, 1);
            unsigned long m8 = mpz_fdiv_ui(n, 8);
            if (m8 == 3 || m8 == 5)
                result = -result;
        }
        mpz_swap(a, n); /* a, n = n, a */
        if (mpz_fdiv_ui(a, 4) == 3 && mpz_fdiv_ui(n, 4) == 3)
            result = -result;
        mpz_mod(a, a, n);
    }
    int ret = (mpz_cmp_ui(n, 1) == 0) ? result : 0;
    mpz_clears(a, n, NULL);
    return ret;
}

/* Strong Lucas probable-prime test with Selfridge parameters (the Lucas half of
 * Baillie-PSW). Faithful to oracle._lucas_strong. */
static int lucas_strong(const mpz_t n)
{
    /* P is fixed at 1 for Selfridge parameters, so it is folded into the
     * recurrences below rather than kept as a live variable. */
    mpz_t D, absD, Q, d, u, v, qk, nu, nv, t1, t2, tmp;
    mpz_inits(D, absD, Q, d, u, v, qk, nu, nv, t1, t2, tmp, NULL);
    int ret = 0;

    /* Selfridge D: first of 5, -7, 9, -11, 13, ... with Jacobi(D, n) = -1. */
    long mag = 5;
    mpz_set_si(D, 5);
    for (;;) {
        int j = jacobi_sym(D, n);
        if (j == -1)
            break;
        if (j == 0) {
            mpz_abs(absD, D);
            if (mpz_cmp(absD, n) != 0) { /* D shares a factor with n */
                ret = 0;
                goto done;
            }
        }
        mag += 2;
        /* magnitudes 5,7,9,11,13,... carry signs +,-,+,-,+,... */
        if ((((mag - 5) / 2) % 2) == 0)
            mpz_set_si(D, mag);
        else
            mpz_set_si(D, -mag);
    }

    mpz_ui_sub(t1, 1, D);     /* 1 - D */
    mpz_fdiv_q_ui(Q, t1, 4);  /* (1 - D) // 4 (exact; D == 1 mod 4) */

    /* decompose n+1 = d * 2^s with d odd */
    mpz_add_ui(d, n, 1);
    unsigned long s = 0;
    while (mpz_even_p(d)) {
        mpz_fdiv_q_2exp(d, d, 1);
        s++;
    }

    /* U_d, V_d, Q^d mod n via binary expansion of d (MSB -> LSB). P == 1. */
    mpz_set_ui(u, 0);
    mpz_set_ui(v, 2);
    mpz_set_ui(qk, 1);
    size_t nb = mpz_sizeinbase(d, 2);
    for (long i = (long)nb - 1; i >= 0; i--) {
        /* doubling: u, v = (u*v)%n, (v*v - 2*qk)%n ; then qk = (qk*qk)%n */
        mpz_mul(t1, u, v);
        mpz_mod(t1, t1, n);
        mpz_mul(t2, v, v);
        mpz_mul_2exp(tmp, qk, 1); /* 2*qk (old qk) */
        mpz_sub(t2, t2, tmp);
        mpz_mod(t2, t2, n);
        mpz_set(u, t1);
        mpz_set(v, t2);
        mpz_mul(qk, qk, qk);
        mpz_mod(qk, qk, n);
        if (mpz_tstbit(d, (mp_bitcnt_t)i)) {
            /* nu = P*u + v = u + v ; nv = D*u + P*v = D*u + v */
            mpz_add(nu, u, v);
            mpz_mul(nv, D, u);
            mpz_add(nv, nv, v);
            if (mpz_odd_p(nu))
                mpz_add(nu, nu, n);
            if (mpz_odd_p(nv))
                mpz_add(nv, nv, n);
            mpz_fdiv_q_2exp(u, nu, 1); /* nu even => exact half */
            mpz_mod(u, u, n);
            mpz_fdiv_q_2exp(v, nv, 1);
            mpz_mod(v, v, n);
            mpz_mul(qk, qk, Q);
            mpz_mod(qk, qk, n);
        }
    }

    if (mpz_sgn(u) == 0 || mpz_sgn(v) == 0) {
        ret = 1;
        goto done;
    }
    for (unsigned long i = 0; i + 1 < s; i++) { /* range(s-1) */
        mpz_mul(t2, v, v);
        mpz_mul_2exp(tmp, qk, 1);
        mpz_sub(t2, t2, tmp);
        mpz_mod(v, t2, n);
        mpz_mul(qk, qk, qk);
        mpz_mod(qk, qk, n);
        if (mpz_sgn(v) == 0) {
            ret = 1;
            goto done;
        }
    }
    ret = 0;

done:
    mpz_clears(D, absD, Q, d, u, v, qk, nu, nv, t1, t2, tmp, NULL);
    return ret;
}

/* Baillie-PSW: the ground-truth primality test. Faithful to oracle.is_prime. */
static int is_prime(const mpz_t n)
{
    if (mpz_cmp_ui(n, 2) < 0)
        return 0;
    for (size_t i = 0; i < SMALL_PRIMES_N; i++) {
        unsigned long p = SMALL_PRIMES[i];
        if (mpz_cmp_ui(n, p) == 0)
            return 1;
        if (mpz_divisible_ui_p(n, p))
            return 0;
    }
    if (!mr_strong(n, 2))
        return 0;
    if (is_perfect_power(n))
        return 0;
    return lucas_strong(n);
}

/* ------------------------------------------------------------------------- */
/* RSA modulus hygiene detectors                                             */
/* ------------------------------------------------------------------------- */

/* True if n has a prime factor below 1,000,000. Mirrors oracle.smallest_factor
 * (returning only the boolean the verdict needs). Trial division 2, then odd
 * numbers; the smallest divisor found is necessarily prime. */
static int has_small_factor(const mpz_t n)
{
    mpz_t pp;
    mpz_init(pp);
    int found = 0;
    for (unsigned long p = 2; p <= 1000000UL;) {
        mpz_set_ui(pp, p);
        mpz_mul(pp, pp, pp); /* p*p */
        if (mpz_cmp(pp, n) > 0)
            break;
        if (mpz_divisible_ui_p(n, p)) {
            found = 1;
            break;
        }
        p += (p == 2) ? 1 : 2;
    }
    mpz_clear(pp);
    return found;
}

/* True if n factors as two close primes within the bounded Fermat search.
 * Mirrors oracle.fermat_close_factor (returning only the boolean). */
static int fermat_close(const mpz_t n)
{
    if (mpz_even_p(n))
        return 1; /* (2, n/2) */
    mpz_t a, b2, b, sq;
    mpz_inits(a, b2, b, sq, NULL);
    mpz_sqrt(a, n);
    mpz_mul(sq, a, a);
    if (mpz_cmp(sq, n) < 0)
        mpz_add_ui(a, a, 1);
    int found = 0;
    for (unsigned long i = 0; i < (1UL << 16); i++) { /* max_steps = 1 << 16 */
        mpz_mul(b2, a, a);
        mpz_sub(b2, b2, n);
        if (mpz_sgn(b2) >= 0) {
            mpz_sqrt(b, b2);
            mpz_mul(sq, b, b);
            if (mpz_cmp(sq, b2) == 0) {
                found = 1;
                break;
            }
        }
        mpz_add_ui(a, a, 1);
    }
    mpz_clears(a, b2, b, sq, NULL);
    return found;
}

/* Accept/reject an RSA public key (n, e) under the BR-tracking policy. Reject
 * reasons ordered most-structural first, exactly as oracle.rsa_modulus_verdict.
 * Returns 1 (accept) or 0 (reject); *reason points at a static string. */
static int rsa_verdict(const mpz_t n, long e, const char **reason)
{
    if (mpz_cmp_ui(n, 3) <= 0 || mpz_even_p(n)) {
        *reason = "modulus_not_odd_or_too_small";
        return 0;
    }
    if (is_perfect_power(n)) {
        *reason = "modulus_perfect_power";
        return 0;
    }
    if (has_small_factor(n)) {
        *reason = "modulus_small_factor";
        return 0;
    }
    if (fermat_close(n)) {
        *reason = "modulus_close_primes";
        return 0;
    }
    size_t bits = mpz_sizeinbase(n, 2);
    if (!(bits == 2048 || bits == 3072 || bits == 4096)) {
        *reason = "modulus_bit_length_not_allowed";
        return 0;
    }
    if (!(e == 3 || e == 65537)) {
        *reason = "public_exponent_not_allowed";
        return 0;
    }
    if (e % 2 == 0 || e < 3) {
        *reason = "public_exponent_invalid";
        return 0;
    }
    *reason = "ok";
    return 1;
}

/* ------------------------------------------------------------------------- */
/* driver                                                                    */
/* ------------------------------------------------------------------------- */

int main(int argc, char **argv)
{
    const char *path = (argc > 1) ? argv[1] : getenv("ALGOVOI_KEYHYGIENE");
    if (!path || !*path) {
        fprintf(stderr, "usage: %s <corpus_path>  (or set ALGOVOI_KEYHYGIENE)\n", argv[0]);
        return 2;
    }

    json_error_t jerr;
    json_t *root = json_load_file(path, 0, &jerr);
    if (!root) {
        fprintf(stderr, "cannot load corpus: %s (line %d)\n", jerr.text, jerr.line);
        return 2;
    }

    int total = 0, matched = 0;
    size_t i;
    json_t *el;

    json_t *prim = json_object_get(root, "primality");
    json_array_foreach(prim, i, el) {
        const char *value = json_string_value(json_object_get(el, "value"));
        const char *note = json_string_value(json_object_get(el, "note"));
        int expect = json_is_true(json_object_get(el, "expect_prime"));
        mpz_t x;
        mpz_init(x);
        if (mpz_set_str(x, value ? value : "", 10) != 0) {
            fprintf(stderr, "primality[%zu]: bad integer '%s'\n", i, value ? value : "");
            mpz_clear(x);
            json_decref(root);
            return 2;
        }
        int got = is_prime(x) ? 1 : 0;
        mpz_clear(x);
        total++;
        if (got == expect)
            matched++;
        else
            fprintf(stderr, "primality[%zu] %s: got prime=%d want %d\n",
                    i, note ? note : "", got, expect);
    }

    json_t *rsa = json_object_get(root, "rsa_modulus_hygiene");
    json_array_foreach(rsa, i, el) {
        const char *ns = json_string_value(json_object_get(el, "n"));
        const char *note = json_string_value(json_object_get(el, "note"));
        const char *want_reason = json_string_value(json_object_get(el, "reason"));
        long e = (long)json_integer_value(json_object_get(el, "e"));
        int expect_accept = json_is_true(json_object_get(el, "expect_accept"));
        mpz_t n;
        mpz_init(n);
        if (mpz_set_str(n, ns ? ns : "", 10) != 0) {
            fprintf(stderr, "rsa[%zu]: bad integer '%s'\n", i, ns ? ns : "");
            mpz_clear(n);
            json_decref(root);
            return 2;
        }
        const char *reason = "";
        int accept = rsa_verdict(n, e, &reason);
        mpz_clear(n);
        total++;
        if (accept == expect_accept && want_reason && strcmp(reason, want_reason) == 0)
            matched++;
        else
            fprintf(stderr, "rsa[%zu] %s: got (%d,%s) want (%d,%s)\n",
                    i, note ? note : "", accept, reason, expect_accept,
                    want_reason ? want_reason : "");
    }

    json_decref(root);
    printf("c: %d/%d cases matched\n", matched, total);
    return (matched == total) ? 0 : 1;
}
