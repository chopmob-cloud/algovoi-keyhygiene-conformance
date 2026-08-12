# Elixir runner for the keyhygiene battery.
#
# Standalone script (no mix, no deps): run as `elixir verify.exs <corpus.json>`.
# Independent port of tools/oracle.py, mirroring the validated Go and TypeScript
# runners. Reproduces every verdict byte-for-byte:
#
#   - primality: Baillie-PSW (small-prime trial + strong Miller-Rabin base 2 +
#                perfect-power reject + strong Lucas with Selfridge parameters).
#   - RSA hygiene: ordered structural detectors (perfect power, small factor,
#                Fermat close primes) then bit-length / public-exponent policy.
#
# Elixir integers are arbitrary precision natively, so all big-integer math is
# pure integer arithmetic. The target runtime (Elixir 1.16 / OTP 26) ships no
# JSON module and no Jason dependency, so the corpus is read by a small
# hand-rolled recursive-descent JSON parser (module J) built on binary pattern
# matching. Decimal integer strings up to ~1300 digits parse with
# String.to_integer/1.

# ---------------------------------------------------------------------------
# Minimal JSON reader: a recursive-descent parser over the raw binary. It
# returns Elixir maps (string keys) / lists / binaries / integers / floats /
# booleans / nil, so downstream code just does Map.get on the decoded tree.
# Each parse function returns {value, rest_binary}; whitespace is skipped
# before every value and between structural tokens.
# ---------------------------------------------------------------------------
defmodule J do
  def decode(bin) do
    {val, _rest} = value(bin)
    val
  end

  defp skip_ws(<<c, rest::binary>>) when c in [?\s, ?\t, ?\n, ?\r], do: skip_ws(rest)
  defp skip_ws(bin), do: bin

  defp value(bin) do
    case skip_ws(bin) do
      <<?{, rest::binary>> -> object(skip_ws(rest), %{})
      <<?[, rest::binary>> -> array(skip_ws(rest), [])
      <<?", rest::binary>> -> string(rest, [])
      <<"true", rest::binary>> -> {true, rest}
      <<"false", rest::binary>> -> {false, rest}
      <<"null", rest::binary>> -> {nil, rest}
      other -> number(other)
    end
  end

  # object: `bin` is already whitespace-skipped and positioned at `}` or a key.
  defp object(<<?}, rest::binary>>, acc), do: {acc, rest}

  defp object(<<?", rest::binary>>, acc) do
    {key, r1} = string(rest, [])
    <<?:, r2::binary>> = skip_ws(r1)
    {val, r3} = value(r2)
    acc = Map.put(acc, key, val)

    case skip_ws(r3) do
      <<?,, r4::binary>> -> object(skip_ws(r4), acc)
      <<?}, r4::binary>> -> {acc, r4}
    end
  end

  # array: `bin` is already whitespace-skipped and positioned at `]` or a value.
  defp array(<<?], rest::binary>>, acc), do: {Enum.reverse(acc), rest}

  defp array(bin, acc) do
    {val, r1} = value(bin)
    acc = [val | acc]

    case skip_ws(r1) do
      <<?,, r2::binary>> -> array(skip_ws(r2), acc)
      <<?], r2::binary>> -> {Enum.reverse(acc), r2}
    end
  end

  # string: `bin` is positioned just after the opening quote; `acc` is a reverse
  # list of byte/binary chunks assembled into the final binary at the close quote.
  defp string(<<?", rest::binary>>, acc), do: {acc |> Enum.reverse() |> IO.iodata_to_binary(), rest}
  defp string(<<?\\, ?", rest::binary>>, acc), do: string(rest, [?" | acc])
  defp string(<<?\\, ?\\, rest::binary>>, acc), do: string(rest, [?\\ | acc])
  defp string(<<?\\, ?/, rest::binary>>, acc), do: string(rest, [?/ | acc])
  defp string(<<?\\, ?n, rest::binary>>, acc), do: string(rest, [?\n | acc])
  defp string(<<?\\, ?t, rest::binary>>, acc), do: string(rest, [?\t | acc])
  defp string(<<?\\, ?r, rest::binary>>, acc), do: string(rest, [?\r | acc])
  defp string(<<?\\, ?b, rest::binary>>, acc), do: string(rest, [?\b | acc])
  defp string(<<?\\, ?f, rest::binary>>, acc), do: string(rest, [?\f | acc])

  defp string(<<?\\, ?u, hex::binary-size(4), rest::binary>>, acc) do
    cp = String.to_integer(hex, 16)
    string(rest, [<<cp::utf8>> | acc])
  end

  defp string(<<c, rest::binary>>, acc), do: string(rest, [c | acc])

  # number: consume the numeric run, then classify as float (has . / e / E) or
  # integer. Only integer JSON numbers are consumed by callers here, but floats
  # are handled for completeness/robustness.
  defp number(bin) do
    {chars, rest} = number_chars(bin, [])
    s = chars |> Enum.reverse() |> IO.iodata_to_binary()

    val =
      if String.contains?(s, ".") or String.contains?(s, "e") or String.contains?(s, "E") do
        String.to_float(s)
      else
        String.to_integer(s)
      end

    {val, rest}
  end

  defp number_chars(<<c, rest::binary>>, acc)
       when c in ?0..?9 or c in [?-, ?+, ?., ?e, ?E],
       do: number_chars(rest, [c | acc])

  defp number_chars(bin, acc), do: {acc, bin}
end

# ---------------------------------------------------------------------------
# Decision surface: pure-integer reimplementation of tools/oracle.py.
# ---------------------------------------------------------------------------
defmodule KH do
  @small_primes [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251
  ]

  @allowed_bits [2048, 3072, 4096]
  @allowed_e [3, 65537]

  # --- integer helpers ----------------------------------------------------

  # Non-negative modulo (Python `%` semantics for positive modulus).
  defp pmod(a, n) do
    r = rem(a, n)
    if r < 0, do: r + n, else: r
  end

  # bit_length: Integer has no bit_length/1, so derive it from the base-2 string.
  defp bit_length(0), do: 0
  defp bit_length(n) when n > 0, do: n |> Integer.to_string(2) |> String.length()

  # Modular exponentiation via right-to-left binary method.
  defp powmod(base, exp, mod), do: do_powmod(pmod(base, mod), exp, mod, 1)
  defp do_powmod(_b, 0, _mod, acc), do: acc

  defp do_powmod(b, exp, mod, acc) do
    acc = if rem(exp, 2) == 1, do: rem(acc * b, mod), else: acc
    do_powmod(rem(b * b, mod), div(exp, 2), mod, acc)
  end

  # Integer square root (floor) via Newton iteration.
  defp isqrt(n) when n < 2, do: n

  defp isqrt(n) do
    x = Integer.pow(2, div(bit_length(n) + 1, 2))
    isqrt_iter(n, x)
  end

  defp isqrt_iter(n, x) do
    y = div(x + div(n, x), 2)
    if y >= x, do: x, else: isqrt_iter(n, y)
  end

  # Split m = d * 2^r with d odd; returns {d, r}.
  defp factor_twos(d, r) do
    if rem(d, 2) == 0, do: factor_twos(div(d, 2), r + 1), else: {d, r}
  end

  # --- perfect power ------------------------------------------------------

  def perfect_power?(n) when n < 4, do: false

  def perfect_power?(n) do
    bl = bit_length(n)
    Enum.any?(2..bl, fn b -> pp_search(n, b, 2, Integer.pow(2, div(bl, b) + 1)) end)
  end

  defp pp_search(_n, _b, lo, hi) when lo > hi, do: false

  defp pp_search(n, b, lo, hi) do
    mid = div(lo + hi, 2)
    p = Integer.pow(mid, b)

    cond do
      p == n -> true
      p < n -> pp_search(n, b, mid + 1, hi)
      true -> pp_search(n, b, lo, mid - 1)
    end
  end

  # --- strong Miller-Rabin ------------------------------------------------

  defp mr_strong(n, a) do
    if rem(n, a) == 0 do
      n == a
    else
      {d, r} = factor_twos(n - 1, 0)
      x = powmod(a, d, n)

      if x == 1 or x == n - 1 do
        true
      else
        mr_loop(x, n, r - 1)
      end
    end
  end

  defp mr_loop(_x, _n, count) when count <= 0, do: false

  defp mr_loop(x, n, count) do
    x2 = rem(x * x, n)
    if x2 == n - 1, do: true, else: mr_loop(x2, n, count - 1)
  end

  # --- Jacobi symbol ------------------------------------------------------

  defp jacobi(a, n), do: jacobi_loop(pmod(a, n), n, 1)

  defp jacobi_loop(0, n, result), do: if(n == 1, do: result, else: 0)

  defp jacobi_loop(a, n, result) do
    {a, result} = jacobi_twos(a, n, result)
    # swap (a, n) = (n, a)
    a2 = n
    n2 = a
    result = if rem(a2, 4) == 3 and rem(n2, 4) == 3, do: -result, else: result
    jacobi_loop(rem(a2, n2), n2, result)
  end

  defp jacobi_twos(a, n, result) do
    if rem(a, 2) == 0 do
      r8 = rem(n, 8)
      result = if r8 == 3 or r8 == 5, do: -result, else: result
      jacobi_twos(div(a, 2), n, result)
    else
      {a, result}
    end
  end

  # --- strong Lucas (Selfridge parameters) --------------------------------

  defp lucas_strong(n) do
    case select_d(n, 5, 5) do
      :composite ->
        false

      d ->
        p = 1
        q = div(1 - d, 4)
        {dd, s} = factor_twos(n + 1, 0)
        {u, v, qk} = lucas_uv(dd, n, p, q, d)

        if u == 0 or v == 0 do
          true
        else
          lucas_v_loop(v, qk, n, s - 1)
        end
    end
  end

  # First term of 5,-7,9,-11,13,... with Jacobi(D, n) = -1. Jacobi 0 with
  # |D| != n means D shares a factor with n, so n is composite.
  defp select_d(n, d, mag) do
    case jacobi(d, n) do
      -1 ->
        d

      0 ->
        if abs(d) != n, do: :composite, else: next_d(n, mag)

      _ ->
        next_d(n, mag)
    end
  end

  defp next_d(n, mag) do
    mag2 = mag + 2
    d2 = if rem(div(mag2 - 5, 2), 2) == 0, do: mag2, else: -mag2
    select_d(n, d2, mag2)
  end

  # U_k, V_k, Q^k mod n via binary expansion of k (P = 1).
  defp lucas_uv(k, n, p, q, d) do
    bits = k |> Integer.to_string(2) |> String.to_charlist()

    Enum.reduce(bits, {0, 2, 1}, fn bit, {u, v, qk} ->
      u1 = rem(u * v, n)
      v1 = pmod(v * v - 2 * qk, n)
      qk1 = rem(qk * qk, n)

      if bit == ?1 do
        nu = p * u1 + v1
        nv = d * u1 + p * v1
        nu = if rem(nu, 2) != 0, do: nu + n, else: nu
        nv = if rem(nv, 2) != 0, do: nv + n, else: nv
        {pmod(div(nu, 2), n), pmod(div(nv, 2), n), pmod(qk1 * q, n)}
      else
        {u1, v1, qk1}
      end
    end)
  end

  defp lucas_v_loop(_v, _qk, _n, count) when count <= 0, do: false

  defp lucas_v_loop(v, qk, n, count) do
    v2 = pmod(v * v - 2 * qk, n)
    qk2 = rem(qk * qk, n)
    if v2 == 0, do: true, else: lucas_v_loop(v2, qk2, n, count - 1)
  end

  # --- Baillie-PSW --------------------------------------------------------

  def prime?(n) when n < 2, do: false

  def prime?(n) do
    case small_prime_decision(n, @small_primes) do
      {:decided, result} ->
        result

      :continue ->
        cond do
          not mr_strong(n, 2) -> false
          perfect_power?(n) -> false
          true -> lucas_strong(n)
        end
    end
  end

  defp small_prime_decision(_n, []), do: :continue

  defp small_prime_decision(n, [p | rest]) do
    cond do
      n == p -> {:decided, true}
      rem(n, p) == 0 -> {:decided, false}
      true -> small_prime_decision(n, rest)
    end
  end

  # --- RSA hygiene detectors ----------------------------------------------

  # Smallest divisor of n at or below `bound` (2 then odd candidates); nil if
  # none. Any smallest divisor > 1 is prime, matching oracle's prime sieve.
  defp smallest_factor(n, bound), do: sf_loop(n, 2, bound)

  defp sf_loop(n, p, bound) do
    cond do
      p > bound -> nil
      p * p > n -> nil
      rem(n, p) == 0 -> p
      p == 2 -> sf_loop(n, 3, bound)
      true -> sf_loop(n, p + 2, bound)
    end
  end

  # Bounded Fermat factorisation: true if a close-prime factorisation is found
  # within max_steps (the RNG-bug / weak-keygen class).
  defp fermat_close?(n, _max_steps) when rem(n, 2) == 0, do: true

  defp fermat_close?(n, max_steps) do
    a0 = isqrt(n)
    a = if a0 * a0 < n, do: a0 + 1, else: a0
    fermat_loop(n, a, max_steps)
  end

  defp fermat_loop(_n, _a, 0), do: false

  defp fermat_loop(n, a, steps) do
    b2 = a * a - n

    found =
      if b2 >= 0 do
        b = isqrt(b2)
        b * b == b2
      else
        false
      end

    if found, do: true, else: fermat_loop(n, a + 1, steps - 1)
  end

  # Ordered accept/reject verdict, most-structural reason first.
  def rsa_verdict(n, e) do
    cond do
      n <= 3 or rem(n, 2) == 0 -> {false, "modulus_not_odd_or_too_small"}
      perfect_power?(n) -> {false, "modulus_perfect_power"}
      smallest_factor(n, 1_000_000) != nil -> {false, "modulus_small_factor"}
      fermat_close?(n, 65536) -> {false, "modulus_close_primes"}
      bit_length(n) not in @allowed_bits -> {false, "modulus_bit_length_not_allowed"}
      e not in @allowed_e -> {false, "public_exponent_not_allowed"}
      rem(e, 2) == 0 or e < 3 -> {false, "public_exponent_invalid"}
      true -> {true, "ok"}
    end
  end

  # --- batch common-factor (Mining-your-Ps-and-Qs) ------------------------

  # Per-key verdict for a SET of RSA moduli: True iff the key shares a nontrivial
  # prime with another key in the set (a common GCD strictly between 1 and n_i).
  # Such a key is trivially factorable by anyone holding the set. O(n^2) over the
  # (small) set; Integer.gcd/2 is native arbitrary precision.
  def batch_common_factor_verdicts(moduli) do
    indexed = Enum.with_index(moduli)

    Enum.map(indexed, fn {ni, i} ->
      Enum.any?(indexed, fn {nj, j} ->
        if i == j do
          false
        else
          g = Integer.gcd(ni, nj)
          1 < g and g < ni
        end
      end)
    end)
  end

  # --- EC public-key hygiene ----------------------------------------------

  # Curve parameters {p, a, b}, copied byte-for-byte from oracle.EC_CURVES.
  # P-256 and P-384 use a = p - 3; secp256k1 uses a = 0, b = 7. All three are
  # prime-order (cofactor 1), so in-range + on-curve is sufficient.
  defp ec_curve("p256"),
    do:
      {0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
       0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc,
       0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b}

  defp ec_curve("p384"),
    do:
      {0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff,
       0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc,
       0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef}

  defp ec_curve("secp256k1"),
    do: {0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f, 0, 7}

  # Accept/reject an affine EC public point (x, y) on a named prime-order curve.
  # Reject out-of-range coordinates, then off-curve points. pmod/2 normalises the
  # (possibly negative) Elixir remainder to Python `%` semantics before the zero
  # test.
  def ec_verdict(curve, x, y) do
    {p, a, b} = ec_curve(curve)

    cond do
      x < 0 or x >= p or y < 0 or y >= p -> {false, "coordinate_out_of_range"}
      pmod(y * y - (x * x * x + a * x + b), p) != 0 -> {false, "not_on_curve"}
      true -> {true, "ok"}
    end
  end

  # --- ROCA fingerprint (CVE-2017-15361) ----------------------------------

  # The cyclic subgroup {g^j mod pf} (all powers of the generator g modulo the
  # prime pf), returned as a MapSet. Start at x = 1 and multiply by g until the
  # sequence repeats. pf is an odd prime and g is positive, so rem/2 is already
  # non-negative and no pmod normalisation is needed.
  defp roca_subgroup(g, pf), do: roca_subgroup(g, pf, MapSet.new(), rem(1, pf))

  defp roca_subgroup(g, pf, set, x) do
    if MapSet.member?(set, x) do
      set
    else
      roca_subgroup(g, pf, MapSet.put(set, x), rem(x * g, pf))
    end
  end

  # True iff n carries the ROCA fingerprint: n mod pf is a power of the generator
  # g for EVERY pf in `primes`. Infineon RSALib primes are p = k*M + (g^a mod M),
  # so n = p*q is congruent to g^(a+b) mod M and thus n mod each pf | M lands in
  # the subgroup generated by g. A random modulus meets all of them only with
  # negligible probability. Deterministic; mirrors oracle.roca_fingerprint_verdict.
  def roca_verdict(n, g, primes) do
    Enum.all?(primes, fn pf ->
      MapSet.member?(roca_subgroup(g, pf), rem(n, pf))
    end)
  end
end

# ---------------------------------------------------------------------------
# main: read corpus, reproduce every verdict, report, and set the exit code.
# ---------------------------------------------------------------------------
path =
  case System.argv() do
    [p | _] -> p
    [] -> System.get_env("ALGOVOI_KEYHYGIENE")
  end

corpus =
  path
  |> File.read!()
  |> J.decode()

primality = Map.get(corpus, "primality", [])
rsa = Map.get(corpus, "rsa_modulus_hygiene", [])
batch = Map.get(corpus, "batch_common_factor", [])
ec = Map.get(corpus, "ec_key_hygiene", [])
roca = Map.get(corpus, "roca_fingerprint", [])

# ROCA parameters live in the corpus policy block: the generator (65537) and the
# prime factors of M, both already decoded as native integers by J.decode/1.
policy = Map.get(corpus, "policy", %{})
roca_generator = Map.get(policy, "roca_generator")
roca_primes = Map.get(policy, "roca_primes")

prime_failures =
  primality
  |> Enum.with_index()
  |> Enum.flat_map(fn {c, i} ->
    got = KH.prime?(String.to_integer(Map.fetch!(c, "value")))
    want = Map.fetch!(c, "expect_prime")

    if got == want do
      []
    else
      note = Map.get(c, "note", "")
      ["primality[#{i}] #{note}: got prime=#{got} want #{want}"]
    end
  end)

rsa_failures =
  rsa
  |> Enum.with_index()
  |> Enum.flat_map(fn {c, i} ->
    n = String.to_integer(Map.fetch!(c, "n"))
    e = Map.fetch!(c, "e")
    {accept, reason} = KH.rsa_verdict(n, e)
    want_accept = Map.fetch!(c, "expect_accept")
    want_reason = Map.fetch!(c, "reason")

    if accept == want_accept and reason == want_reason do
      []
    else
      note = Map.get(c, "note", "")
      ["rsa[#{i}] #{note}: got (#{accept},#{reason}) want (#{want_accept},#{want_reason})"]
    end
  end)

# batch_common_factor: read the whole set of moduli, then compare each key's
# shared-factor verdict to its frozen expectation.
batch_failures =
  case batch do
    [] ->
      []

    _ ->
      moduli = Enum.map(batch, fn c -> String.to_integer(Map.fetch!(c, "n")) end)
      verdicts = KH.batch_common_factor_verdicts(moduli)

      batch
      |> Enum.zip(verdicts)
      |> Enum.with_index()
      |> Enum.flat_map(fn {{c, got}, i} ->
        want = Map.fetch!(c, "shares_factor")

        if got == want do
          []
        else
          note = Map.get(c, "note", "")
          ["batch_common_factor[#{i}] #{note}: got shares=#{got} want #{want}"]
        end
      end)
  end

ec_failures =
  ec
  |> Enum.with_index()
  |> Enum.flat_map(fn {c, i} ->
    curve = Map.fetch!(c, "curve")
    x = String.to_integer(Map.fetch!(c, "x"))
    y = String.to_integer(Map.fetch!(c, "y"))
    {valid, reason} = KH.ec_verdict(curve, x, y)
    want_valid = Map.fetch!(c, "expect_valid")
    want_reason = Map.fetch!(c, "reason")

    if valid == want_valid and reason == want_reason do
      []
    else
      note = Map.get(c, "note", "")
      ["ec_key_hygiene[#{i}] #{note}: got (#{valid},#{reason}) want (#{want_valid},#{want_reason})"]
    end
  end)

roca_failures =
  roca
  |> Enum.with_index()
  |> Enum.flat_map(fn {c, i} ->
    n = String.to_integer(Map.fetch!(c, "n"))
    got = KH.roca_verdict(n, roca_generator, roca_primes)
    want = Map.fetch!(c, "roca_vulnerable")

    if got == want do
      []
    else
      note = Map.get(c, "note", "")
      ["roca_fingerprint[#{i}] #{note}: got roca=#{got} want #{want}"]
    end
  end)

failures = prime_failures ++ rsa_failures ++ batch_failures ++ ec_failures ++ roca_failures
total = length(primality) + length(rsa) + length(batch) + length(ec) + length(roca)
matched = total - length(failures)

Enum.each(failures, fn f -> IO.puts("  - " <> f) end)
IO.puts("elixir: #{matched}/#{total} cases matched")

if failures == [], do: System.halt(0), else: System.halt(1)
