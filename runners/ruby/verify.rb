# frozen_string_literal: true

# Ruby runner for the keyhygiene battery.
#
# Independent port of tools/oracle.py using Ruby's arbitrary-precision Integer:
# Baillie-PSW primality (strong Miller-Rabin base 2 + strong Lucas) and the RSA
# hygiene detectors (perfect power, small factor, close primes). Reads the frozen
# corpus and reproduces every verdict byte-for-byte; exits 0 iff all match.
#
# Ruby's Integer is arbitrary precision. Integer#pow(e, m) is modular
# exponentiation and Integer.sqrt is floor integer square root; both are used
# below in place of the portable helpers oracle.py implements by hand. We do NOT
# use `require 'prime'` because Prime.prime? is trial division, not BPSW.

require 'json'

# ---------------------------------------------------------------------------
# integer helpers
# ---------------------------------------------------------------------------

def isqrt(n)
  raise ArgumentError, 'isqrt of negative' if n < 0

  Integer.sqrt(n)
end

# True if n == a**b for integers a >= 2, b >= 2 (mirrors oracle.is_perfect_power).
def perfect_power?(n)
  return false if n < 4

  bl = n.bit_length
  (2..bl).each do |b|
    lo = 2
    hi = 1 << (bl / b + 1)
    while lo <= hi
      mid = (lo + hi) / 2
      p = mid**b
      return true if p == n

      if p < n
        lo = mid + 1
      else
        hi = mid - 1
      end
    end
  end
  false
end

# ---------------------------------------------------------------------------
# primality: Baillie-PSW (strong Miller-Rabin base 2 + strong Lucas)
# ---------------------------------------------------------------------------

SMALL_PRIMES = [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
  239, 241, 251
].freeze

# Strong (Miller-Rabin) probable-prime test of n to base a.
def mr_strong(n, a)
  return n == a if (n % a).zero?

  d = n - 1
  r = 0
  while (d % 2).zero?
    d /= 2
    r += 1
  end
  x = a.pow(d, n)
  return true if x == 1 || x == n - 1

  (r - 1).times do
    x = (x * x) % n
    return true if x == n - 1
  end
  false
end

# Jacobi symbol (a/n), n odd positive.
def jacobi(a, n)
  a %= n
  result = 1
  while a != 0
    while (a % 2).zero?
      a /= 2
      result = -result if [3, 5].include?(n % 8)
    end
    a, n = n, a
    result = -result if a % 4 == 3 && n % 4 == 3
    a %= n
  end
  n == 1 ? result : 0
end

# Strong Lucas probable-prime test with Selfridge parameters.
def lucas_strong(n)
  d_param = 5
  mag = 5
  loop do
    j = jacobi(d_param, n)
    break if j == -1
    return false if j.zero? && d_param.abs != n

    mag += 2
    d_param = (((mag - 5) / 2) % 2).zero? ? mag : -mag
  end
  p = 1
  q = (1 - d_param) / 4

  # decompose n+1 = d * 2^s with d odd
  d = n + 1
  s = 0
  while (d % 2).zero?
    d /= 2
    s += 1
  end

  # U_d, V_d, Q^d mod n via binary expansion of d
  u = 0
  v = 2
  qk = 1
  d.to_s(2).each_char do |bit|
    u, v = (u * v) % n, (v * v - 2 * qk) % n
    qk = (qk * qk) % n
    next unless bit == '1'

    nu = p * u + v
    nv = d_param * u + p * v
    nu += n if nu.odd?
    nv += n if nv.odd?
    u = (nu / 2) % n
    v = (nv / 2) % n
    qk = (qk * q) % n
  end

  return true if u.zero? || v.zero?

  (s - 1).times do
    v = (v * v - 2 * qk) % n
    qk = (qk * qk) % n
    return true if v.zero?
  end
  false
end

# Baillie-PSW: the ground-truth primality test.
def prime?(n)
  return false if n < 2

  SMALL_PRIMES.each do |sp|
    return true if n == sp
    return false if (n % sp).zero?
  end
  return false unless mr_strong(n, 2)
  return false if perfect_power?(n)

  lucas_strong(n)
end

# ---------------------------------------------------------------------------
# RSA modulus hygiene detectors
# ---------------------------------------------------------------------------

def smallest_factor(n, bound = 1_000_000)
  p = 2
  while p <= bound
    break if p * p > n
    return p if (n % p).zero?

    p += p == 2 ? 1 : 2
  end
  nil
end

def fermat_close_factor?(n, max_steps = 1 << 16)
  return true if (n % 2).zero?

  a = isqrt(n)
  a += 1 if a * a < n
  max_steps.times do
    b2 = a * a - n
    if b2 >= 0
      b = isqrt(b2)
      return true if b * b == b2
    end
    a += 1
  end
  false
end

BR_ALLOWED_BITS = [2048, 3072, 4096].freeze
BR_ALLOWED_E = [3, 65537].freeze

# Accept/reject an RSA public key (n, e); mirrors oracle.rsa_modulus_verdict.
def rsa_modulus_verdict(n, e)
  return [false, 'modulus_not_odd_or_too_small'] if n <= 3 || (n % 2).zero?
  return [false, 'modulus_perfect_power'] if perfect_power?(n)
  return [false, 'modulus_small_factor'] unless smallest_factor(n).nil?
  return [false, 'modulus_close_primes'] if fermat_close_factor?(n)
  return [false, 'modulus_bit_length_not_allowed'] unless BR_ALLOWED_BITS.include?(n.bit_length)
  return [false, 'public_exponent_not_allowed'] unless BR_ALLOWED_E.include?(e)
  return [false, 'public_exponent_invalid'] if e.even? || e < 3

  [true, 'ok']
end

# ---------------------------------------------------------------------------
# runner
# ---------------------------------------------------------------------------

def main
  path = ARGV[0] || ENV['ALGOVOI_KEYHYGIENE']
  if path.nil? || path.empty?
    warn 'no corpus path (ARGV[0] or ALGOVOI_KEYHYGIENE)'
    exit 2
  end

  corpus = JSON.parse(File.read(path))
  failures = []

  (corpus['primality'] || []).each_with_index do |c, i|
    got = prime?(c['value'].to_i)
    if got != c['expect_prime']
      failures << "primality[#{i}] #{c['note']}: got prime=#{got} want #{c['expect_prime']}"
    end
  end

  (corpus['rsa_modulus_hygiene'] || []).each_with_index do |c, i|
    accept, reason = rsa_modulus_verdict(c['n'].to_i, c['e'].to_i)
    if accept != c['expect_accept'] || reason != c['reason']
      failures << "rsa[#{i}] #{c['note']}: got (#{accept},#{reason}) want (#{c['expect_accept']},#{c['reason']})"
    end
  end

  total = (corpus['primality'] || []).length + (corpus['rsa_modulus_hygiene'] || []).length
  unless failures.empty?
    puts "FAIL: #{failures.length}/#{total} cases diverged"
    failures.first(20).each { |f| puts "  - #{f}" }
    exit 1
  end
  puts "ruby: #{total}/#{total} cases matched"
end

main
