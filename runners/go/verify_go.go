// Go runner for the keyhygiene battery.
//
// Independent implementation of the reference decision surface using math/big:
// Baillie-PSW primality (big.Int.ProbablyPrime(0) is a deterministic BPSW test)
// and the RSA hygiene detectors (perfect power, small factor, close primes)
// implemented directly. Reads the frozen corpus and reproduces every verdict;
// exits 0 iff all match.
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"
)

type corpus struct {
	Primality []struct {
		Value       string `json:"value"`
		ExpectPrime bool   `json:"expect_prime"`
		Note        string `json:"note"`
	} `json:"primality"`
	RSA []struct {
		N            string `json:"n"`
		E            int64  `json:"e"`
		ExpectAccept bool   `json:"expect_accept"`
		Reason       string `json:"reason"`
		Note         string `json:"note"`
	} `json:"rsa_modulus_hygiene"`
	Batch []struct {
		N            string `json:"n"`
		SharesFactor bool   `json:"shares_factor"`
		Note         string `json:"note"`
	} `json:"batch_common_factor"`
	EC []struct {
		Curve       string `json:"curve"`
		X           string `json:"x"`
		Y           string `json:"y"`
		ExpectValid bool   `json:"expect_valid"`
		Reason      string `json:"reason"`
		Note        string `json:"note"`
	} `json:"ec_key_hygiene"`
}

var (
	zero  = big.NewInt(0)
	one   = big.NewInt(1)
	two   = big.NewInt(2)
	three = big.NewInt(3)
)

func mustInt(s string) *big.Int {
	n, ok := new(big.Int).SetString(s, 10)
	if !ok {
		panic("bad integer: " + s)
	}
	return n
}

func isPrime(n *big.Int) bool {
	// ProbablyPrime(0) is Go's deterministic Baillie-PSW test.
	return n.ProbablyPrime(0)
}

func isqrt(n *big.Int) *big.Int {
	return new(big.Int).Sqrt(n)
}

func isPerfectPower(n *big.Int) bool {
	if n.Cmp(big.NewInt(4)) < 0 {
		return false
	}
	bl := n.BitLen()
	for b := 2; b <= bl; b++ {
		lo := big.NewInt(2)
		hi := new(big.Int).Lsh(one, uint(bl/b+1))
		exp := big.NewInt(int64(b))
		for lo.Cmp(hi) <= 0 {
			mid := new(big.Int).Add(lo, hi)
			mid.Rsh(mid, 1)
			p := new(big.Int).Exp(mid, exp, nil)
			c := p.Cmp(n)
			if c == 0 {
				return true
			} else if c < 0 {
				lo.Add(mid, one)
			} else {
				hi.Sub(mid, one)
			}
		}
	}
	return false
}

func smallestFactor(n *big.Int, bound int64) *big.Int {
	p := big.NewInt(2)
	pp := new(big.Int)
	rem := new(big.Int)
	for p.Int64() <= bound {
		pp.Mul(p, p)
		if pp.Cmp(n) > 0 {
			break
		}
		rem.Mod(n, p)
		if rem.Sign() == 0 {
			return new(big.Int).Set(p)
		}
		if p.Cmp(two) == 0 {
			p.Add(p, one)
		} else {
			p.Add(p, two)
		}
	}
	return nil
}

func fermatClose(n *big.Int, maxSteps int) bool {
	if new(big.Int).And(n, one).Sign() == 0 {
		return true
	}
	a := isqrt(n)
	if new(big.Int).Mul(a, a).Cmp(n) < 0 {
		a.Add(a, one)
	}
	b2 := new(big.Int)
	for i := 0; i < maxSteps; i++ {
		b2.Mul(a, a)
		b2.Sub(b2, n)
		if b2.Sign() >= 0 {
			b := new(big.Int).Sqrt(b2)
			if new(big.Int).Mul(b, b).Cmp(b2) == 0 {
				return true
			}
		}
		a.Add(a, one)
	}
	return false
}

var allowedBits = map[int]bool{2048: true, 3072: true, 4096: true}
var allowedE = map[int64]bool{3: true, 65537: true}

func rsaVerdict(n *big.Int, e int64) (bool, string) {
	if n.Cmp(three) <= 0 || new(big.Int).And(n, one).Sign() == 0 {
		return false, "modulus_not_odd_or_too_small"
	}
	if isPerfectPower(n) {
		return false, "modulus_perfect_power"
	}
	if smallestFactor(n, 1000000) != nil {
		return false, "modulus_small_factor"
	}
	if fermatClose(n, 1<<16) {
		return false, "modulus_close_primes"
	}
	if !allowedBits[n.BitLen()] {
		return false, "modulus_bit_length_not_allowed"
	}
	if !allowedE[e] {
		return false, "public_exponent_not_allowed"
	}
	if e%2 == 0 || e < 3 {
		return false, "public_exponent_invalid"
	}
	return true, "ok"
}

// batchCommonFactorVerdicts mirrors oracle.batch_common_factor_verdicts: per-key
// verdict is true iff the key shares a nontrivial prime with another key in the
// set (1 < gcd(n_i, n_j) < n_i for some j != i).
func batchCommonFactorVerdicts(moduli []*big.Int) []bool {
	out := make([]bool, len(moduli))
	g := new(big.Int)
	for i, ni := range moduli {
		shared := false
		for j, nj := range moduli {
			if i == j {
				continue
			}
			g.GCD(nil, nil, ni, nj)
			if g.Cmp(one) > 0 && g.Cmp(ni) < 0 {
				shared = true
				break
			}
		}
		out[i] = shared
	}
	return out
}

// ecCurve holds (p, a, b) copied EXACTLY from oracle.EC_CURVES.
type ecCurve struct{ p, a, b *big.Int }

func mustHex(s string) *big.Int {
	n, ok := new(big.Int).SetString(s, 16)
	if !ok {
		panic("bad hex: " + s)
	}
	return n
}

var ecCurves = map[string]ecCurve{
	"p256": {
		p: mustHex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"),
		a: mustHex("ffffffff00000001000000000000000000000000fffffffffffffffffffffffc"),
		b: mustHex("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"),
	},
	"p384": {
		p: mustHex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff"),
		a: mustHex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc"),
		b: mustHex("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef"),
	},
	"secp256k1": {
		p: mustHex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
		a: big.NewInt(0),
		b: big.NewInt(7),
	},
}

// ecKeyVerdict mirrors oracle.ec_key_verdict: in-range then on-curve check over
// the prime field. big.Int.Mod is non-negative for a positive modulus.
func ecKeyVerdict(curve string, x, y *big.Int) (bool, string) {
	c := ecCurves[curve]
	p, a, b := c.p, c.a, c.b
	if x.Sign() < 0 || x.Cmp(p) >= 0 || y.Sign() < 0 || y.Cmp(p) >= 0 {
		return false, "coordinate_out_of_range"
	}
	// lhs = y*y ; rhs = x^3 + a*x + b
	lhs := new(big.Int).Mul(y, y)
	rhs := new(big.Int).Mul(x, x)
	rhs.Mul(rhs, x)
	ax := new(big.Int).Mul(a, x)
	rhs.Add(rhs, ax)
	rhs.Add(rhs, b)
	diff := new(big.Int).Sub(lhs, rhs)
	if diff.Mod(diff, p).Sign() != 0 {
		return false, "not_on_curve"
	}
	return true, "ok"
}

func main() {
	path := ""
	if len(os.Args) > 1 {
		path = os.Args[1]
	} else {
		path = os.Getenv("ALGOVOI_KEYHYGIENE")
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintln(os.Stderr, "cannot read corpus:", err)
		os.Exit(2)
	}
	var c corpus
	if err := json.Unmarshal(raw, &c); err != nil {
		fmt.Fprintln(os.Stderr, "cannot parse corpus:", err)
		os.Exit(2)
	}

	var failures []string
	for i, cs := range c.Primality {
		got := isPrime(mustInt(cs.Value))
		if got != cs.ExpectPrime {
			failures = append(failures, fmt.Sprintf("primality[%d] %s: got prime=%v want %v", i, cs.Note, got, cs.ExpectPrime))
		}
	}
	for i, cs := range c.RSA {
		accept, reason := rsaVerdict(mustInt(cs.N), cs.E)
		if accept != cs.ExpectAccept || reason != cs.Reason {
			failures = append(failures, fmt.Sprintf("rsa[%d] %s: got (%v,%s) want (%v,%s)", i, cs.Note, accept, reason, cs.ExpectAccept, cs.Reason))
		}
	}

	if len(c.Batch) > 0 {
		moduli := make([]*big.Int, len(c.Batch))
		for i, cs := range c.Batch {
			moduli[i] = mustInt(cs.N)
		}
		verdicts := batchCommonFactorVerdicts(moduli)
		for i, cs := range c.Batch {
			if verdicts[i] != cs.SharesFactor {
				failures = append(failures, fmt.Sprintf("batch_common_factor[%d] %s: got shares=%v want %v", i, cs.Note, verdicts[i], cs.SharesFactor))
			}
		}
	}
	for i, cs := range c.EC {
		valid, reason := ecKeyVerdict(cs.Curve, mustInt(cs.X), mustInt(cs.Y))
		if valid != cs.ExpectValid || reason != cs.Reason {
			failures = append(failures, fmt.Sprintf("ec_key_hygiene[%d] %s: got (%v,%s) want (%v,%s)", i, cs.Note, valid, reason, cs.ExpectValid, cs.Reason))
		}
	}

	total := len(c.Primality) + len(c.RSA) + len(c.Batch) + len(c.EC)
	if len(failures) > 0 {
		fmt.Printf("FAIL: %d/%d cases diverged\n", len(failures), total)
		for _, f := range failures {
			fmt.Println("  -", f)
		}
		os.Exit(1)
	}
	fmt.Printf("go: %d/%d cases matched\n", total, total)
}
