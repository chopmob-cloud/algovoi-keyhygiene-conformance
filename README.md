# algovoi-keyhygiene-conformance

A signed, cross-language conformance battery for **RSA/EC public-key hygiene and
primality soundness**. Given a candidate integer or a public key, every
independent implementation must reproduce the same accept/reject verdict,
byte-for-byte, including the adversarial cases that fool naive checks.

This is the **L0** layer of the AlgoVoi assurance stack: is the key material
sound *before* you sign with it?

```
L0  key soundness      is the prime / key sound at all        <- this repo
L1  canonicalisation   RFC 8785 (JCS) canonical bytes         (algovoi-jcs-conformance-vectors)
L2  signature verdict  RFC 9421 accept/reject over bytes      (algovoi-rfc9421-conformance)
```

## Why this exists

Rejecting weak keys is not a nicety, it is a compliance obligation. The
CA/Browser Forum Baseline Requirements require CAs to reject ROCA, Debian-weak,
and small-factor keys; eIDAS qualified trust service providers must validate key
material; HSM/TPM and government-PKI operators need third-party assurance that
their acceptance logic actually rejects the known-weak classes. None of them has
a neutral, signed, cross-language corpus to test against. This is that corpus.

It is deliberately **not** payment-specific: the primitives (primality, RSA
modulus hygiene) sit under every PKI, so the battery reaches the RSA-dominant
regulated industries (CAs, eIDAS, HSM/TPM, government identity, TLS/PKI audit).

## The sections (v0)

| Section | Each case | Verdict |
|---|---|---|
| `primality` | a candidate integer (decimal string) | prime? (Baillie-PSW ground truth) |
| `rsa_modulus_hygiene` | an RSA public key `(n, e)` | accept / reject + reason, under the CA/Browser-Forum-tracking policy |

`primality` carries the adversarial core: composites that are **strong
pseudoprimes** to a target base set, so a checker using Miller-Rabin over those
bases calls them prime. Every composite carries a factorisation, so the corpus
proves its own compositeness by multiplication, without trusting any primality
test.

`rsa_modulus_hygiene` rejects perfect-power moduli, small-factor moduli,
close-prime (Fermat-factorable) moduli, disallowed bit lengths, and disallowed
public exponents; it accepts valid 2048/3072/4096-bit moduli.

## The differential has teeth

```
python tools/demo_naive_divergence.py
```

demonstrates that each adversarial vector fools a naive fixed-base Miller-Rabin
checker while Baillie-PSW (ground truth) catches every one. A conformance corpus
of verdicts is only meaningful if a weak implementation actually gets some wrong;
this shows the primality section discriminates.

## Assurance

- **Signed corpus.** The corpus head (per-section digests + file hash) is
  canonicalised (RFC 8785 JCS) and EdDSA-signed via
  [algovoi-corpus-cm](https://github.com/chopmob-cloud/algovoi-corpus-cm); only
  the public JWK ships, the signing seed is a genuine secret held off-repo.
- **KAT gate** (`tools/check_kat.py`): verifies the head signature, and
  independently re-derives every verdict, composites by re-multiplying their
  factors, primes by deterministic Miller-Rabin sound in range, RSA reasons by an
  independent structural check, so a systematic error shared by the generator and
  a runner cannot pass as consensus.
- **N-way consensus** (planned): twelve independent implementations, each using
  its own big-integer stack, must reproduce every verdict.

## Security scope (defensive only)

This is audit / key-acceptance conformance tooling. It ships **public keys and
crafted composites only, never private keys**. The weak keys exist to test
detection (ROCA and batch-GCD detection are published defensive techniques). It
contains no factoring engine aimed at live keys; bounded Fermat is used only as a
detector on the corpus's own crafted moduli.

## Run

```
python tools/gen_keyhygiene_v0.py                      # regenerate the corpus (deterministic)
python runners/python/verify_py.py                     # reference runner: reproduce every verdict
ALGOVOI_LOCAL_SRC=/path/to/algovoi-corpus-cm/src \
  python tools/sign_keyhygiene_v0.py                   # sign the head (off-repo secret)
ALGOVOI_LOCAL_SRC=/path/to/algovoi-corpus-cm/src \
  python tools/check_kat.py                            # fail-closed KAT gate
```

## Licence

Apache-2.0. See `LICENSE` and `NOTICE`.
