# Ten positive unknowns, degree 816: a scaled, centered sixteen-fold norm

One integer-coefficient polynomial N in **ten strictly positive unknowns**

    j, F, alpha, i, T, w, Y, n, eta, zeta

with **exact total degree 816** and **124 binary operations** (74 ×, 30 +,
20 −). Its coefficients are the whole compact44 tuple (beta, K0, MC, MF),
with B = beta+1 = 2^590069 and MF already shifted. [PROOF.md](PROOF.md)
proves:

> N has a zero in positive integers if and only if ZFC has a finite
> syntactic refutation.

Hence ZFC proves that Con(ZFC) is equivalent to N having no positive zero.
The proof is ordinary mathematics. Its only inherited theorem is package
61's compiler/calibration interface (`thm:source`). Package 70 also
needs a weighted transport theorem; this proof does not.

This is an in-repository research result written by Claude (Anthropic) at
Vladimir Reshetnikov's request on 2026-10-23. It is not an intake package.

## Where it sits

All comparison numbers are from this repository: the
[combined frontier](../../con-zfc-diophantine-forms/README.md), the
[wave-11 review](../../PROPOSAL_REVIEW_WAVE11.md) and the
[latest size comparison](../../PROPOSAL_REVIEW_LATEST.md). "Positive" means
strictly positive unknowns; ℤ means unrestricted integers.

| Unknowns | Previously best stated | **This equation** |
|---|---|---|
| 9 positive | 433 ops at degree 1,628,768; degree 999,518 at 953 ops | — |
| **10 positive** | **131 ops, degree 1,152** (radical-residue arrival `440dd03ab8`) | **124 ops, degree 816** |
| 10 ℤ | 471 ops at degree 1,245,324; degree 1,080,888 at 512 ops | different domain |
| 11 positive | 111 ops at degree 211 | — |

Against the only previous ten-positive equation, this one is better in both
measures: 7 fewer operations and degree 29% lower. Against the nine-positive
forms, one more unknown buys a degree about 1,200 times lower in less than a
third of the operations. The 10ℤ forms quantify over all integers, so
they are not directly comparable. No global minimality is claimed.

## The construction

Package 70's eleven-positive equation sums three Pell roots (first,
strong, auxiliary) in an octic norm. It keeps the main Pell residual and
its quotient gamma in a separate equation. Making the main root a fourth
radical of one sixteen-fold norm removes gamma. The radical-residue
arrival did this first, and this note found it concurrently. Here
X = wq is built in. One rational equation must then deliver four
congruences:

* q³ | Y,
* q−1 | transport,
* μ² | k−R−1 with μ = q²+1,
* H′ | X + a′c − D_main.

The construction gets them in four moves:

1. **μ-scaling.** Both Pell parameters are scaled by μ: A′ = μ(a+2)+1 and
   P′ = 2Xμ²Y²+1. The Pell ratio c/k still satisfies the half-binomial
   bounds, and μ² enters the first-index modulus while Y stays a free
   degree-1 unknown. H′ = 4A′−5 ≡ −1 modulo every prime of μ, so the index
   congruence comes out of a coprime partial fraction.
2. **Archimedean separation.** The remaining moduli H′, q³ and q−1 may
   share factors. Clearing them gives only H′ | q³(q−1)(X + a′c ∓ D_main).
   Once the indices are fixed, H′ exceeds q⁴·2^(R+1)·X. The projections
   χ − a′ψ ≡ 2^R and χ + a′ψ ≡ 2^(−R) then force the positive main root
   and X = 2^R, after which q³ | Y and q−1 | transport follow. This adapts
   the radical-residue ten-positive proof.
3. **Centering.** The carrier is centered at the auxiliary register V,
   with the inner cancellation of the joint-guards centered endpoint. V is
   made positive by the offset T′ = T+α, a sharper form of the
   polynomial-shears offset T+F+α. The transport weight then needs degree
   only 13. In the norm the two largest arguments now differ by a
   polynomial of degree 102. The exact degree therefore drops from the
   syntactic 928 to 8·102 = 816; the sixteen-fold pairing lemma in
   PROOF.md, Lemma 8.1, proves this.
4. **A compact norm.** F16 = Ge² − 64·sd·Go², with Pe = Po² + 4(sd − σ₂),
   takes 28 operations. The radical-residue circuit already uses this
   schedule.

The scaled kernel only pins down R, X = 2^R, Y = M/2 and R ≡ 3 (mod 4).
Package 61's source theorem is then applied to freshly constructed
unscaled witnesses. Package 69's adjacent-coefficient descent makes the
auxiliary root integral.

## How it got here

The first version used the scaling λ = q(q−1)(q²+1) and full coprimality:
136 operations, degree 1,216 (an earlier draft had degree 1,360). The
radical-residue archive had already delivered 131/1,152 with unscaled
parameters and Y = q³s. That archive arrived in `docs/incoming` at 19:09 and
was reviewed at 19:34. Both events predate the first version's package
files, but this note's construction was already in progress in scratch: its
sixteen-fold norm check dates from 19:05. Combining the archive's Archimedean step
and compact norm with μ-scaling gave 124/960. Centering gave 124/816.
PROOF.md Sections 0 and 9 list what is borrowed and what is new.

## Files

| File | Contents |
|---|---|
| [PROOF.md](PROOF.md) | Definitions, lemmas, estimates for all inputs, soundness, completeness, exact degree |
| `circuit.py` | The 124 literal rows and an evaluator |
| `p10_positive_degree816.json` | The emitted circuit (one row per line), counts, register degrees, coefficient binding |
| `build.py` | Emits the JSON; `--check` regenerates and compares bytes. Verifies the port hashes, B = 2^590069, 0 < MC < beta < MF < 2·beta, K0 > 0, topology, liveness and counts |
| `verify.py` | Finite audits (below); writes `CHECKS.json` |
| `CHECKS.json` | Receipt of the last full `verify.py` run |
| `INDEPENDENT_REVIEW.md` | Adversarial review of the proof and circuit |

The coefficients are read at their canonical binding,
`con-zfc-diophantine-forms/44-b4-sparse/native/coefficients/`. These are
the same four payloads as package 70's `ACTIVE_BINDING.json`, checked by
gzip and raw SHA-256.

## Running

```bash
py -I build.py --check
```

```bash
py -I verify.py
```

`verify.py` needs SymPy and mpmath, and uses gmpy2 when available. It
checks:

* the F16 identity and Lemma 8.1, symbolically;
* the register contracts against an independent evaluator, modulo
  2^127−1 with the actual ports;
* the conjugate-product identity at real points, to 4000 digits;
* the exact degree: restrictions to random lines with the actual ports have
  degree 816, with leading coefficient ω0⁸ from the closed form;
* the μ-scaled and unscaled Pell kernels with toy q (16 ≤ q ≤ 64), at Pell
  values of up to 3.7 million bits. The actual q exceeds 2^590070, so these
  cases test the identities, not the actual sizes;
* the composition and descent lemmas, on small parameters;
* the estimates valid for every input, with the actual ports, in the
  three sign cases of b′ = cT′ − R.

A full run takes about five minutes; `--quick` skips the last audit. These
finite checks support the proof but do not replace it.

## Limits

* The compiler, compact-coefficient adapter and blank-K215 calibration
  are inherited through package 61's `thm:source`.
* No Lean formalization was attempted. Lean work in this project is
  paused.
* Over the natural numbers, substituting v+1 for every unknown keeps the
  degree and adds at most ten additions.
* A second center at the strong root's approximation A′I is possible; it
  is the analogue of the polynomial-shears center Cf = (a+2)I. The
  transport majorant then drops its strong-root term: L = 2(V₀+1)k + I +
  b′ + cT′. A scratch circuit of 127 operations measures exact degree 796
  on random lines with the actual ports. Its proof is not written up here,
  so it is not claimed.
