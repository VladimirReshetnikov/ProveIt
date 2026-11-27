# Lean formalization roadmap (not compiled)

The following is an implementation plan. It is not Lean source, not a checked proof, and does not assert that Mathlib contains specific lemmas under guessed names. The local environment did not have `lean` installed.

## Target interface

Use the pinned `grh-compact` project (Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`). Import its `Main` for the forward result, then apply `LFunction_eq_zero_re` to all characters in the annihilator of a fixed subgroup. The unconditional converse should instead be in a separate module importing only classical analytic prerequisites, not the proved GRH theorem.

The intended statements are those of Theorems 2.1 and 2.2 of `paper.pdf`:

1. For q positive, H a subgroup of the units of ZMod q, and the finite character set X annihilating H, assume every L-zero in the open strip has real part 1/2. There exists C such that for m >= 1 and real t >= 0, `|B m d t - 4*M| <= C * log (2*m) / sqrt m`.
2. For fixed m, eventual upper boundedness of `B m d` implies the critical-line proposition restricted to X. Stronger version: if any zero has real part > 1/2 + delta, then the scaled expression is unbounded above on every tail.

`M` should be the sum of analytic orders of vanishing at 1/2, not a count of distinct zeros. It includes any central zeros and excludes the pole at 1. Establish finiteness of orders using non-identically-zero L-functions. For primitive descent, prove that missing Euler factors are nonzero on the open strip.

## Dependency DAG and proof obligations

| Layer | Precise obligation | Source / method |
|---|---|---|
| A | Character orthogonality for H and X; extension by zero, q=1 | finite duality of abelian groups |
| B | Ramp sum, S, Laplace transform, Laurent cancellation | paper Lemma 3.1; termwise integration on absolutely convergent domain |
| C | Completed Hadamard products, zero counts, local partial fractions, vertical and horizontal contour estimates | standard analytic theory; some results in repository `Lib` may be reusable, exact API audit needed |
| D | Ramp Perron inversion and absolutely convergent spectral formula under GRH | paper Lemma 3.2; rectangular contour, residues, dominated convergence |
| E | Finite forward shifts, binomial expansion, constant elimination and multiplier | direct algebra; independent of analytic number theory |
| F | Two-frequency bound for sqrt 2 | paper Lemma 4.1; nearest integer, Pell norm, compact minimum, cosine inequality |
| G | Dyadic sum of damped coefficients | paper Lemma 4.2; geometric and superexponential series |
| H | Uniform convergence plus error contraction | A–G; forward theorem |
| I | Entire correction from finite interval Laplace transform; pole signs | B and E; no GRH |
| J | Landau principle for nonnegative integrals | paper Lemma 5.1; Taylor coefficients, monotone convergence; consider reusable `Lib/Analytic/Landau/PolarLandau.lean` |
| K | One-sided blowup and reflection via primitive functional equation | I, J, classical line-1 nonvanishing; no GRH |

## Recommended implementation order

First implement E and F, which have short stand-alone algebraic/real-analysis proofs. Next formalize G in an abstract countable weighted-frequency interface. State H parametrically in a supplied summable spectral expansion and prove it without any number-theoretic API. In parallel implement I and J for general Laplace transforms, so K depends on only a meromorphic-pole hypothesis and reflection. Finally connect the generic results to A–D. This isolates the substantial analytic-number-theory work instead of obscuring it in tactic scripts.

Audit `#print axioms` of both final theorems, build from the pinned toolchain, and verify the converse does not depend on the GRH theorem. No `sorry`, axiom replacement, or independent kernel check of this extension is provided in this archive.
