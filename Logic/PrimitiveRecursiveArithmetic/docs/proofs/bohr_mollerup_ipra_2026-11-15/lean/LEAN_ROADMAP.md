# Lean formalization roadmap

This directory contains an **outline**, not a completed formalization. The
build environment used for the report did not contain `lean` or `lake`, so the
scaffold has not been type-checked here. The target repository already has the
critical object-theory infrastructure under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA`.

## Existing interfaces to reuse

- `ConciseIPRA.PR`
  - `PR k`: primitive-recursive function syntax.
  - `PTm n`: iPRA terms.
  - `PRAAx`: defining equations, successor axioms, and quantifier-free
    induction.
  - `PRA.qfInd`: the induction constructor to use for all coded loop
    invariants.
- `ConciseIPRA.BiInterpretation`
  - `pra_theorem_iff`: transports a closed theorem of the usual iPRA
    presentation to the concise scalar theory.

## Proposed module graph

```text
BM.Code
  ├── BM.IntervalReal
  ├── BM.AMGM
  └── BM.Root
         └── BM.EulerBracket
                 └── BM.GammaQ
                       ├── BM.EulerConvex
                       └── BM.Squeeze
                              └── BM.Completion

BM.PRDefs ── BM.QFGraphs ── BM.ObjectLemmas
                              └── BM.ObjectTheorem
                                    └── BM.Translate
```

## Milestones and acceptance criteria

1. **Exact rational core**
   - Canonical signed rational codes and cross-multiplied order.
   - No quotient types in object-level code.
   - Tests agreeing with `code/bm_bounds.py`.

2. **Bounded root bisection**
   - Explicit iteration count.
   - Invariant `lo^b ≤ target ≤ hi^b` and dyadic width theorem.
   - PR syntax implementation and defining-equation proof.

3. **Euler brackets**
   - Definitions of `A n q` and `B n q` through rational root names.
   - `A n ≤ A (n+1)`, `B (n+1) ≤ B n`, and `B n - A n ≤ 1/n`.
   - Proof uses the finite weighted AM–GM certificate, not logarithms.

4. **Gamma presentation**
   - Running maximum/minimum normalization of raw enclosures.
   - Strip value on `0 < q ≤ 1`.
   - Canonical decomposition `x = m + r` and recurrence extension.

5. **Uniqueness**
   - Upper squeeze from convexity at `n+q` between `n` and `n+1`.
   - Lower squeeze from convexity at `n+1` between `n+q` and `n+q+1`.
   - Explicit power-gap rate and positive-power cancellation.

6. **Constructed convexity**
   - `E_n` factorization and `C_m/n` tail.
   - Weighted AM–GM proof that every `E_n` is RLC.
   - Explicit finite-power perturbation bound for passing to gamma.

7. **Completion**
   - Derive the rational local modulus from the finite approximants.
   - Extend from canonical rational centers of a regular input name.
   - Prove real-domain equality using the two supplied moduli.

8. **Object-level replay**
   - Compile every algorithm to `PR`.
   - Represent every invariant by a quantifier-free graph formula.
   - Use `PRA.qfInd` only.
   - Discharge candidate hypotheses explicitly in the final formula.

9. **Translation and audit**
   - Apply `pra_theorem_iff`.
   - Add `#print axioms` for all exported theorems.
   - CI rejects `sorry`, `admit`, `axiom`, and `sorryAx` in completed modules.

## Suggested theorem names

```lean
rootBisect_invariant
rootBisect_width
weighted_amgm
A_mono
B_antitone
B_sub_A_le
stripGamma_regular
gammaQ_one
gammaQ_add_one
eulerApprox_le_gamma
gamma_sub_eulerApprox_le
eulerApprox_rlc
gammaQ_rlc
candidate_pow_lower
candidate_pow_upper
pow_gap_le
pow_injective_of_strongPositive
bohrMollerupQ
gammaQ_localModulus
bohrMollerupRegular
bmClosedFormula_derivable
bmClosedFormula_in_concise_core
```

## Important proof-engineering choice

Do not begin by importing Mathlib's real gamma function. Its existing
Bohr–Mollerup theorem is useful as a regression target, but it obscures the
proof-theoretic claim. The core development should be finite arithmetic on
codes. A separate bridge file may later prove that the completed regular-real
presentation agrees extensionally with `Real.Gamma` in a stronger ambient
theory.
