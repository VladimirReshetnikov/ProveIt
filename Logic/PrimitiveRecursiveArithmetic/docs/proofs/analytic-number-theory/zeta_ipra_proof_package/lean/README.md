# Lean formalization outline: explicit trust boundary

**Status: these `.lean` files are uncompiled candidates.** No Lean, Lake, or Elan executable was available in the preparation environment. There is no claim that their syntax or proof scripts passed a kernel check. They contain no added `axiom` declarations and no `sorry` terms; that fact alone is not verification.

The human mathematical development in the PDF is the principal deliverable. `FiniteDefinitions.lean` records rational complex data, names, apartness, Bernoulli recursion, elementary finite polynomials, and the regularized Euler–Maclaurin expression. `ArithmeticTargets.lean` gives the actual deep-embedding endpoint using the inspected ProveIt names `PR`, `PTm`, `PRAAx`, `Prf`, and `pra_iff_native`.

## Pinned environment

- ProveIt: `f7e5eac0a94a0e690a22cbeecc5f6cca9270e6df`.
- Root `lean-toolchain`: `leanprover/lean4:v4.32.0`.
- Root `lakefile.toml`: Mathlib `v4.32.0`; the `ConciseIPRA` library source directory is `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`.

In a configured checkout at that revision, try:

```sh
lake env lean /absolute/path/zeta_ipra/lean/FiniteDefinitions.lean
lake env lean /absolute/path/zeta_ipra/lean/ArithmeticTargets.lean
```

These commands are proposed reproduction steps, not commands run in this task.

## Completion order

1. Port the exact `CQ`/ball arithmetic and fixed exp/log programs from Python to explicit natural-number/rational-code functions. Prove signed-integer and fraction decoding invariants.
2. Compile each fixed program to `PR k` by the constructors `zero`, `succ`, `proj`, `comp`, `prec`. The semantic correctness proof takes place in Lean; the corresponding arithmetic laws need actual `Prf PRAAx` derivations. A semantic theorem about `ℂ` is insufficient.
3. Prove coded finite sums/products, bounded Boolean conjunction, factorization, finite mesh calculus, and rational error propagation using `PRA.qfInd`. Fix the final precision before each induction.
4. Port the Bernoulli coefficient recursion; prove derivative, endpoint, reflection and finite-difference identities. Prove finite Euler–Maclaurin with its signed remainder.
5. Build the entire regular part `H` using the explicit cutoff in the paper, prove consistency and local Taylor estimates, then define zeta only on pole-apartness charts. For general names use the removable-quotient power series, never an exact-zero branch.
6. Add Dirichlet tails, convolution, Möbius/Euler/eta identities and derivatives; prove that the Dirichlet and EM names agree. Add the rotating-block non-Cauchy theorem.
7. Formalize the reciprocal-gamma product and sine gateway, finite Fejér estimate, Gaussian transform, theta periodization, and Mellin splitting. Prove quantitative disk propagation using a finite tree of rational samples and its PR precision recursion; identify the EM and theta continuations.
8. Prove the global Euler–Hasse series using the shifted finite Mellin identity and the C(n+1)^m bound. Derive functional equations, special values, Stieltjes expansion, integrals, and explicit zero-free bounds from the finite lemmas. Circle coefficient extraction is a finite Fourier calculation, not a call to a classical identity theorem.
9. For each theorem form the explicit coded rational residual inequality. Construct a fixed `PR 1` checker for its packed numerical input and a term `Prf PRAAx [] (residualSentence checker)` (or a sequent under fixed-name hypotheses). Only then apply `pra_iff_native`.
10. Run Lean on all files, print transitive axioms for all final theorems, reject unresolved placeholders, and archive the exact source revision and build logs. An ambient use of `Classical.choice` does not by itself settle whether an object proof is intuitionistic; inspect the constructed `Prf` constructors and induction formulas.

The paper includes the invariant, cutoff, and error contract for each of these stages. No unfinished analytic obligation is disguised here as an assumed theorem with the target as a hypothesis.
