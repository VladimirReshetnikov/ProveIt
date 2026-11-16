# Lean formalization status and completion path

These are **uncompiled outlines**, not a completed Lean verification. No `sorry`
or added axiom is used to state the missing results as proved. Proposition-valued
definitions deliberately identify the remaining obligations. Conditional assembly
theorems remain conditional.

## Files

- `RationalGeometry.lean` uses `Std` only. It gives complete definitions of the
  rational expression language, integer polynomial normalization, all metric and
  electromagnetic entries, formal differentiation, Christoffel symbols, Ricci
  contraction, Einstein--Maxwell residuals, and their exact arithmetic target.
- `ObjectTarget.lean` names the separate object-language target
  `Prf PRAAx [] (statement s)` and the final existing transfer to the native core.
  Its `ArithmeticSymbols` fields must be replaced by the concrete `PR` syntax
  for the coding operations described in the paper. They are obligations, not
  axioms asserted to have been satisfied.
- `upstream_inspected/` records four inspected source files, unchanged, from
  ProveIt. They are a provenance excerpt, not a self-contained copy of all imports.

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `87ccad4659b63acdce75540d17a69d799bbd25ad`

The inspected `lean-toolchain` specifies `leanprover/lean4:v4.32.0`, and the root
Lake configuration requires mathlib `v4.32.0` and exposes the `ConciseIPRA` library.
Neither `lean` nor `lake` was available in this generation environment, so no build
result is claimed here.

## Completion order

1. Compile `RationalGeometry.lean` under the pinned toolchain and fix any API or
   elaboration changes. The file is a transparent specification; directly
   expanding all its unreduced expressions is intentionally not the efficient
   certificate-replay strategy.
2. Implement the executable polynomial representation used by the delivered
   certificate checker in Lean. Prove addition, negation, convolution and formal
   derivative correctness. For a monomial-factor reduction, verify the claimed
   quotient by multiplying it back; do not trust an external CAS's cancellation.
3. Prove `CoefficientSoundGoal` by grouping equal exponent vectors, using finite
   list folds. Prove `NormalizationSoundGoal` by rational-expression recursion.
   For future object proof extraction, retain the explicit bounded fold invariant
   described in `notes/ipra_audit.md` rather than relying only on a host induction.
4. Prove `GuardPropagationGoal`. Every inverse in the fixed master calculation
   reduces to products and powers of `2`, `Sigma`, `Delta`, and `1-x^2`.
   The recursive derivative of an inverse only squares existing guarded factors.
5. Replay all exact certificate steps in Lean and discharge
   `CheckedResidualsGoal`. Kernel `decide`/explicit proof terms or proved
   reflection are suitable; an unverified `native_decide` run must not stand in
   for the arithmetic derivation or the certificate soundness proof.
6. Discharge `ArithmeticGoal` with `arithmetic_of_obligations`. Add specialization
   substitutions `q=0`, `a=0`, and both zero. Prove determinant/signature and
   coordinate-chart bridges separately, using the formulas in the paper.
7. Encode signed integers, positive-denominator rationals, finite polynomial
   arrays and bounded folds by explicit `PR` syntax. Implement their arithmetic
   laws as derivations using `PRA.qfInd`, `PRA.comp`, `PRA.precZero`,
   `PRA.precSucc`, and `Prf.eqCongr`/`Prf.eqTrans`. Instantiate the normalizer
   soundness invariant at the fixed certificate. Construct, rather than merely
   name, `main_derivation : MainDerivationGoal concreteSymbols`.
8. Apply `native_of_main`, whose underlying `pra_iff_native` theorem is already
   present in the pinned repository. The bridge transfers an existing derivation;
   it does not convert an arbitrary theorem about ordinary Lean rationals into an
   iPRA derivation.
9. For constructive real semantics, fix each primitive recursive name externally,
   give explicit bounds and reciprocal apartness, and internalize its requested
   finite precision contracts. A global Lean manifold theorem is an additional
   semantic layer, not a prerequisite for the arithmetic identities.

## Suggested build commands

Inside the pinned ProveIt checkout, with these files copied into a temporary
directory and `ConciseIPRA` built:

```sh
lake env lean path/to/RationalGeometry.lean
lake env lean path/to/ObjectTarget.lean
```

Inspect `#print axioms` on final discharged theorems. Keep separate ledgers for
host algebra, object-language arithmetic, effective real interpretation, and
global geometric statements. This packet's completed claim is the mathematical
proof and exact executable certificate; the full Lean derivation is the project
specified above.
