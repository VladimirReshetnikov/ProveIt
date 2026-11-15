# Lean interface drafts

**Status: uncompiled and incomplete.** No Lean executable was available
when this package was produced. These files are not a formalization of
the analytic proof and do not establish the final iPRA theorem.

| File | What it states |
| --- | --- |
| `AlgebraicCore.lean` | The polynomial identity expressing the symmetry of `1+s*(s-1)*(J(s)+J(1-s))`, for an arbitrary function `J` over a commutative ring. |
| `ArithmeticBridge.lean` | A quantifier-free matrix `check=1`, its universal closure, and transfer of a **supplied** iPRA derivation through `pra_iff_native`. |
| `lean-toolchain` | The inspected ProveIt toolchain, `leanprover/lean4:v4.32.0`. |

The drafts contain no added axioms or `sorry`. That does not mean they
have been compiled, nor does it fill in the missing analytic definitions
and object-language derivations.

## Intended environment and checking commands

Use a ProveIt checkout at commit
`c5093c20b5bffb0333fd42915b7bc858d5aa45cc`, with its recorded Lean and
mathlib `v4.32.0` dependencies installed. These drafts do not constitute a
standalone Lake project.

From that ProveIt checkout, the proposed commands are:

```bash
lake build +ConciseIPRA.NativeBiInterpretation
lake env lean /absolute/path/to/zeta_ipra/lean/ArithmeticBridge.lean
lake env lean /absolute/path/to/zeta_ipra/lean/AlgebraicCore.lean
```

Replace the two absolute paths with the extracted package location.
These commands were **not executed** in the production environment;
compatibility or elaboration fixes may be needed.

## Completion criterion

Implement the fixed finite checker from `../finite_contract.md` as
`compiledCheck : PR 3`, prove all finite estimates in the deeply embedded
theory, and construct:

```lean
Prf PRAAx [] (residualSentence compiledCheck)
```

Then apply the existing `pra_iff_native` bridge to obtain:

```lean
NPrf [] (NFm.ofPRA (residualSentence compiledCheck))
```

The seven main implementation layers and their acceptance gates are
listed in `../formalization_plan.md`. Ordinary Lean statements about
`Complex`, `Rat`, or a semantic evaluator do not substitute for this
object-language derivation. Mathlib's zeta theorems may be used in a
separate semantic comparison.
