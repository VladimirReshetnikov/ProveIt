# Logic of the numerical calculus, in models of IΣ₁

The direction `¬Halt(M₁₉₄) → Con(PA)` needs, inside a model, a derivation of the
contradiction code in the separate-diagonal numerical calculus from an internal first-order
proof. The ordinary-number version of that compiler is
[`pa194-reverse-rewrite`](../pa194-reverse-rewrite), [`pa194-source-calculus`](../pa194-source-calculus),
[`pa194-source-lk`](../pa194-source-lk) and [`pa194-foundation-lk`](../pa194-foundation-lk/README.md).
This directory rebuilds it for `TargetProvable`, the provability predicate of the calculus in
a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`.

**Status.** The implication basis, finite-context machinery, and fixed-size neighborhood
equality derivations are checked. They contain no induction inside the model. The compiler
itself, which needs
internal inductions over a derivation, over formula codes and over sequents of nonstandard
length, is not started. Nothing here yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `PA194ModelPropositional` | The upstream generic derivation `M6.Logic.RestrictedImplication` instantiated with `M`, `impValue` and `TargetProvable`: `imp_k`, `imp_s`, `imp_peirce`, `imp_comp`, `imp_exchange`, `imp_refl`, and `rho8_all` (the restricted row without its side condition `u ≤ a`). |
| `PA194ModelContext` | `Ctx Γ a`: proof trees of standard size from a standard-length list `Γ` of model elements. `Ctx.deduction` (deduction theorem), `Ctx.generalize`, `Ctx.existsElim`, `Ctx.casesOnFormula`; `explosion`, `doubleNegationElimination`, `contraposition`; the vacuity rules `negationVacuity`, `implicationVacuity`, `universalVacuity`, `conjunctionVacuity`; `existentialMonotonicity`, `liftImp`; `memRight`, `memLeft`. |
| `PA194ModelNeighborhood` | The target-code neighborhood relation is reflexive, symmetric and transitive, and three corresponding universally closed source equality-supplier-shaped formulas are target-provable for arbitrary model labels. |
| `PA194ModelNeighborhoodDef` | The neighborhood and biconditional constructors are Σ₁-definable model functions, which permits their use in suitable internal induction predicates. |
| `PA194ModelNeighborhoodCode` | A fixed ternary candidate-PRA code for the neighborhood constructor has its stated value on arbitrary model inputs, including nonstandard labels, and agrees over the natural numbers with the existing source-LK neighborhood encoding. |
| `PA194ModelSourceAtomCode` | Candidate-PRA codes decode positive and negative source equality atoms and select bound/free labels from encoded environments, including for nonstandard terms and vectors. |

These are fixed-size proof transformations parameterized by arbitrary elements of `M`,
not an internal induction over source proof codes. The formulas have the same displayed
shape as the ordinary-number source-LK equality suppliers, but no theorem here identifies
them with the translation of internal source-formula codes. The latter connection and the
internal compiler remain open.

For the source atom decoder, relation code `0` is equality and the term vector
must satisfy Foundation's `IsUTermVec` predicate at arity two. The raw codes
do not check the atom tag, arity, relation code, term validity or scope; these
are hypotheses of the model equations. The function-free source language has
only bound and free variable terms. The two label environments are Foundation
stacks encoded with `0` for empty and `pair head tail + 1` for cons; the
existing total lookup code agrees with Foundation's `stack.[i]`. No index
bounds are asserted. The atom code applies the neighborhood constructor to
the selected labels and a reserved label, with negation for a negative atom.
Its fixed Σ₁ graph is correct on arbitrary inputs. The finite codes inherit
the earlier classically chosen Cantor and projection witnesses.

These results do not identify the environments with the compiler's variable
allocation policy, recursively translate internal source formulas, or compile
nonstandard source proofs.

The entries of a context and the parameters of every theorem are arbitrary elements of `M`,
so they cover nonstandard formula codes. What is standard is the shape of each derivation.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check.sh [--out DIR]
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with
`PA194ModelSourceAtomCode` as the top module. On 2026-11-14, the preceding
modules and the source-atom code were rebuilt against a retained combined
overlay. Their printed axiom reports were free of `sorryAx`. The
overlay contains previously checked Foundation, project and standalone
prerequisites; these were suffix checks, not empty-overlay replays.
