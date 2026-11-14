# Logic of the numerical calculus, in models of IΣ₁

The direction `¬Halt(M₁₉₄) → Con(PA)` needs, inside a model, a derivation of the
contradiction code in the separate-diagonal numerical calculus from an internal first-order
proof. The ordinary-number version of that compiler is
[`pa194-reverse-rewrite`](../pa194-reverse-rewrite), [`pa194-source-calculus`](../pa194-source-calculus),
[`pa194-source-lk`](../pa194-source-lk) and [`pa194-foundation-lk`](../pa194-foundation-lk/README.md).
This directory rebuilds it for `TargetProvable`, the provability predicate of the calculus in
a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`.

**Status.** The implication basis, finite-context machinery and neighborhood equality
derivations are checked. A finite formula-translation code now agrees on internally valid
formulas with an independent model-level structural recursion, including for nonstandard
codes. Freshness and semantic correctness, and the compiler over internal derivations and
sequents of nonstandard length, remain open. Nothing here yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `PA194ModelPropositional` | The upstream generic derivation `M6.Logic.RestrictedImplication` instantiated with `M`, `impValue` and `TargetProvable`: `imp_k`, `imp_s`, `imp_peirce`, `imp_comp`, `imp_exchange`, `imp_refl`, and `rho8_all` (the restricted row without its side condition `u ≤ a`). |
| `PA194ModelContext` | `Ctx Γ a`: proof trees of standard size from a standard-length list `Γ` of model elements. `Ctx.deduction` (deduction theorem), `Ctx.generalize`, `Ctx.existsElim`, `Ctx.casesOnFormula`; `explosion`, `doubleNegationElimination`, `contraposition`; the vacuity rules `negationVacuity`, `implicationVacuity`, `universalVacuity`, `conjunctionVacuity`; `existentialMonotonicity`, `liftImp`; `memRight`, `memLeft`. |
| `PA194ModelNeighborhood` | The target-code neighborhood relation is reflexive, symmetric and transitive, and three corresponding universally closed source equality-supplier-shaped formulas are target-provable for arbitrary model labels. |
| `PA194ModelNeighborhoodDef` | The neighborhood and biconditional constructors are Σ₁-definable model functions, which permits their use in suitable internal induction predicates. |
| `PA194ModelNeighborhoodCode` | A fixed ternary candidate-PRA code for the neighborhood constructor has its stated value on arbitrary model inputs, including nonstandard labels, and agrees over the natural numbers with the existing source-LK neighborhood encoding. |
| `PA194ModelSourceAtomCode` | Candidate-PRA codes decode positive and negative source equality atoms and select bound/free labels from encoded environments, including for nonstandard terms and vectors. |
| `PA194ModelSourceEnvironment` | A finite code pushes a label onto the bound environment; its lookup equations have the head/tail behavior of the standard source translator's binder update. |
| `PA194ModelBoundAllocation` | A finite code reconstructs consecutive binder labels and the bound stack from a remaining depth budget, including at nonstandard depths. |
| `PA194ModelTranslationContext` | Finite PRA codes unpack the fixed history parameters and reconstruct the current bound environment and binder label from the remaining budget. |
| `PA194ModelMembershipAtomCode` | Candidate-PRA codes decode positive and negative source membership atoms, with the argument reversal used by the numerical calculus. |
| `PA194ModelFormulaDispatch` | A finite packed-history dispatcher satisfies model equations for the atomic, truth, Boolean and quantifier constructors. |
| `PA194ModelFormulaUniqueness` | Internal Σ₁ structural induction proves bounded and root agreement with any candidate-PRA comparison code satisfying explicit constructor recurrences. |
| `PA194ModelFormulaUniquenessF` | The same bounded/root uniqueness argument applies to a Σ₁-definable model function satisfying constructor equations on valid children. |
| `PA194ModelFormulaSpecification` | An independent Foundation structural recursion satisfies those equations, and agrees with the packed history on valid formulas at budgets at least the formula code. |
| `PA194ModelFormulaTranslation` | A finite candidate-PRA `Code 5` packages the root translation and agrees with the independent reference for all valid model formulas, including nonstandard codes. |
| `PA194ModelFormulaFreshness`, `PA194ModelEnvironmentFreshness` | Binder labels and bounded entries of reconstructed bound stacks are below a reserved label under explicit allocation and initial-stack bounds. |
| `PA194ModelSourceIndexBound`, `PA194ModelAtomicFreshness` | Source-atom variable indices are below the atom code, and the selected labels are fresh under explicit ceiling and environment bounds. |
| `PA194ModelSourcePath` | A finite PRA code follows source-formula child paths for arbitrary model-length step counts; visited node codes are bounded by the root. |

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

The binder update prepends `new` to the bound environment as `pair new old + 1`.
For arbitrary model indices it maps bound index zero to `new`, bound index
`i + 1` to the previous value at `i`, and leaves free-variable lookup unchanged.
This matches the head/tail behavior of `Fin.cases lo bound` in the ordinary
source `toNamed` translation. It does not establish a recursive translation of
internal formulas or its correctness under quantifiers.

`boundAtBudget` reconstructs the bound stack from fixed initial parameters and
truncated subtraction `ceiling - budget`. At the root, budget equals ceiling.
The binder equation assumes a positive parent budget `b + 1` with
`b + 1 ≤ ceiling` and shows that the child budget `b` pushes the current
label. If `ceiling < budget`, subtraction saturates at zero and the stack and
label revert to their initial values; no binder equation is asserted there.
The intended packed-history recursion must preserve the budget on Boolean
children and decrement it only at binders, as the existing formula-budget
machinery does. This module does not yet supply the new dispatcher, packed
parameter decoder, or the depth invariant needed for a recursive compiler.

The context codes take a history node indexed by `pair source remaining` and
two fixed parameters: `pair initialBound free` and
`pair initialBudget (pair initialLabel reservedLabel)`. Their model equations
decode those values and reconstruct the current bound stack and label for
arbitrary model inputs. They do not enforce formula well-formedness, budget
inequalities, or the dispatcher's requirement to preserve the budget on
Boolean children and decrement it only under quantifiers.

The membership decoder assumes source relation code `1` and an internally
valid arity-two term vector; the raw code does not validate these hypotheses.
It reverses the two source arguments in the target membership constructor.
The formula dispatcher uses the decoded atom and context codes. Its checked
history equations preserve the budget for Boolean children and use one less
for a quantified body, provided the parent budget is a successor. Its default
branch applies to any unrecognized tag, so interpreting that branch as an
existential requires source-constructor validity. Identifying the allocated
binder with the intended environment additionally requires the budget bound.
These local equations do not prove an independent recursive translation for
every internally valid source formula, its depth invariant, or proof transport.

For a fixed comparison code `spec`, fixed model parameters and bound `B`,
the uniqueness proof shows that `∀ b ≤ B, p ≤ b → history(p,b) = spec(p,b)`
is a Σ₁-definable predicate of `p`. Internal Σ₁ structural induction then
establishes it for every valid source-formula code, including nonstandard
codes, assuming the eight displayed atomic, truth, Boolean and quantifier
recurrences for `spec`. Taking `B = b = p` gives root agreement. The `p ≤ b`
condition is a conservative budget bound, not a claimed minimal depth bound.
The original comparison-code theorem takes its recurrence equations as
explicit hypotheses. The later `formulaReference` is a separate Foundation
`UformulaRec1` construction whose eight constructor equations are proved on
valid source syntax. Internal Σ₁ induction proves that `formulaHistory` agrees
with this reference whenever the formula code is at most the budget. The root
code `fixedFormulaTranslation` uses the source formula code itself as budget;
its value and fixed Σ₁ graph agree with the reference on every internally
valid source formula. It inherits the previously classically chosen Cantor and
projection code witnesses.

This establishes syntactic agreement only. Source syntax validity does not
assert de Bruijn scope and the environment lookups are total. No theorem here
identifies the reference on standard typed formulas with the existing host
`toNamed`/`relationalCode` translation. Semantic correctness of the
neighborhood-equality translation also requires
the reserved label to be fresh for the initial environments and all labels
allocated under binders. The constructor equations and source-syntax validity
do not by themselves establish that freshness invariant. `currentBinder_lt_reserved`
proves a binder label is strictly below the reserve when the parent budget is
positive, bounded by the ceiling, and `base + ceiling ≤ reserve`. Internal
Σ₁ induction proves the same strict bound for entries at indices at most the
ceiling in reconstructed bound stacks, assuming it for the initial stack and
that the number of entered binders is at most the ceiling.

For any internally valid arity-two source atom, every bound/free index in its
two terms is strictly below the numeric atom code. If that code is at most the
ceiling, both selected labels are below the reserve under the bound-stack
invariant and a separate strict bound on free-stack entries. These statements
do not establish the initial or free-stack bounds, propagate the atom-code bound
through every node of a compound formula, or prove semantic preservation. PA
proof transport and the physical machine correspondence remain open.

`sourcePath` iterates a finite child-selection code using choices from an
encoded stack. Boolean tags select one child, quantifier tags select the body,
and atomic/truth/falsity or unrecognized tags stay at the current node.
Internal Σ₁ induction proves every visited node is at most the root, even for
nonstandard step counts. At a visited valid source atom, its variable indices
are therefore below the root, and its labels are fresh under the explicit
initial-bound/free-stack bounds, `base + root ≤ reserve`, and a separately
supplied allocation depth `n ≤ root`. No theorem yet shows every internal
syntactic subformula is reachable by a coded path or identifies `n` with the
number of binders traversed.

The entries of a context and the parameters of every theorem are arbitrary elements of `M`,
so they cover nonstandard formula codes. What is standard is the shape of each derivation.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check.sh [--out DIR]
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with
`PA194ModelSourcePath` as the top module. On 2026-11-14, all twenty modules in
this directory were rebuilt against a retained combined overlay.
Their printed axiom reports were free of `sorryAx`. The
overlay contains previously checked Foundation, project and standalone
prerequisites; these were suffix checks, not empty-overlay replays.
