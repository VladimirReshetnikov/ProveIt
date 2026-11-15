# Logic of the numerical calculus, in models of IΣ₁

The direction `¬Halt(M₁₉₄) → Con(PA)` needs, inside a model, a derivation of the
contradiction code in the separate-diagonal numerical calculus from an internal first-order
proof. The ordinary-number version of that compiler is
[`pa194-reverse-rewrite`](../pa194-reverse-rewrite), [`pa194-source-calculus`](../pa194-source-calculus),
[`pa194-source-lk`](../pa194-source-lk) and [`pa194-foundation-lk`](../pa194-foundation-lk/README.md).
This directory rebuilds it for `TargetProvable`, the provability predicate of the calculus in
a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`.

**Status.** The implication basis, context machinery and formula-translation recursion
are checked, including for nonstandard codes. The
[general seeded freshness field](GENERAL-FRESHNESS.md) and
[general shift rules](SHIFT-INTERFACE.md) are proved in PRA models with an IΣ₁
arithmetic reduct. The [unrestricted universal-introduction rule](UNRESTRICTED-ALL.md)
has passed a repository source-closure replay for arbitrary internal formula depth.
The unrestricted existential rule and finite-adjunctive compiler simulation have
independent replays and await repository integration. Identification of the source
theory with PA remains open. None of these results is a native iPRA consistency implication. The detailed
module descriptions below include earlier stages of the development; consult the
linked individual status notes for later results and their audit provenance.

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
| `PA194ModelSourcePathDepth` | A finite code counts binders actually traversed by such a path; the visited node plus the count is bounded by the root. |
| `PA194ModelSourcePathValidity` | Every visited node of a valid source formula remains valid, including at nonstandard path lengths. |
| `PA194ModelPathBudget` | At remaining budget `root − binderCount`, the dispatcher allocation agrees with the path's binder count. |
| `PA194ModelPathDispatch`, `PA194ModelPathDispatcherFresh` | Selected Boolean and binder edges satisfy dispatcher equations at their path budgets, and visited valid atoms have fresh labels under explicit environment bounds. |
| `PA194ModelPathPrepend` | Prefixing a choice to a model-length path follows that edge and then continues through the former choice stack. |
| `PA194ModelPathPrependDepth` | Prefixing a choice adds the parent’s binder bit to the path’s binder count. |
| `PA194ModelPathReachability`, `PA194ModelPathReachabilityDef` | Operational path reachability with binder depth is reflexive, extends by a parent edge, and is uniformly Σ₁ in root, target, and depth. |
| `PA194ModelDirectEdge`, `PA194ModelSourceChain` | Independently coded chains of source-child edges give operational paths, including for model-valued chain lengths. |
| `PA194ModelSyntacticDescendant` | The chain-based descendant relation is reflexive, closed under direct edges, covered by paths, and preserves formula validity. |
| `PA194ModelSourceChainDepth` | A separately coded sum of the chain’s binder bits equals the operational path depth. |
| `PA194ModelDescendantComplexity` | The independent edge, chain, and descendant relations are uniformly Σ₁-definable. |
| `PA194ModelRecursorOccurrence` | The actual Foundation formula-reference equations expose immediate child descendants with their binder depths. |
| `PA194ModelRecursorChain`, `PA194ModelRecursorGraph` | A newly specified recursion chain has exact depth and budget change; actual Foundation graph inversions supply its immediate edges. |
| `PA194ModelPathBudgetPositive`, `PA194ModelPathGraph` | Visited binders have positive remaining budget, and every chosen path node has an actual Foundation graph entry. |
| `PA194ModelPathReferenceStep` | Every path step from valid syntax is either a stationary leaf or a reference edge with actual graph entries at both ends. |
| `PA194ModelEqualityObservations` | Translated equality atoms derive four quantified neighborhood observations in the target calculus. |
| `PA194ModelPathAtomSubstitution` and dependencies | [Target membership substitution](SUBSTITUTION.md) follows for suitably bounded equal-depth source paths with explicit environment bounds. |
| `PA194RelExtTypedTranslation`, `PA194ModelBinaryRelationSubstitution` | [Foundation relation extensionality](REL-EXT.md) has an exact standard syntax translation and a matching model-uniform target proof shape. |
| `PA194ModelEqRefl` | The [actual Foundation reflexivity axiom](EQ-REFL.md) has a target-provable internal translation. |
| `PA194ModelEqSymm` | The [actual Foundation symmetry axiom](EQ-SYMM.md) has a target-provable internal translation. |
| `PA194ModelEqTrans`, `PA194ModelEqRelExt` | The [transitivity](EQ-TRANS.md) and [equality-relation extensionality](EQ-REL-EXT.md) axioms have target-provable internal translations. |

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
initial-bound/free-stack bounds and `base + root ≤ reserve`. A finite binder
counter, using the same choice stack, counts exactly the quantifier tags
traversed. Internal Σ₁ induction proves that the visited node plus this count
is at most the root, including at nonstandard step counts. This supplies the
allocation-depth bound for freshness at a visited valid atom. No theorem yet
shows every internal syntactic subformula is reachable by a coded path. A
separate internal induction proves that every visited node of a valid root
remains valid. At remaining budget `root − binderCount`, the reconstructed
bound stack and current label equal allocation at that count; the next path
step leaves the budget unchanged at a nonbinder and decreases it by one at a
binder. The six single-edge dispatcher equations identify the selected
Boolean child or binder body with that next node and budget, retaining the
other Boolean child in its proper position. They are equations for values of
the packed-history code, not a runtime call-stack theorem. At a visited valid
atom, the selected labels in the initialized dispatcher context are fresh
under the stated reserve and initial-bound/free-stack hypotheses.

For arbitrary model-valued path lengths, prefixing a choice to the encoded
stack follows the corresponding first edge and then the old path; this uses
internal Σ₁ induction. The binder count of the prefixed path equals the parent’s
binder bit plus the count of the remaining path. Operational `PathWithDepth`
records an endpoint and binder count, has a zero-step witness, and extends by a
parent edge. A finite code packs the step count and choice stack into one witness;
this gives uniform Σ₁ definability in root, target, and depth. A separate relation defines each direct edge from the source constructors, and
a model-coded chain requires each adjacent node pair to satisfy this relation.
Internal Σ₁ induction converts every such chain, including nonstandard-length
chains, into an operational path with some binder depth; a valid source root
gives a valid target. The resulting explicitly chain-defined descendant relation
is reflexive, closed under direct edges, covered by operational paths, and
preserves formula validity. A finite PRA code independently sums binder bits along
the chain, and internal induction gives an operational path at exactly this depth,
including for nonstandard-length chains. The independent edge, chain, descendant,
and exact-depth descendant relations are uniformly Σ₁-definable; existentially
quantifying the depth recovers the ungraded descendant relation. This does not
identify the relation with a separately defined
Foundation subformula predicate, prove that the translator visits every such
node, or establish semantic correctness of the translation. For each valid
Boolean or binder constructor, the actual Foundation `formulaReference`
recurrence equation now has independently chain-defined witnesses for its
immediate recursive child inputs, with depth zero for Boolean edges and one
for binders. This is a local result, not a theorem covering an entire
nonstandard Foundation recursion history. A newly specified chain of valid
reference edges has exact binder depth and budget change even at nonstandard
lengths. Actual Foundation graph inversions expose the corresponding immediate
Boolean child graphs and positive-budget binder body graphs. Every path from a
valid root has actual Foundation graph entries at its visited nodes and
root-derived budgets; visited binder budgets are positive, and their next nodes
and budgets match the graph inversions. The converse extraction of paths or
chains from arbitrary Foundation fixpoint witnesses remains open. Every path
step from valid syntax is either a stationary leaf with unchanged budget or a
reference edge, with actual Foundation graph entries at both endpoints.
The target calculus also derives all four quantified neighborhood membership
implications from a translated equality atom, uniformly for internally valid
source term vectors and model-valued labels. Arbitrary-label specialization
and membership substitution remain separate obligations.

The entries of a context and the parameters of every theorem are arbitrary elements of `M`,
so they cover nonstandard formula codes. What is standard is the shape of each derivation.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check.sh [--out DIR]
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with
`PA194ModelGraphAudit` as the top module. On 2026-11-14, the path and
dispatcher modules were rebuilt against a retained combined overlay.
Their printed axiom reports were free of `sorryAx`. The
overlay contains previously checked Foundation, project and standalone
prerequisites; these were suffix checks, not empty-overlay replays.

The [numerical target sequent instance](SEQUENT-INSTANCE.md) connects the actual
fixed formula translation to nonstandard finite source sets; source proof-rule
simulation and derivation induction remain open.

The [finite equality-axiom sequent](EQ-SEQUENT.md) connects an explicit coded
axiom predicate to target sequents; its identity with an existing internal
source-theory predicate and general proof compilation remain open.

The [equality-theory axiom rule](SIM-AXIOM.md) uses an explicit Foundation
Δ₁ presentation and discharges the corresponding abstract compiler field under
a reserve bound; the remaining compiler rules and admissibility remain open.

The [sequent truth and weakening lemmas](SEQUENT-TRUTH.md) handle two source
rules for model-valued finite sets; the general initial axiom and remaining
rules still require additional translation facts.

The [propositional compiler rules](SIM-PROPOSITIONAL.md) discharge the actual
conjunction and disjunction Sim conclusions; other rules remain open.

The [binder context translation](BINDER-CONTEXT.md) derives exact quantified
constructor equations in candidate models; freshness, substitution, and the
compiler quantifier rules remain separate.

The [negation duality and refined cut interface](REFINED-CUT.md) handle
arbitrary internally valid formulas, but do not construct the complete
derivation simulation.

The [universal-rule atom fragments](UNIVERSAL-ATOM.md) cover both atom
polarities under explicit environment bounds, but nested binders and full
quantifier rules remain open.

The [depth-admission candidate](DEPTH-ADMISSION.md) supplies a model-valued
linear-stack seed and local preservation but does not yet bound environment
codes or construct a complete derivation simulation.
