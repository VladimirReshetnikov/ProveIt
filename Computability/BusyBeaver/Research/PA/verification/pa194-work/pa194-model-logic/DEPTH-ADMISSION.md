# PA194 partial derivation admissibility

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
itself remains incomplete: it needs internal inductions over derivations, formula codes and
sequents of nonstandard length, as well as the remaining rule simulations and axiom
suppliers. Nothing here yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `PA194ModelPropositional` | The upstream generic derivation `M6.Logic.RestrictedImplication` instantiated with `M`, `impValue` and `TargetProvable`: `imp_k`, `imp_s`, `imp_peirce`, `imp_comp`, `imp_exchange`, `imp_refl`, and `rho8_all` (the restricted row without its side condition `u ≤ a`). |
| `PA194ModelContext` | `Ctx Γ a`: proof trees of standard size from a standard-length list `Γ` of model elements. `Ctx.deduction` (deduction theorem), `Ctx.generalize`, `Ctx.existsElim`, `Ctx.casesOnFormula`; `explosion`, `doubleNegationElimination`, `contraposition`; the vacuity rules `negationVacuity`, `implicationVacuity`, `universalVacuity`, `conjunctionVacuity`; `existentialMonotonicity`, `liftImp`; `memRight`, `memLeft`. |
| `PA194ModelNeighborhood` | The target-code neighborhood relation is reflexive, symmetric and transitive, and three corresponding universally closed source equality-supplier-shaped formulas are target-provable for arbitrary model labels. |

These are fixed-size proof transformations parameterized by arbitrary elements of `M`,
not an internal induction over source proof codes. The formulas have the same displayed
shape as the ordinary-number source-LK equality suppliers, but no theorem here identifies
them with the translation of internal source-formula codes. The latter connection and the
internal compiler remain open.

The entries of a context and the parameters of every theorem are arbitrary elements of `M`,
so they cover nonstandard formula codes. What is standard is the shape of each derivation.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check.sh [--out DIR]
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with `PA194ModelNeighborhood` as
the top module. On 2026-11-14, with `--out` pointing at the object directory that already
held the compiled closure, it recompiled the prior two modules and printed seven
axiom reports, all `propext`, `Classical.choice`, `Quot.sound`. A run into an empty directory
has not been done.

The neighborhood module was checked with `check_bridge.py` using the new module as its
top, `--reports 9`, and a retained combined overlay. The checker recompiled the top module against retained prerequisite objects, with all nine printed
axiom reports free of `sorryAx`. The combined overlay includes the audited Foundation,
project and standalone prerequisites; this is a suffix check, not an empty-overlay replay.

`partialInitialEnvironment bound d` supplies a concrete initial candidate: its free stack is empty, its base is 1, and its reserve is `1 + (d + 1)`. The theorem `partialAdmission_initial` establishes `PartialAdmission B ... d` for every `B`. This does not supply a common environment-code bound, prove arbitrary pop or shift preservation, or complete a compiler instance.

The ranked and linear environment invariants apply in an arbitrary model of candidate PRA + IΣ₁, including nonstandard stacks. `RankedEnvironment e` requires the stack length plus one to be at most the base and each entry plus its one-based index to be at most the base. It is Π₁-definable, holds at `partialInitialEnvironment`, is preserved and reflected by pushing, and yields every lookup strictly below the base, including lookups beyond the stack length. `RankedAdmission e d` combines this invariant with `base + (d + 1) ≤ reserve`; it is Π₁-definable and has the displayed child, pushed-child, equality-reserve, and closed-atomic freshness consequences.

`LinearEnvironment e` strengthens each ranked entry inequality to equality. It is Π₁-definable, holds initially, is preserved and reflected by push, and implies the ranked invariant. If the free stack is nonempty, popping preserves linearity and pushing the pop reconstructs the exact input environment; therefore it lies in the push image. The nonempty hypothesis is essential to that argument. The results do not establish nonemptiness at shift nodes, a bound on environment codes, all universal/shift simulation fields, or a complete compiler instance.

`linearSeed bound reserve n` uses the existing model-interpreted `allocateBound` function to create a free stack of `n` consecutive labels, including for nonstandard `n`. `linearSeed_succ` identifies the next seed with `simPushFree`; `linearSeed_properties` proves linearity and exact stack length by an internally Σ₁-definable induction.

`DepthAdmission e d` requires `LinearEnvironment e`, `d + 1 ≤ len (simFree e)`, and `simBase e + (d + 1) ≤ simReserve e`. It is Π₁-definable, implies `RankedAdmission`, and holds for an explicitly constructed seed with stack length `d + 1` and matching reserve. For every child `< d`, it is preserved under the same, pushed, and popped environment. The pop proof uses the depth condition to establish a nonempty stack and then the exact push/pop inverse from linearity. These facts hold in arbitrary candidate-PRA + IΣ₁ models, not just standard codes.

This is not a compiler instance: the work has not proved a single uniform bound on all environment codes, nor all simulation fields for shift, substitution, freshness, and theory axioms. The seed supplies depth but does not by itself supply those properties.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-depth-admission.sh --out DIR` with matching retained prerequisites.

In an arbitrary candidate-PRA + IΣ₁ model, `sigmaFunction_boundedRange` proves that any Σ₁-definable total unary function has a common bound on a model-valued initial segment. Its Σ₁-induction step takes a common bound for the previous values and adds the new value. Applied to the internally coded environment function, `linearSeed_boundedRange` bounds the complete seed codes for each fixed bound-stack field and reserve, over any specified model-valued index range.

`SeedEnvironment e` states that `e` equals its canonical `linearSeed` at the length of its free stack. It is Π₁-definable, holds for every seed, implies the linear invariant, and is preserved by push and, under `DepthAdmission`, by pop. For fixed `bound` and `reserve`, `SeedAdmission bound reserve e d` combines that invariant, `DepthAdmission e d`, and equality of those two fixed fields. It is Π₁-definable; an explicit seed is initially admitted; and admission is inherited by every strictly smaller child in the unchanged, pushed, and popped environment. `seedAdmission_uniformBound` obtains one model-valued code bound for all `e,d` satisfying the same fixed-parameter admission: the reserve bounds the stack length, and the bounded-range theorem bounds the corresponding seed codes.

These results provide the structural and environment-bound ingredients for a concrete compiler admission. No complete compiler or consistency implication follows here: general target logical and source-theory axiom simulation fields remain to be proved. In particular the finite equality-theory supplier does not supply all PA axioms.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-seed-admission.sh --out DIR` with matching retained prerequisites.
## Compiler admission bundle

`SeedCompilerAdmission bound reserve` packages the seven structural admission
inheritance obligations used by the `CutValidity.Sim` compiler, including a
single bound on admitted environment codes. `seedCompilerAdmission_exists`
constructs the bundle for arbitrary model-valued parameters. The seed
admission predicate is Π₁-definable, and `seedAdmission_initial` gives an
explicit starting seed for a suitable reserve.

This bundle is not a `Sim` instance or a consistency implication. The
remaining obligations include quantified and substitution rule simulations
and suppliers for the non-equality PA axioms.

