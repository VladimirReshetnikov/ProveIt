# Abstract proof-enumerator equivalence

`Enum254.enum_halts_iff` proves that the abstract six-register enumerator
halts from its all-zero state exactly when falsity code 1 is derivable in
`Code254.C254`. The module arrived in repository commit `0e3b7b0caf`.
Its main theorem has no model-existence, consistency or simulation premise.
The paired numerical bridge also yields `Enum254.Halts ↔ Numeric254.NumThm 1`.

The new Lean definitions were compared directly with the frozen upstream
`ZF/m254/coq/logic/Enum254.v`, pin
`297ab8df7e5de329605c3875b4934643b371a5e3`, from Jeff's verification of
Mira-Cult's machine. All six persistent fields, MP/DROP/NIP/AX selectors,
parameter additions, stack push order, gates, candidate fetch and halting
convention agree. This is an inspected source correspondence, not a Lean
simulation of the actual `Prog254` instruction list or binary table.

Soundness uses derivability of the current and cached formulas and every
entry of the infinite zero-padded stack. Successful MP pushes truth code 0;
AX emits the exact original rows, generalization and gated bundle. The only
halting transition is NIP with cache 1.

Completeness constructs command blocks for all twelve proof constructors.
A block either halts early or returns its target theorem while preserving
the old stack and resetting the parameter/cache. This disjunction handles
intermediate derivations of falsity without assuming they execute onward.
The initial AX reset makes the final halting command list work from arbitrary
retained registers; candidate boundaries do not silently clear them.
Continuation pointers use the exact `+1` encoding, and a nonzero pointer
strictly decreases. Every candidate is therefore reached **unless an earlier
candidate halts**. Neither an unproved fair search nor a finite execution
sample substitutes for this argument.

## Correction to the final model corollary

The delivered `halts_of_no_model` retained the old premise

```text
∀ D mem, IR mem → ModelsEncodable mem → False
```

without a valuation. That premise is refuted by the empty-domain model,
already recorded as the axiom-free `Code254.empty_domain_counterexample`.
It also fails to typecheck against the corrected `c254_complete` interface.
The original source was checked unchanged in scratch: its only error is the
final application of that incompatible premise. The original commit, full
compiler error and source location are preserved in the integration evidence.

The corrected corollary requires

```text
∀ D mem, IR mem → ModelsEncodable mem → (Nat → D) → False
```

and now compiles. This fixes the model corollary; it leaves the core
`enum_halts_iff` proof unchanged. A caller with the corrected explicit
valuation interface and the existing empty-domain counterexample both pass.
The misleading unconditional wording about reaching every candidate was
also narrowed to the reached-or-already-halted statement actually proved.

## Verification and remaining scope

The corrected source, `QuotientSeparation` and the complete updated umbrella
were checked serially with the explicit Lean 4.32.0 executable, reusing the
previously source-verified 62-module cache. The default runner now has 64
source units. Eleven selected axiom audits and three composition callers
pass; dependencies use only the usual `propext`, `Classical.choice` and
`Quot.sound`. The empty-domain counterexample remains axiom-free.
Commands, timings, exact source identities, original failed compiler output
and final audit/caller source are in
`results/enum-separation-integration-verification.json`.

An independent full-source review found no further defect in the abstract
interface, stack invariant, candidate descent or completeness construction.
This closes the abstract enumerator-versus-numerical-derivability step.
Its simulation by the literal register program, full binary runtime and
bootstrap linkage, and the internal ZFC consistency calibration remain
separate obligations. No new state count follows from this theorem alone.
