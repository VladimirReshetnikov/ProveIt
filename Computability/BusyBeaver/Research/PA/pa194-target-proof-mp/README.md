# Concrete target modus-ponens closure

`PA194TargetVectorJoin.lean` proves `mp_closed`: in every candidate-PRA model
whose arithmetic reduct satisfies IΣ₁, the concrete `TargetProvable` relation
is closed under the numerical target calculus's modus-ponens rule, including
for nonstandard formulas and proof vectors. The proof obtains a vector with
both programs as consecutive segments by Foundation's internal Σ₁
Skolem-vector theorem. It uses an internal IΣ₁ induction and the accepted-line
replay theorem to preserve the second program's accepted results after the
first is prepended, and then appends an MP line with reverse offsets to the two
results. Rejected lines are not assumed to remain rejected.

`targetHistory_closed` instantiates the earlier conditional target-history
invariant with the concrete Σ₁ target provability predicate. All its head1,
MP, generalization and remaining leaf closure premises are discharged in
Lean; every accepted history entry in every covered model is therefore
`TargetProvable` in this independent encoding.

The joined proof vector is supplied by model-level Σ₁ Skolemization. This
package does not construct a fixed finite candidate-PRA code for the proof
transformation. The independent line encoding is not yet identified with the
upstream certificate format, and source-proof compilation and machine/calculus
calibration remain open. These theorems alone do not prove a PA194/Con(PA)
implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-proof-mp/check.sh
```

The final module was rebuilt against the freshly rebuilt accepted-line replay
module and previously checked history suffix. A full nested replay of this
wrapper has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.

An independent suffix replay recompiled the target proof-join and MP-closure
module against separately checked target replay and leaf objects, reusing
remaining prerequisite overlays. Its reported theorem axioms did not include
`sorryAx`; the full nested replay remains separate.
