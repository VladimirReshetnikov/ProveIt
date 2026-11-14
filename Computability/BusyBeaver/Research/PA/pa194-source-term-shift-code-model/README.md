# Candidate-PRA code for PA194 source term shift in all IΣ₁ models

`candidate first second` is an explicit finite candidate-PRA function-code
expression built from two projection codes, predecessor, pairing, successor,
and a selector. `candidate_correct` proves that, provided the two projection
codes satisfy their stated PRA certificates, its interpretation agrees with
Foundation's `termShift` on **every internally valid PA194 source term** in
every candidate-PRA model whose arithmetic reduct satisfies IΣ₁. The bound
and free variable cases include nonstandard variable codes.

The package discharges both projection-certificate premises using the existing
`PRA_has_pi1Code` and `PRA_has_pi2Code` theorems. `fixedTermShiftCode` uses
one classically chosen pair of such projection codes, fixed independently of
the model. `fixedTermShiftCode_correct` establishes the same all-model
agreement without open projection premises. `fixedGraph_correct` additionally
identifies the actual parameter-free Σ₁ graph of this very candidate-PRA code
with Foundation term shift on internally valid inputs.

A fresh tmpfs suffix replay rebuilt `PA194TermShiftModel`, `PA194BranchSeed`,
`PA194CodeGraph`, and the repository source in that dependency order against
the ordered source and term-graph development overlays, using the same
audited project and Foundation objects. The printed theorems report
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The full nested
two-chain standalone replay remains pending.

The projection codes are existentially certified and chosen classically, so
this is a fixed finite code but its full constructor tree is not printed. The
model agreement is proved only for inputs satisfying the internal source-term
recognizer. This is a term-level compiler component; full source formula shift,
nonstandard proof compilation, PA194 machine calibration and the desired
consistency equivalence remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited current
Foundation object overlay and `IPRA_LEAN_OVERLAY` to the pinned audited
project object overlay, then run
`bash Computability/BusyBeaver/Research/PA/pa194-source-term-shift-code-model/check.sh`.

An independent Lean invocation also recompiled the final module using that
same freshly rebuilt dependency overlay. It reported the same axioms and no
`sorryAx`; it did not independently rebuild the prerequisite chains.
