# Candidate-PRA code for PA194 source formula shift in IΣ₁ models

`fixedFormulaShiftCode` is one finite candidate-PRA function code assembled
from the previously certified source atomic shift and a packed recursive
history. Its two projection-code witnesses are chosen once independently of
the model, and their PRA certificates are discharged.

`fixedFormulaShiftCode_correct` proves that, in every candidate-PRA model whose
arithmetic reduct satisfies IΣ₁, the code's model interpretation agrees with
Foundation's `shift` on **every internally valid PA194 source formula**. This
includes nonstandard formula codes. `fixedFormulaShiftGraph_correct` proves the
same equation for the actual fixed parameter-free Σ₁ graph of that code.

The proof checks the source-specific atom, truth/falsity, Boolean, and
quantifier equations for a single history dispatcher. Quantifier bodies use
the same auxiliary packed budget as their parent; their strictly smaller
formula code makes the history lookup valid. The proof of `history_correct`
uses **internal Σ₁ structural induction** over the recognized model formula,
not external induction over nonstandard formulas. It works for arbitrary
internal values of the auxiliary history parameters.

The fixed finite code includes classically chosen existential projection-code
witnesses, so its complete constructor tree is not printed. The model theorem
requires the internal `IsUFormula` validity hypothesis, candidate-PRA model
axioms and the IΣ₁ arithmetic reduct. It does not yet prove full nonstandard
LK proof compilation, PA194 machine calibration, or either desired
consistency implication.

A fresh ordered tmpfs suffix replay rebuilt `PA194FormulaBudget`,
`PA194FormulaUpdate`, the term, vector and atom shift code modules, and this
package in dependency order against the audited source and history overlays.
All printed theorems report `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`. The full nested two-chain standalone replay also passed with the audited
overlays.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited current
Foundation object overlay and `IPRA_LEAN_OVERLAY` to the pinned audited
project object overlay, then run
`bash Computability/BusyBeaver/Research/PA/pa194-source-formula-shift-code-model/check.sh`.

An independent Lean invocation also recompiled the final source-shift module
against the same freshly rebuilt suffix dependencies, with the same axiom
report and no `sorryAx`. That invocation did not rebuild the full prerequisite
chains.
