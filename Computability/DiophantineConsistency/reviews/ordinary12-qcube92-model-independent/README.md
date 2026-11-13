# Independent review of the 92-operation transformed model theorem

`zero_iff_transformed` states that, for any model `V` satisfying the recorded
`IΣ₁` hypothesis, any natural-valued four-port tuple, and any 12-coordinate
valuation in that model, the 92-expression is internally zero if and only if
the 94-expression is internally zero at the valuation obtained by replacing
coordinate 6 by `q³` times it. The theorem includes nonstandard model
valuations. It does not require positive coordinates or positive beta: with
natural port numerals and natural model values, `q = 1 + J*beta` is positive
even when `J` or beta is zero.

The proof uses the injective embedding into the model's ordered difference
ring to turn split-natural internal zeros into ring zeros. `lift_cast` matches
the natural-coordinate update with the ring-level update. The imported
algebra identities give old first residual `q⁶` times new first residual and
identify the other two residuals. `cube_ne_zero` proves `q³ ≠ 0`; the
`NoZeroDivisors` property permits cancellation. A separate three-square
lemma uses nonnegativity of each square to reduce a zero sum to three zero
residuals. These steps establish equivalence at the related valuations, not
existence equivalence for arbitrary positive old zeros: obtaining a positive
quotient remains a separate obligation.

The retained author run exited zero with empty stderr and no `sorryAx` or
warning; the three named results report Lean metatheory axioms
`[propext, Classical.choice, Quot.sound]`. Its retained source snapshot,
object and logs match the receipt. The direct imported `QCube92` object is
the exact object recorded by algebra attempt05. All 75 files in the selected
provider traversal currently match the receipt, including the 74-file
provider inherited from the algebra run. The independent algebra source and
graph audit was rerun successfully. Five recorded process samples saw at most
one Lean process and at least 18,488,796 KiB available memory.

Run `python3 -I -S -B check.py` from this directory, or pass its path from
another directory. The read-only checker pins the source, receipts and logs,
rechecks provider paths and hashes before and after, and runs the earlier
read-only algebra review. The captured output is in `observations/stdout`;
the review exited zero with empty stderr. It needs the original absolute
`/tmp` providers and output objects. No Lean process was started.

The selected-provider traversal does not cover all symlinked, transitive,
package or dynamic ancestry. These checks are a review of a single author
run, not a fresh kernel replay. The model theorem does not prove the quotient
existence direction, a JSON/TeX/PDF semantics theorem, or an internal iPRA
endpoint.
