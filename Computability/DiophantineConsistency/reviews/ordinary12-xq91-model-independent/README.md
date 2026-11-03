# Independent review of the 91-operation transformed model theorem

The checked `zero_iff_transformed` statement applies to every model `V` of
`IΣ₁`, every natural-valued four-port tuple and every 12-coordinate valuation
in that model, including nonstandard values. It equates zero of the 91 graph
at the given valuation with zero of the 92 graph after updating coordinate 5
from `w` to `X=(1+J*beta)*w`. The statement does not require positive
coordinates or positive beta.

The proof maps split-natural internal zero to evaluation in the ordered
difference ring. `lift_cast` identifies the natural-coordinate update with
the ring update, and the three earlier algebra theorems identify the first,
main and ordinary residuals exactly. Both graph outputs are the same sum of
squares of their respective residuals, so the zero equivalence follows by
rewriting. No nonzero-q hypothesis, square cancellation or positivity
argument is needed for this specified-valuation comparison. It does not
show that every positive 92-zero has an `X=q*w` quotient; the positive-zero
existence bridge remains separate.

The recorded author run exited zero with empty stderr, no warnings and no
`sorryAx`. Both named results report Lean metatheory axioms
`[propext, Classical.choice, Quot.sound]`. Its retained source snapshot,
output object and logs match the receipt. All 76 selected-provider files
were rehashed with resolved paths; the selected direct `XQ91` object is the
exact 91-algebra object from the earlier accepted run, and the earlier 75
selected provider records remain unchanged. Two recorded resource samples
saw two Lean processes and at least 18,256,628 KiB available memory.

Run `python3 -I -S -B check.py` from this directory, or give its path from
another directory. The read-only checker pins source, receipts and logs,
rehashes selected provider files before and after, and reruns the earlier
algebra and graph review. Its captured execution exited zero with empty
stderr; see `observations/stdout`. It requires the retained absolute `/tmp`
provider and output paths. No Lean process was started for this review.

The selected traversal does not cover all symlinked directories or complete
project, package-transitive or dynamic ancestry; historical source-to-object
provenance remains inherited. Resource samples are not continuous. This is an
inspection of one author build, not an independent Lean replay. The fixed-port
positive-existence bridge, internal iPRA endpoint and external coefficient
file/PDF bindings remain separate work.
