# Source review: quartic-40 model transport

This review inspects the six author-compiled `AdaptiveQM40` context, zero,
map, norm, model and check modules from the
[bounded replay](../adaptive-qm40-native-bounded-replay/README.md), together
with their square-divisibility and quotient interfaces. No defect was found in
the inspected witness transport. This is a source review and finite index
check, not an independent Lean replay or a validation of every transitive
arithmetic dependency.

For the forward map, old coordinates 24 and 30 satisfy
`old24² = old15² * (1+old34)`; the source obtains this from old residuals 1
and 21. Strict positivity gives `old15>0`, so the model-level
`scaled_quotient` theorem provides `old24=old15*t` and `t²=1+old34`.
Positivity of `old24` then gives `t>0`. The projection places `t` in new
coordinate 24, drops old coordinate 30, and shifts later coordinates down;
new coordinate 33 is old coordinate 34. The common residuals agree under the
substitution `old24 ↦ new15*new24`, and the new norm supplies residual 1.

The reverse map replaces old coordinate 24 by `new15*new24` and old
coordinate 30 by `new15²`, preserving all other coordinates with the inverse
shift. The new norm then makes old residual 1 zero; old residual 21 vanishes
by construction. Products of positive model elements remain positive. The
sum-of-squares zero lemmas cover every individual residual, and the two
30-element index maps cover precisely all remaining indices: the old 32
except 1 and 21, and the new 31 except 1. Both directions then translate
positive witnesses to natural tuples for the `positiveShift` expressions by
subtracting one only after establishing positivity.

The model assumptions in these results are an `ORingStructure` satisfying
IΣ₁, and the four ports are arbitrary integers. The imported
`dvd_of_square_dvd` theorem itself uses a model-level Bézout-gcd construction;
the review does not independently replay that transitive proof. The target is
the **no-zero equivalence**, not equivalence of the raw existential witness
formulas without the explicit positivity and shifts.

[`audit.py`](audit.py) pins the workspace and author snapshot sources, checks
the two residual index ranges and the 39 unchanged-coordinate positions,
checks a positive sample of both maps, and invokes the existing external
166-row literal/DAG comparison. It rejects optimized Python. The sample is
not a substitute for the all-model Lean argument; the literal/DAG comparison
is an external source-text check and does not give a Lean semantics of a PDF
or authenticate its displayed coefficients.

The bounded author run compiled all six model-side modules and recorded the
model theorem's axiom report without `sorryAx`; it then timed out on the
native client, so that run has no completed native endpoint or peer replay.
A later retry, if any, requires its own terminal evidence and is outside this
review. The first run's sampled hashes and direct-provider guards inherit the
documented historical, package, transitive, dynamic and between-check limits.
The iPRA theorem and the particular displayed equation require their own
successful native/provider and display bindings.
