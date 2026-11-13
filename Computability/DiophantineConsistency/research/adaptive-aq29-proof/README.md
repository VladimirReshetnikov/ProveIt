# Twenty-nine-variable degree-eight reduction

`AdaptiveAQ29.shifted_no_zero_iff` compares the 29- and 30-variable shifted literals in every IΣ₁ model, for arbitrary integer port vectors. The parent-to-candidate map deletes the named f-square coordinate using its defining residual; the reverse map computes `f*f`, which is positive because the original f coordinate is positive. The transport checks all remaining residuals and the removed square constraint.

`verify_literal.py` checks all 135 Lean gates against the pinned candidate graph. The six-module model replay completed with byte-matched author and peer rows, and its receipt was independently audited at the time; see `reviews/adaptive-aq29-model-replay`. This is a historical point-in-time result, not a claim that the provider files remain available.

The initial focused native replay failed before its first Lean module because
the inherited package provider's `Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean`
symlink points to a missing file. That attempt remains in
`reviews/adaptive-aq29-native-replay`. On a subsequently rebuilt Foundation
provider, the [fresh project-source pair](../../reviews/fresh-project-pair-terminal/README.md)
completed and matched all 1,210 modules including the native endpoint. Its
[independent artifact audit](../../reviews/fresh-project-pair-independent-audit/README.md)
passed. It is a historical snapshot with 15 workspace-source drifts, and the
Foundation build wrapper's outer exit was not observed.

The fresh pair inherits package-transitive and dynamic ancestry. It does not establish a fully current-source closure or identify the chosen native theory with every standard iPRA presentation.
