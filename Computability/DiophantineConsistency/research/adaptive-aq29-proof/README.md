# Twenty-nine-variable degree-eight reduction

`AdaptiveAQ29.shifted_no_zero_iff` compares the 29- and 30-variable shifted literals in every IΣ₁ model, for arbitrary integer port vectors. The parent-to-candidate map deletes the named f-square coordinate using its defining residual; the reverse map computes `f*f`, which is positive because the original f coordinate is positive. The transport checks all remaining residuals and the removed square constraint.

`verify_literal.py` checks all 135 Lean gates against the pinned candidate graph. The six-module model replay completed with byte-matched author and peer rows, and its receipt was independently audited at the time; see `reviews/adaptive-aq29-model-replay`. This is a historical point-in-time result, not a claim that the provider files remain available.

The native theorem and replay driver are prepared, but the guarded native replay did not pass. Its first Lean invocation exited with an error because the inherited package provider's `Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean` symlink points to a missing file under `/home/codex/src/Proofs/.lake/build/lib/lean`. The failed attempt is preserved in `reviews/adaptive-aq29-native-replay`; no native equivalence result is claimed from it. Restoring or rebuilding a properly verified provider is required before another replay.

The selected parent inherits historical transitive project and package ancestry and dynamic imports. The focused replay does not establish a fully current-source closure or identify the chosen native theory with every standard iPRA presentation.
