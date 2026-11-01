# Superseded fixed-port coercion attempts

These scratch attempts do not support the checked theorem. A broad `simp` on the concrete port definitions unfolded a large exponent, emitted exponent-threshold and looping-simplifier warnings, and exited 1 at a recursion-depth error. A subsequent finite-case/definitional attempt grew to about 5.6 GB RSS while reducing the concrete ports; it was intentionally sent SIGTERM and its tool session exited 143. Neither was a successful proof or a guarded replay.

The replacement uses the existing `ArithmeticAdaptiveScaledNorms2011.currentPorts_cast` theorem to specialize the natural-port result, and compiled without those warnings. Exact scratch sources and terminal output were not preserved as a standalone log; this record describes the observed outcomes and does not claim a separate replay.
