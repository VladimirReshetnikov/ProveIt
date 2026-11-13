# Conditional saturation-to-guard draft

This source combines `ArithmeticSaturation.saturation` and `ArithmeticRankForcing.noCarry_add_lt`. It assumes the same model values, `q=Exp.exp u`, `C>0`, the explicit bounds `C-1<q`, `F<q`, `MC*J+1<q`, `F<=MC*J`, the stated natural four-block equation, and both stated population inequalities. It proposes both no-carry conclusions and `F+C<q`.

These are **hypotheses**, not consequences yet derived from a 74 graph zero. The separate [all-ring identity](../trace74-direct-four-block-rebuild/README.md) has an author Lean check, but does not establish the natural truncated-subtraction equation or any of these bounds. The existing 75 saturation proof uses the reverse guard and cannot be used to discharge them circularly. The author Lean check passed; the [independent post-run review](../../reviews/trace74-conditional-saturation-guard-result-independent/README.md) passed. No fixed-BFS guard, graph equivalence or iPRA result is asserted.

The [independent source review](../../reviews/trace74-conditional-saturation-guard-draft-independent/README.md) verified the stated hypotheses, same parameters and inequality direction; it did not run Lean.
