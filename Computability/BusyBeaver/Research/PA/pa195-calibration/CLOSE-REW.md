# Variable cases of capture-avoiding closure

`PA194CloseRew.lean` defines `closeDepthRew` by lifting the exact
`PA194BindTranslation.closeLabel` rewriting under a fixed, standard number of
binders. At depth zero it is the rewriting used by `closeLabel`. It proves
that every standard free variable maps to the selected bound variable when its
label matches, and otherwise remains free, and that each existing bound
variable below the standard binder depth remains unchanged.

Under an explicit IΣ₁ assumption on a candidate-PRA model,
`modelCloseFreeQuote` and `modelCloseBoundQuote` show that the represented
variable-operation codes return the Foundation quotes of these actual lifted
rewritings for standard labels and binder depths. Their numeric variable-case
equations in arbitrary candidate-PRA models, including nonstandard indices and
depths, are proved separately in `PA194CloseVariable.lean`.

This is not a code for closing an arbitrary formula. It does not cover the
recursive traversal of function terms, vectors, and formula trees, does not
connect the represented codes to rewriting of nonstandard syntax, and does
not establish PA calibration or a machine-consistency implication. Recheck
with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-close-rew.sh
```
