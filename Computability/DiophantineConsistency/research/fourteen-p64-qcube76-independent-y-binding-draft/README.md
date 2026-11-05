# Checked independent-`y` ring binding

`P64QCube76YBinding.lean` proves residual and output equalities between the
76 independent-`y` and 77 graphs over an arbitrary commutative ring. It
expresses the parent signed auxiliary carrier `V` by `oldV`, and updates
coordinate 12 to `V+e`; it also proves invariance of the 76 auxiliary
residual and output when that coordinate is replaced by another value with
the same square.

The source passed a [bounded guarded Lean check](../p64-qcube76y-binding-guarded-check/README.md):
all eight declarations reported `[propext]`, with no warnings or `sorryAx`.
It proves these ring equalities; positivity of witnesses, zero-existence
equivalence and an iPRA endpoint require additional results. Captured-provider
ancestry remains inherited.

Source SHA-256:
`917aece0aa983dcd5947baed77eb80725d3f99e2b4fd5ca4cac0901c1adadfc6`.
