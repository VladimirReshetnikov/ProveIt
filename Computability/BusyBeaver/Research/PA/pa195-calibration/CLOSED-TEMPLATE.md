# Closing fixed PA194 formula templates

`PA194ClosedTemplate.lean` statically compiles any externally fixed arithmetic
formula template with two outer placeholders into a primitive-recursive code.
Given a label and two model-valued source labels, it closes the selected label
under every internal binder and retains the other label as free. Theorems
`modelTermCode` and `modelFormulaCode` prove the output agrees with an explicit
numeric structural specification in every candidate-PRA model. In particular,
all three labels may be nonstandard; the template and binder depths in its
source syntax are standard and fixed externally.

`modelBitCloseQuote` and `modelNegativeBitCloseQuote` apply this to the exact
bounded bit formula and its negation. For standard labels, they identify the
numeric output with the Foundation quote of the actual capture-avoiding
`closeLabel` rewrite. These quote theorems additionally assume IΣ₁, as required
by the current Foundation syntax interpretation. The first template argument
is Foundation's bit index and the second its containing number; for PA194's
membership `M(a,b)`, these are `b` and `a`, respectively.

This is not a runtime traversal of arbitrary or nonstandard formula syntax,
not the general `close` function required by the recursive translator, and not
an iPRA machine-consistency implication. No numeric serialization or size
bound for the resulting primitive-recursive codes is claimed. Recheck with:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/Foundation/objects \
  Computability/BusyBeaver/Research/PA/pa195-calibration/check-closed-template.sh
```
