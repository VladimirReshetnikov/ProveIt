# Membership and bit argument order

The PA194 source and Foundation's bit graph use opposite argument orders.
For source code `M(a,b)`, the intended reading in the calibration is that
`b` is an element of `a`: the first argument is the container and the second
is the element. The source separation head binds `b` while using `M(a,b)`
and `M(c,b)` in the matrix; see
[`PA196/Commands/Code.lean:39`](../jamesyc-upstream/pa196/PA196/Commands/Code.lean#L39)
through line 43. The retained PA194 report writes the corresponding bounded
separation matrix as `Bit(x_a,z)` at
[`report/calibration.tex:152`](../docs/pa194_conpa_2026-11-13/report/calibration.tex#L152)
through line 156. This is evidence for the intended convention; the cited
source definitions themselves are numeric syntax, not a proved semantic
interpretation.

The report defines `Bit(s,z)` with container `s` and bit index `z` at
[`report/calibration.tex:126`](../docs/pa194_conpa_2026-11-13/report/calibration.tex#L126)
through line 131, and uses `Bit(x_a,x_b)` for `M(a,b)`. Those two report
statements are consistent with the source convention above.

Foundation uses `Bit(i,a)` with bit index `i` and container `a` and defines
`bitDef` in that same order; see
[`Exponential/Bit.lean:25`](../jamesyc-upstream/pa196/vendor/Foundation/Foundation/FirstOrder/Arithmetic/Exponential/Bit.lean#L25)
through line 31. The current `bitTemplateCode` compiles Foundation's
`bitDef` with its two inputs in Foundation order. Therefore the intended
PA194 membership branch must pass it the decoded source fields in **reversed
order**: for `M(a,b)`, call `bitTemplateCode(b,a)`.

This is an interface requirement, not a completed correctness claim: the
source-to-arithmetic translator, its binding to the exact PA194 machine, and
the weak-arithmetic proof of that correspondence remain open.
