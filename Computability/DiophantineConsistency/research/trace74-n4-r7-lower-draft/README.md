# `n=4, r=7` lower endpoint source draft

Both sources are unchecked. The first asserts a positive polynomial after `x=32+u`, `t=1+v` for nonnegative `u,v`. The second uses that certificate and the explicit strict comparison `c<kY+k` to conclude `x³+6x²+15x+18<t`. The independently audited ordinary-integer [scalar checker](../trace74-n4-r7-scalar-obstruction/README.md) records the corresponding algebra.

No graph-zero, Pell-ordinate, q-divisibility, upper-endpoint, or iPRA claim is made. Source and prelaunch review are required before a coordinated Lean run.

The [independent source/prelaunch audit](../../reviews/trace74-n4-r7-lower-prelaunch-independent/README.md) passed. One author check ran in actual tool session 62525, exit 0 and fully reaped. Its [terminal](observations/attempt01/terminal.json) SHA-256 is `38241de928159785a5c01d71c951b8f9e5c1ed2993606a530c6d47f001b40212`; both stages passed. The [independent result audit](../../reviews/trace74-n4-r7-lower-result-independent/README.md) also passed.
