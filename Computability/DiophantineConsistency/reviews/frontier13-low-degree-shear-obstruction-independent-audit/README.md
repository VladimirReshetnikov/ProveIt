# Independent review of the bounded residual-shear degree obstruction

The independent review actually exited 0; its receipt SHA-256 is
`4c6c3af701bea6d52870559b74d7035aedf3fce5226f055bc9babe58520a4137`.
It reconstructs the pinned graph using a separately structured nested
witness-monomial/port-polynomial representation, rather than relying on the
original checker's flat exponent vectors. It reproduces residual witness
degrees `15, 13, 10, 18`, confirms the exact four-square output wiring and
rejects the three recorded graph mutations. The original checker and an
isolated copy of its process wrapper also exited 0; the wrapper reproduced its
saved receipt and refused overwrite. Optimized Python is rejected.

Let `N` denote the auxiliary residual and `A0`, `A1`, `S` the other three.
Every degree-15 term of `A0`, degree-13 term of `A1`, and degree-10 term of
`S` contains `eta` or `zeta`. Independently setting both variables to zero
strictly lowers each residual's degree. The coefficient in `N` of the
witness monomial `J^8 f^6 X^2 Y^2` is exactly `beta^8` as a polynomial in
all four ports; it has no other port contribution. The graph, port metadata,
compressed and decompressed beta bytes and earlier finite PDF binding receipt
are pinned. The saved beta is exactly `2^94517 − 1`, so this coefficient is
nonzero at the selected actual port.

For arbitrary polynomial multipliers of witness degrees at most 3, 5 and 8,
respectively, each product with `A0`, `A1` or `S` has witness degree at most
18. Any degree-18 contribution comes from a leading term of its residual and
therefore still contains `eta` or `zeta`: ordinary polynomial multiplication
cannot remove either variable. It cannot alter the displayed monomial's
coefficient. Thus `N + H0*A0 + H1*A1 + HS*S` has degree exactly 18 after
fixed-port specialization. The other three residual squares have degrees at
most 30, 26 and 20. The degree-36 homogeneous part of the sheared square is
nonzero because the integer polynomial ring has no zero divisors, so no
other square can cancel it. Replacing each witness by itself plus one preserves
the leading homogeneous part and therefore the degree 36.

At integer assignments, a sum of four squares is zero exactly when every
residual is zero, and the invertible triangular shear preserves their common
zero set. This mathematical argument is not a formal Lean theorem. The bound
does not cover higher-degree multipliers with cancellations, changing other
residuals, non-shear transformations, alternative variables, or another
polynomial with the same zero set. It is not an unrestricted degree lower
bound or global minimality result. The link from saved beta bytes to the
printed recipe retains the earlier finite review's manually transcribed
decoder/rank boundary.
