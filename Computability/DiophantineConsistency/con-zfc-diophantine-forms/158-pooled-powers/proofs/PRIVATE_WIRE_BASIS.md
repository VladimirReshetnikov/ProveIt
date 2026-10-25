# Private wire aggregation and common multiplication bases

All displayed indices in this note refer to the original pinned P245, or
the strict241 stage, whose coordinates and rows through90 are unchanged.
Coordinates range over all integers.

## Sum of two private squares

The coordinates X81 and X83 occur only in

    R65=X81-X80^2,
    R67=X83-(X14-X15-X82)^2,
    R88=...-X101*X81-X101*X83.

Replace X81,X83 by one coordinate U and the one row

    U-X80^2-(X14-X15-X82)^2=0.

Replace their contribution to R88 by -X101*U. This saves one coordinate
and one quadratic residual. Forward, set U=X81+X83. Backward, restore
X81=X80^2 and X83=U-X80^2; the new row makes the latter equal the required
second square. These are polynomial maps over the integers, not an
argument that a sum-of-squares residual may be discarded without a row.

## Share the multiplier before distributing it

Put F=X3, S=X14, S'=X15, a=X10, b=X11, p=X21 and
K=X70=F*S'. Three otherwise private coordinates are

    X84=1+Fb,
    X85=1+F(a-1),
    X89=1+F(6a+8b+2p).

Introduce J=FS and remove all three coordinates and their three defining
rows. Replace the three affected consumer rows by

    -S'-Kb+X86*X87+X88=0,
    -S-J(a-1)+X87=0,
    S+Jb-S'-K(6a+8b+2p)+X90=0.

Keep the row K=FS' and add the row J=FS. The change saves two coordinates
and two quadratic rows. Its point is that distributing after choosing the
common products FS and FS' avoids the cubic expressions that direct
single-wire substitution would produce.

For explicit residual certificates, let E=J-FS and d=6a+8b+2p.
After restoring the three deleted private coordinates, the old rows69,72,74
are respectively

    new69 + b*old54,
    new72 + (a-1)*E,
    new74 - b*E + d*old54.

The deleted rows68,70,73 become zero identically. Conversely, on inserting
J=FS, the new rows69,72,74 are respectively

    old69 + S'*old68 - b*old54,
    old72 + S*old70,
    old74 - S*old68 + S'*old73 - d*old54.

The verifier checks all residual identities, including every unaffected
row, in both directions. Composing the two changes gives the 241-to-238
stage. This equivalence is entirely algebraic and requires none of the
semantic sign, range, Pell or consistency assumptions.
