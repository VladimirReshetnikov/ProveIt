# Private signed quotients in a direct quartic

This note proves the local transformation from the pinned 3,609-natural-variable
quartic to the 6,628-integer intermediate. Later guard or wire reductions may
compose with this result. It is an equivalence theorem, not a proof of either
consistency or inconsistency of ZFC.

## Fixed input

The parent is `source/natural_equation.json`, with SHA-256
`e851ff1d420a39be069e63f6f117557356c38e6d8272a481258fe38cb38dc6ea`.
It has 3,609 variables and 2,949 quadratic residuals; its equation is their
sum of squares. All parent coordinates are natural numbers, including zero.
Its ordinary consistency calibration and finite arithmetic compiler are
inherited from the pinned ProveIt snapshot
`278bc68df1af125d62f9cbfe28c9fd3ebcf50d5b`.

The original unrestricted-integer companion appended one three-variable
nonnegativity certificate for each of 1,670 semantic inputs, yielding
8,619 variables and 4,619 residuals. The remaining 1,939 coordinates were
definitional arithmetic gates, whose nonnegativity followed by induction.

## Elimination lemma

Suppose a natural residual system contains a pair of private natural variables
`p,q`, two private gate outputs `u,v`, and the three equations

    u = M p,       v = M q,       E + epsilon(u-v) = 0,

where `epsilon` is either 1 or -1. The variables `p,q` occur only in their
displayed product definitions; `u,v` occur only in those definitions and the
displayed third equation. The modulus `M` is an affine polynomial with
nonnegative integer coefficients in retained natural coordinates, and `E`
does not contain the four eliminated coordinates.

Replace those equations by

    E + epsilon M z = 0,

where `z` is one unrestricted integer. This preserves existence, and it
preserves the quadratic residual degree if `E` was quadratic.

For the forward implication put `z=p-q`. For the reverse implication put
`p=max(z,0)` and `q=max(-z,0)`, so both are natural and `z=p-q`. Set `u=Mp`
and `v=Mq`; these are natural because `M>=0`. Every old equation is then
restored exactly. The proof permits `M=0`; it uses no division or
nonzero-modulus assumption. All other coordinates are unchanged.

A private affine gate `g=A` used only linearly in one further residual can
be substituted into that residual and deleted. When `A` has nonnegative
coefficients in natural coordinates, `g` is restored naturally. Its deletion
does not increase a quadratic residual's degree when the use is linear.

## Application to the literal parent

The transformation certificate identifies exactly 221 quotient pairs:
four pairs in each of 55 positive-power certificates, and one pair for the
final CRT evaluation congruence. The four power congruences are `B_mod_U`,
`S_mod_U`, `R_mod_4Y`, and `power_congruence`.

All 442 quotient coordinates occur only in their own multiplication definition.
All 442 product outputs have one further use. For 219 pairs the outputs occur
with opposite unit coefficients in the same residual. The remaining two pairs
first require deletion of the private affine bridge coordinates 337 and 394
(the indices are those of the frozen natural parent). Their complete affine
definitions and unique uses are recorded in the certificate.

Consequently the transformed core has

    variables = 3609 - 3*221 - 2 = 2944,
    residuals = 2949 - 2*221 - 2 = 2505.

Of the core variables, 221 are unrestricted quotients, 1,228 are retained
natural semantic inputs, and 1,495 are retained natural gate outputs. Every
gate still has a unique monic topological defining equation with a polynomial
of nonnegative coefficients on the right. No signed quotient occurs in a
retained gate definition, in a quotient modulus, or in either restored affine
bridge. Thus the gate nonnegativity induction remains valid.

## Integer certificates

For every retained natural semantic coordinate `x`, add fresh unrestricted
integers `a,b,c` and the residual

    x - a*a - b*b - c*(c+1).

This vanishes exactly when `x` is nonnegative. Necessity follows because
`c(c+1)>=0` for every integer `c`. For sufficiency, Legendre's three-square
theorem applies to `4x+1`: it is odd and is 1 or 5 modulo 8, hence is never
of the forbidden form `4^r(8s+7)`. Its representation has exactly one odd
square and two even squares, giving
`4x+1=(2c+1)^2+(2a)^2+(2b)^2` after permuting the three squares. Dividing
the difference by four gives the displayed residual.

The resulting integer equation has

    variables = 2944 + 3*1228 = 6628,
    residuals = 2505 + 1228 = 3733.

It is the sum of the squares of all listed quadratic residuals. Over the
integers that sum vanishes if and only if every residual vanishes. Therefore
an integer zero first recovers all natural semantic inputs through the guards,
then all natural gates by induction, then all eliminated natural quotient
coordinates by the explicit lift above. This produces a zero of the entire
frozen natural parent. Conversely every natural parent zero projects to the
core and extends through the three-square certificates to an integer zero.

The fully collected polynomial has exactly 31,237 nonzero monomials and
coefficient height 127,285,349. A fresh guard auxiliary has fourth-power
coefficient 1 and occurs nowhere else, so the degree is exactly four.
All 6,628 variables are live. These numerical claims are independently
checkable from the finite coefficient dictionaries; they are not used to
prove the unbounded existence equivalence.

## ZFC provability and scope

The transformation is a finite sequence of polynomial identities, definitions
by cases on integer signs, topological inductions, and applications of the
three-square theorem. Each argument is an ordinary proof in ZFC. It is uniform
over the theory's own natural and integer objects: it does not transfer a
bounded experimental check to a universal statement, and it does not restrict
proof certificates to externally standard numbers.

Composing this local ZFC-provable equivalence with the parent calibration gives
the same no-integer-zero iff Con(ZFC) statement for the new polynomial. This
package does not emit or claim a new kernel-checked encoded derivation in the
repository's sealed object-language calculus. The parent calibration is a
named inherited mathematical dependency; the exact compiler source and its
finite audits are retained separately.
