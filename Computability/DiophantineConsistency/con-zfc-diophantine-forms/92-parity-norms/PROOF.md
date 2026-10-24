# An odd-carrier norm merger in sixteen unrestricted integers

## Statement and boundary

The literal packets `parity16_sos.json` and `parity16_unit_product.json`
define ordinary fixed polynomials in **sixteen unrestricted integer
unknowns**, of exact degrees **160** and **152**, respectively. Their
existence of an integer zero is equivalent to existence of an integer zero
of the copied parent `parent/degree88_17.json`. The parent is the
17-integer degree-88 equation from the incoming `con_zfc_pell_congruences_2026-10-23.zip`
at ProveIt commit `cfbf118b4ad9b2c651fe96b571d9415261766328`.

The new equivalence is proved below without a Pell classification or a
rational Pell descent theorem. Its composition with the parent's ordinary
native/Pell/refutation calibration yields the requested theorem formalizable
in ZFC: absence of a zero is equivalent to syntactic Con(ZFC). This note
does not provide a new end-to-end kernel certificate or reprove the
inherited compiler calibration. The sixteen-variable point improves the
variable/degree tradeoff; it does not beat the separate ten-integer
high-degree frontier or assert a global minimum.

All six fixed integers are supplied, unchanged, under `coefficients/`.
Their whole binding is source34's mixed-parity-unrounded tuple plus
source71's two determinant scales. In particular MF is already shifted.

## 1. The elementary merger

**Lemma.** Let a, delta, r be integers with delta nonzero and put A=4a+1.
There exist integers u,y with

    u^2 = A,       delta*y^2 = r

if and only if there is an integer t with

    G = [delta*(t(t+1)-a)-r]^2 - A*delta*r = 0.       (1)

No positivity, coprimality, or size condition on a, delta, or r is needed.

**Proof.** Put x=2t+1, which is always nonzero. The exact polynomial
identity is

    16G = [delta*(x^2+A)-4r]^2 - 4A*x^2*delta^2.     (2)

If G=0, define the rational number

    u = [delta*(x^2+A)-4r] / (2*x*delta).

Equation (2) gives u^2=A. A rational number whose square is an integer
is an integer: in a reduced fraction m/n, n^2 divides m^2 and hence n=1.
Moreover u is odd, since A is 1 modulo 4. Thus y=(x-u)/2 is an integer.
The definition of u gives delta*(x-u)^2=4r, so delta*y^2=r.

Conversely, given u,y as above, u is odd. Set x=u+2y and t=(x-1)/2.
Then t is integral, x is odd and nonzero, and substituting these values
in (2) gives G=0. This proves both directions. The odd carrier excludes
the zero-carrier component that would make an unrestricted norm unsound.

The factor 16 in (2) is a fixed nonzero integer. Dividing the expanded
polynomial by 16 produces the integer polynomial (1), not a rational
coefficient or a hidden divisibility condition.

## 2. The parent's two private roots

Use all polynomial abbreviations in the copied parent. In particular,

    q = beta*(3J3+1)+1,        W = 4*(3w3+1),
    X = qW,                   Y = (2v_scale+1)q^3,
    E = XY,                   a_native = E+Y,
    Delta = a_native^2+4a_native+3,
    k = R+1+hE,               eta = c-kY,
    P = k+E(c-eta),           I = (2r+1)c^2.

The parent has a first root coordinate tau with residual

    tau^2 + 2tau(2P-k) + k^2 - 4.

This equals

    (tau+2P-k)^2 - 4[1+P(P-k)].

At a zero the integer tau+2P-k is even, so
u=(tau+2P-k)/2 is an integer and u^2=A, where

    A = 1+P(P-k)
      = 1+X Y^2(XY^2+1)k^2
      = 4A4+1,
    A4 = q*(3w3+1)*Y^2*(XY^2+1)*k^2.              (3)

Every expression in (3) is an integer polynomial. The converse restoration
is tau=2u-2P+k.

The parent has a second private coordinate y_gap with residual

    V^2+(1-I^2)y_gap(2V+y_gap)-1.

With Q=I^2, delta=Q-1, r_aux=QV^2-1 and y=V+y_gap, this residual is

    QV^2 - delta*y^2 - 1 = r_aux-delta*y^2.

Its inverse restoration is y_gap=y-V. These two coordinates occur in no
other residual or retained abbreviation. They are therefore eligible for
the lemma, once delta is shown nonzero.

## 3. The denominator is nonzero before either deleted root is recovered

This can be proved without the positivity residual, a fact useful when
merging additional roots. The fixed beta is at least 17. Since 3J3+1
is a nonzero integer,

    |q| >= beta-1 >= 16.

Similarly W is a nonzero multiple of 4, hence |X|>=4|q|. Since
2v_scale+1 is nonzero, |Y|>=|q|^3. Consequently

    |a_native| = |X+1|*|Y| >= (4|q|-1)|q|^3,
    Delta = (a_native+2)^2-1 > 1.

The retained strong row says

    I^2 = Delta*(f^2-1).

If I^2=1, the integer Delta>1 would divide 1, a contradiction. Therefore
delta=I^2-1 is nonzero. This argument applies to every zero of the
new system; it invokes no assertion that an encoded machine halts.

## 4. The exact sixteen-variable system

Remove tau and y_gap from the parent's variable list and add t_parity.
The remaining sixteen variables are

    J3, C_native, z, f, h, r, v_scale, w3, gamma, T, c,
    pair_root, pair_pos1, pair_pos2, pair_pos3, t_parity.

Retain unchanged the main Pell row, strong Pell row, and combined
positivity row. Replace the two private-root rows by

    norm16 = [delta*(t_parity(t_parity+1)-A4)-r_aux]^2
             - (4A4+1)*delta*r_aux.

Thus there are four residuals. A zero of the parent supplies u,y and
then t_parity=(u+2y-1)/2 by the lemma. Conversely the retained strong row
proves delta nonzero, the lemma supplies integer u,y, and the two
restoration formulas recover a zero of the parent. The retained
coordinates are unchanged in both constructions. This is an existence
equivalence; no false uniqueness or zero-set bijection is claimed.

## 5. Two exact single-polynomial finalizers

Let the four residuals be r1,r2,r3,r4. One single equation is

    P160 = r1^2+r2^2+r3^2+r4^2 = 0.

The other is

    P152 = (1+4r1)(1+4r2)(1+4r3)(1+4r4)-1 = 0.

The second equation has exactly the same integer zero set. If its product
is 1, every integer factor is a unit, hence 1 or -1. Each factor is
1 modulo 4 and so cannot equal -1. Thus every factor is 1 and all four
residuals vanish. The converse is immediate. This unit-product finalizer
is elementary and is not claimed as a newly discovered technique.

The residual degrees are exactly 14,14,44,80. Consequently the first
finalizer has degree 160; the second has degree 152. The supplied
certificates evaluate each highest homogeneous part on one exact rational
line over F_1000000007, using the authentic coefficients reduced modulo
that prime. A nonzero coefficient of the claimed top degree, together
with the independently computed upper bound, proves the exact degree
after coefficient specialization. This is exact algebra, not a random
identity test.

## 6. Logical conclusion

For either polynomial the new arguments prove, in ordinary mathematics
formalizable in ZFC,

    exists an integer zero of P
      iff exists an integer zero of the supplied parent
      iff exists a finite syntactic ZFC refutation.

Negating gives the requested ZFC-provable equivalence. The theorem makes
no consistency assumption and does not determine whether a zero actually
exists. Its new local proof is elementary: rational-square integrality,
parity, exact polynomial identities, and integer units. The parent still
supplies the substantial native encoding and logical calibration.

## 7. Reproduction and attribution

Run `python3 build.py` and `python3 audit.py` from this directory. Both
also work with `python3 -O`; checks use explicit errors rather than
removable assertions. The builder writes the two literal packets and
exact degree certificates. The separate auditor imports no builder code.

Pinned parent URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/cfbf118b4ad9b2c651fe96b571d9415261766328/docs/incoming/con_zfc_pell_congruences_2026-10-23.zip

Parent archive internal path:
`con_zfc_pell_congruences_2026-10-23/transport/degree88_17.json`.
The original source34 and source71 numerical data retain their original
binding and provenance. The root package should retain the inherited
source notices and calibration proofs on integration.
