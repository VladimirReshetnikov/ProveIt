# Two forced core columns in the quartic truncation

Working exact reduction, 1 October 2026. The support formulas and exterior
principal-block argument are checked. The full scalar Schur certificate is
not yet complete, so this note does not assert the final BB theorem.

Use a genuine 3+3 minimum cover A union B, with unit activities on the left.
Force B0 and B1. Their core neighborhoods in A are J and K; the remaining
core column B2 has neighborhood H. Let N_S be the exterior-left population
of neighborhood S in B, with bits 1,2,4 corresponding to B0,B1,B2.

Set a=N1+N5, b=N2+N6, c=N3+N7 and

p=ab+ac+bc+c(c-1)/2.

Thus p counts exterior-left pairs matching the two forced columns. Write
h(S,T) for the number of two-element A supports matching columns S,T, and
chi(S,T,U) for the Boolean three-column perfect-matching indicator.

## Exact coefficients

The forced-pair coefficient is

E=p+a|K|+b|J|+c|J union K|+h(J,K).

For a further exterior-right column of type S, its triple coefficient is

r_S=p|S|+a h(K,S)+b h(J,S)+c h(J union K,S)+chi(J,K,S).

For two further distinct exterior-right labels of types S,T, their
four-column coefficient is

b_ST=p h(S,T)+a chi(K,S,T)+b chi(J,S,T)
     +c chi(J union K,S,T).

The union terms count the feasible endpoint set once when the common
exterior-left row can be allocated to either forced column. The formulas
follow by partitioning on zero, one, or two exterior-left selected rows.

Let x be the coefficient for all three B columns, and v_S the coefficient
for all three B columns and an exterior-right column S. Both have direct
finite population formulas. x is the rank-three independent-triple count
on all L rows and the three actual A rows. For v_S, select respectively
three, two, or one L rows: the contributions are q_L |S|, the population
sum of Boolean four-column supports on two L and two A rows, and the
population sum on one L and all three A rows. These formulas are implemented
without allocation multiplicities in build_BB_certificate.py.

## The class matrix and principal block

After differentiating F4=15s^4+10p1s^3+6p2s^2+3p3s+p4 in B0,B1, its positive
s pivot leaves the negative of the matrix with entries

Q_R(S,T)=3r_S r_T/(4E)-b_ST,
Q_B,R(S)=3x r_S/(4E)-v_S,
Q_B,B=3x^2/(4E).

Here b_SS is retained on the diagonal of the seven-class matrix. For a
finite set of R labels, aggregation of a signed test vector gives this
class quadratic plus sum_S b_SS sum_{i of type S} z_i^2. The correction is
nonnegative. Therefore positivity of the class matrix suffices.

Delete the unforced B2 column. The resulting graph has a 3+2 cover, so the
previous small-cover theorem on the transposed graph supplies the full
degree-five right marginal. Differentiate in B0,B1 and then once in s.
Its quadratic Schur inequality has coefficient 2/(3E). The desired R
block has coefficient 3/(4E), larger by 1/(12E). Duplicate each of the seven
R types into m labeled twins, and give each signed test coordinate of a
class the value z_S/m. The within-class correction tends to zero as
m tends to infinity. Hence the class R block is PSD for every actual
integer L population. This uses the retained-variable
version of the small-cover theorem, not merely scalar ULC.

## Exact rational elimination and boundary treatment

Up to permutations of A and interchange of the two forced columns, there
are thirteen pairs:

(0,0),(0,1),(0,3),(0,7),(1,1),(1,2),(1,3),
(1,6),(1,7),(3,3),(3,5),(3,7),(7,7).

build_BB_R.py computes an exact rational inverse on a maximal principal
block of 4E Q_R, retaining six classes for the three permanently
rank-six cases (0,0),(0,1),(1,1), and seven otherwise. In those three cases,
every profile is a linear combination of containment indicators of sets
of size at most two, including the unforced-B cross column. Thus the exact
relation for the omitted class is

v_7=v_3+v_5+v_6-v_1-v_2-v_4,

and the same relation holds for r and every row/column of Q_R. The
one-L-row term in v is zero for (0,0); in the other two cases it is a
fixed population multiple of chi(S,1,H), which also has degree at most
two in containment indicators. Therefore the six-class reduction is a
valid congruence for the full matrix, not only the R principal block.
For seven classes,
only one scalar Schur complement remains:

S=3x^2/(4E) -(3xr/(4E)-v)^T Q_R^{-1}(3xr/(4E)-v).

The exterior L block has a three-element matching basis. Selecting one
of its 51 possible mask multisets b gives N=b+X, X>=0. Its projected
populations lie in at least one of the four cones

(a,b,c)>=(1,1,0),(1,0,1),(0,1,1),(0,0,2).

On each closed translated cone p>=1: p is at least one at its base and is
coordinatewise increasing there, since its derivatives are b+c, a+c, and
a+b+c-1/2. Thus E>=p>=1 throughout, so the original class matrix has no
denominator singularity at a cone boundary.

All exact determinant factors, after p=ab+ac+bc+c(c-1)/2, can be checked
for nonnegative coefficients on these four cones. A nonzero polynomial
with nonnegative coefficients is strictly positive on the open cone.
In particular, the chosen R principal determinant never vanishes there.

The open seven-population cone X>0 is connected and contains integer
points. At an integer point the R principal block is PSD by the preceding
argument and nonsingular by its determinant, hence PD. Continuous inertia
then makes it PD throughout the open cone. This is a purely algebraic
argument; no fractional population is interpreted as a graph.

Once the cleared scalar Schur numerator is proved nonnegative on that
whole cone, the full class matrix is PSD there. Ordinary matrix continuity
extends this conclusion to every boundary X>=0, simultaneously handling
singular R blocks and the required kernel-range condition.

Current status: all thirteen symbolic R inverses and determinants are
available. The primary factor-positivity checks pass. Scalar numerator
generation and complete basis-cone positivity remain in progress.

## Removing extra rows supported only at the unforced column

The population N4 affects neither E, r, nor the R block M=Q_R. Increasing
N4 by t>=0 changes x=x0+tE and v=v0+t r. The cross column therefore becomes
w(t)=w0-t r/4, where w0=3x0 r/(4E)-v0. The previous degree-five bound gives
M>=r r^T/(12E).

Assume the full base class matrix at t=0 is PSD. On the range of M, use its
Moore--Penrose inverse. Both r and w0 lie in this range, and

T=r^T M^+ r<=12E,
w0^T M^+ w0<=3x0^2/(4E).

The scalar Schur remainder at t is the base remainder plus

[3x0/2+(r^T M^+ w0)/2] t+[3E/4-T/16] t^2.

The quadratic coefficient is nonnegative by T<=12E. Cauchy--Schwarz gives
|r^T M^+ w0|<=sqrt(12E * 3x0^2/(4E))=3x0, so the linear coefficient is
also nonnegative. Hence the full class matrix stays PSD for all t>=0,
including singular M. The exact identities for x and v follow by selecting
the new row: it must match the only adjacent column B2, leaving the forced
pair or forced-pair-plus-R support counted by E or r.

A matching exterior L basis contains mask4 at most once. Therefore the
scalar certificate may set N4=0 on cones whose chosen basis omits4 and
N4=1 on cones whose chosen basis contains4; the lemma restores all extra
X4. This removes one population variable from the finite coefficient gate.
