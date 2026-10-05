# Selected-action structure in the inherited positive7 alphabet

The inspected group route does not supply a numerical universal alphabet
or its size. It does, however, give a useful exact restriction on selected
source coordinates: relative to a common identity action, each relator
letter needs only **four of the seven positive history coordinates**.
The eight other raw signed letters need at most six, six, or seven each.
For r presentation relators this gives at most **52+8r selected-source
product interfaces**, versus56+14r if every raw letter uses all seven.

This is an interface reduction, not a paid gate saving. No complete
positive7 history circuit, global operation count, or new universal
Diophantine polynomial is emitted here. Root identified the common
factorization and four-coordinate restriction; the following derivation
checks them and gives the remaining paired-letter census.

## 1. What is fixed, and what has not been materialized

The inherited effective embedding produces a finite presentation on four
free basis letters a,b,z1,z2, with r finite relator words R_j. It supplies
no numerical r or relator list for the universal enumerator. The conjugated
fibre-product subgroup has the following raw generators and their inverses:

    (a z_i a^-1,z_i), i=1,...,4;
    (1,R_j), j=1,...,r.                                    (1)

Thus one may use8+2r labelled slots before removing identities or duplicate
matrices. This formula is not an instantiated alphabet-size bound. The
number and length of physical signed-shear codes, padded controller edge
count, and the positive lift's common coefficient bound remain unknown
numerically for this inherited universal presentation.

Write A=rho(a), Z_i=rho(z_i), and use the actual projective6 representation

    A=U=[1,1;0,1], V=[1,0;4,1],
    rho(b)=V^3=[1,0;12,1],
    rho(z1)=V U V^-1, rho(z2)=V^2 U V^-2.

For a2-by-2 determinant-one matrix P=[p,q;s,d], let

    S(P)=[p²,-2pq,q²; -ps,pd+qs,-qd; s²,-2sd,d²].           (2)

The six-dimensional matrices attached to the generators in(1) are
`diag(S(A Z_i A^-1),S(Z_i))` and `diag(I3,S(rho(R_j)))`.
Their inverse slots have the same structure; matrix entries can have
either sign.

## 2. Low-rank differences, not low-rank positive letters

For every P in SL2(Z),

    rank(S(P)-I3)<=2.                                      (3)

Indeed `(2q,p-d,-2s)` is fixed by S(P). Identifying a vector(a,b,c) with
the symmetric matrix G=[a,-b;-b,c], its product with
J0=[0,-1;1,0] is `tr(P)I2-2P` for this vector. It commutes with P;
`P^T J0=J0 P^-1` therefore proves `PGP^T=G`. The fixed vector is
nonzero unless P is I2 or -I2, in which case S(P)=I3 outright.
This proves(3), including both exceptional central cases.

Consequently relator differences from I6 have rank at most2, and paired
letter differences have rank at most4. In the positive7 lift put

    h=(1,1,1,1,1,2)^T, k=(h,1)^T,
    D=[I6|-h], E=[I6;0], F=8E-k*1_6^T,
    G_sigma=Q A_sigma Q^-1.

Here Q is exactly the unimodular chart of the positive7 note. Its lift is

    L(G)=kappa*k*1_7^T+F G D,
    L(G)-L(I6)=F(G-I6)D.                                 (4)

Because DF=8I6 and DE=I6, F is injective and D surjective over Q.
Thus the difference in(4) has exactly the rank of G-I6. By contrast
L(G) itself is invertible whenever G is: if L(G)v=0 then DL(G)v=8GDv=0,
so v lies in span(k), on which L acts by the nonzero C=8kappa.
Every actual positive letter therefore has rank7.

**Remark 1 (rank factorization alone gives no cheaper action).** A generic
3-by-3 dense action costs9M+6A. Factoring a rank-two3-by-3 matrix into
3-by-2 and2-by-3 dense matrices would use12M+7A for those two products,
even before adding an identity baseline. Thus(3) alone cannot justify
a gate saving. The useful fact below is the actual source-coordinate
support, not a dimension-only inference. These local counts charge all
generic coefficient multiplications and are not lower bounds.

## 3. Exact common-baseline selected action

Assume an independently certified selector interface supplies exact
coordinatewise products Z_sigma=s_sigma*H, with exactly one letter at
each history position. The following equalities can be read per digit or
as identities of the corresponding packed integers. Let S0=sum_i H_i.
Then

    T=sum_sigma G_sigma D Z_sigma
     =D H+sum_sigma (G_sigma-I6)D Z_sigma,
    v7=kappa*S0-sum_(i=1..6)T_i,
    v_i=8T_i+k_i*v7, i<=6.                                (5)

The selected packed action is(v1,...,v7). The value v7 is a shared offset,
not arithmetic that can be deleted because a mass equation exists.
An equivalent baseline identity is

    L(I6)=8I7+(kappa-1)k*1_7^T.                            (6)

Thus the identity letter needs no private selected-source products in the
difference sum. With at most one nonidentity letter, the same formulas
interpret the unused positions as L(I6). Adding this idle action preserves
the inherited zero predicate, multiplying its decoded signed difference
by8 per idle step, rather than acting as the identity on positive states.

Formulas(5)--(6) require actual selector products and their partition
identity. They are not a method for recovering either from untyped words.
Selected outputs can be zero; any positive hatted representation and its
arithmetic must still be accounted for by a later source.

## 4. Four relator coordinates and the raw-slot census

For a seven-vector Z, the actual chart gives

    Q^-1 D Z =
      (Z1-Z4, Z2+Z4-2Z7, Z3+Z4-2Z7,
       Z4-Z7, Z5+Z4-2Z7, Z6+2Z4-4Z7)^T.                  (7)

A relator difference `diag(0,S(rho(R_j))-I3)` uses only the last three
entries of(7). Thus only Z4,Z5,Z6,Z7 need be supplied as its selected
positive-source products. To check all downstream coordinates, if that
last-block difference is(a,b,c), then

    Q(0,0,0,a,b,c)^T=(a,-a,-a,a,b-a,c-2a)^T.

Its sum is b+c-3a, so its full positive7 correction is

    (11a-b-c, -5a-b-c, -5a-b-c, 11a-b-c,
     7b-5a-c, 6c-10a-2b, 3a-b-c)^T.                        (8)

No omitted first-block history enters through the common offset.

For the other slots, a unit upper shear and its inverse have S(P)-I3
independent of the original first coordinate. The paired a slots are
upper shears in both blocks, so they need entries2,3,5,6 of(7), hence at
most positive-source coordinates2,3,4,5,6,7. The paired b slots have a
possibly full first-block difference and a lower shear in the second;
the latter is independent of original coordinate6. Consequently they
need at most positive-source coordinates1,2,3,4,5,7. It is enough to
retain all seven for each paired z1,z2 slot and its inverse.

| Raw slot type | Number | Sufficient positive-source coordinates |
| --- | ---: | --- |
| paired a and its inverse |2|2,3,4,5,6,7|
| paired b and its inverse |2|1,2,3,4,5,7|
| paired z1,z2 and their inverses |4|1,2,3,4,5,6,7|
| relator and inverse slots |2r|4,5,6,7|

Their total is `2*6+2*6+4*7+2r*4=52+8r`, compared with the naive
`7*(8+2r)=56+14r`. These are sufficient interface widths on the raw
labelled list, not minimal widths or paid instructions. Identities,
duplicates, or special relators may admit further simplifications.

## 5. Exact unpaid boundaries and scope

The four-letter presentation rank is explicit; the universal relator
count, word list and numerical matrix alphabet are not. Hence no numerical
kappa, selected-action circuit size or macro-controller size follows from
this census. A direct macro-letter implementation must still pay its
selector partition and the coefficient-weighted action. Replacing macros
by the eight physical shears requires the fixed regular macro-language
controller: arbitrary physical words do not represent the same subgroup
query. The existing complete matrix compiler charges that controller and
all other interfaces, but its numeric ledger also depends on a supplied
finite table; its four-coordinate source costs do not transfer to positive7.

There is also no emitted positive7 duration/height or unbounded-history
certificate here. The supplied selected products, coefficients, sums,
recurrence checks, positive hats, geometry and endpoint obligations remain
separate costs. The exact dyadic mass theorem does not pay them or make
its carry counterexample disappear. No complete operation saving follows
from subtracting4+6r product interfaces from an unrelated source ledger.

**Open question 1 (root's paid-action continuation).** Can the support
restriction(7)--(8), the shared baseline(5), and exact mass be composed
with one explicit typed selector and duration/height source to reduce a
complete positive7 history count? The present algebra identifies exactly
which relator products are unnecessary, but supplies no such source.

This proof-only note reads the complete projective6, positive7 and generic
complete-matrix notes, the group embedding/generator interface, and the
indicated controller/sparse-compiler spans. Their exact byte/read bindings
are in the companion JSON. It does not re-audit the external embedding,
materialize its output, execute any helper or source array, propagate a
saved source degree, or alter the repository/Git. No numerical experiment
is used as proof. The fixed-alphabet universal theorem is inherited with
its stated dependencies, not established anew by these local identities.
