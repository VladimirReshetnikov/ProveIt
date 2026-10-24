# Eleven-coordinate oriented power graph: review and shared-frame compatibility

The direct component in `ConZFC_Congruence_Certificates_2026-10-24.zip`
(SHA256 `f4119b01e56f586558f0910c6deb21b83c82dfc324f884d7d95d28500ef09e63`)
has a sound ordinary positive-power specialization. I found no new gap in
its quotient orientations, Pell-index recovery or order of witnesses.
It is compatible with the existing positive-power *semantics*, but its
standalone six-row block is not a drop-in size improvement over the
synchronized compiler. No new candidate is materialized from this review.

## Exact hypotheses and graph

The theorem is for **n>0, k>0 and m>=0**. It makes no claim about zero
bases or zero exponents. All eleven auxiliary coordinates
`U,a,z,y,q,d,g,b,s,r,h` are nonnegative integers. Define

```
W=n+k, Z=z+1, Y=k+y, T=m+g+1, A=n+a+1,
V=Y^2(d+1), B=1+4Y(q+1),
X=Y(a+1)+m+Th, S=X+Us, R=k+4Yr,
N(A,X,Y)=X^2+Y^2-1-A^2Y^2.
```

The six rows are N(A,X,Y)=N(A,U,V)=N(B,S,R)=0,
B=A+Ub, 2An=T+n^2+1 and N(W+1,A,WZ)=0.
They have a natural solution exactly when m=n^k. The output m is not
one of the eleven auxiliaries. The actual ordinary quartics contain55
power calls, each with these six semantic rows before gate expansion.

The pinned primary Mathlib source is retained inertly as
`direct/upstream/PellMatiyasevic.lean`. Its `matiyasevic` and
`eq_pow_of_pell` statements are the precise dependencies; no new Lean
process was run. The integer norm equalities imply the required natural
subtraction versions exactly. Also A>W>=n before the use of A-n, so
truncated subtraction cannot change the power congruence.

## Quotient and Pell-index orientation

In the intermediate fourteen-auxiliary graph, the last norm and Z>=1
force A>W>=n,k and A>=2. The other definitions give Y>=k>=1,
V>=Y^2>=Y, B>=5 and T>m. The first two norms imply U>=X and U>=A.
Positive representatives of A and X modulo U therefore have the forms
A+Ub and X+Us with b,s>=0. This includes U=A and U=X: a positive
residue-zero representative is at least U. The R quotient is nonnegative
because 0<k<=Y<4Y.

For the remaining quotient put D=X+Yn-YA-m. The first norm gives
X>(A-1)Y, hence D>(n-1)Y-m>=-m>-T. Since D is a multiple of the
positive T, it cannot be negative. Thus h=D/T is nonnegative. This
argument does not assume the conclusion m=n^k.

The Pell-index congruence has a real signed ambiguity which must not be
discarded informally. In the retained Mathlib proof, classify the three
norms at indices i,n,j. The Y^2|V condition gives i<=n and 4Y|4n.
The x-coordinate congruence gives j=i or j=-i modulo4n. Meanwhile the
other congruence gives j=k modulo4Y. In the negative case this would
make k+i a positive multiple of4Y, but k<=Y and i<=Y give
0<k+i<4Y. This contradiction excludes that branch. Then i=k follows
from the remaining congruence and bounds. These are exactly the
hypotheses retained by the oriented graph; it does not assume a generic
unsigned-index theorem which omitted the negative branch.

## Completeness and witness order

For fixed positive n,k first take W=n+k, then
A=chi_(W+1)(W), Z=psi_(W+1)(W)/W. The index congruence modulo W
makes Z integral and positive. Growth gives
n^k<=n^W<(W+1)^W<=A. Next take X=chi_A(k),Y=psi_A(k) and
T=2An-n^2-1. In particular T>=A>m. Only then apply the standard
Pell-index certificate to choose U,V,B,S,R, and finally recover each
oriented quotient and slack. No private Pell witness contributes to W.

The intermediate graph has A>n, so a=A-n-1 is natural. Eliminating
X,S,R by the displayed nonnegative polynomial definitions is an exact
bijection between its solutions and the final eleven-coordinate graph.
It introduces no new sign or quotient assumption. The constructive
fixtures in the provided audit are finite checks; the unbounded proof
uses the Pell criterion and the inequalities above.

## Why the whole gadget is not the next size improvement

The current synchronized factorial-radius compiler has25 power calls,
20 exponent groups,8 distinct bases, one common W/A/Z frame, and one
common U/V/B index frame. Its positive internal congruences are already
oriented by the same inequalities. In particular the quotient
D=X+Yn-YA-m is already nonnegative, and the internal B,S,R quotients
are already natural. Importing the new sign argument alone removes no
currently present signed-quotient coordinate.

The standalone gadget chooses W=n+k and A separately for each call.
Using all25 independently would discard the common frame and would
duplicate the shared auxiliary Pell norms/CRT choices. Repeating the
semantic economy of six rows per isolated call is therefore not a valid
comparison with the synchronized scalar-row count.

A compatible theorem with an arbitrary common W>=n,k is valid: the same
completeness construction works for every such W; the shared frame makes
A>W and hence each local a=A-n-1 natural. But the formula for X depends
on the call's base n, output m and modulus T. A shared X/Y pair belongs
to an exponent group and serves potentially several bases. It cannot be
replaced by a different X definition independently at every call.

One possible separate experiment would introduce a common slack
a0=A-W-1 and use the known positive frame sum for W-n, selecting one
call per exponent group to define X. This is mathematically compatible,
but requires a new measured compiler, complete restoration map and
degree-preserving gate treatment. An expression-level coordinate removal
can recreate the same arithmetic gate when the eliminated X or S is
squared. There is no certified count gain here yet, so none is claimed.

The delivered direct graphs have2473/4860 naturals, degree4,
20580/14719 terms and heights127808289/1837. The current synchronized
radius points use502/509/573 naturals. The2473 point is therefore not
a fewest-variable improvement. The4860 point remains a separate low
height tradeoff; this review does not assert global dominance over it.

## Replays and boundary

The provided direct `verify.py` was read first and run only on a scratch
extraction. It runs the symbolic eleven-coordinate graph audit, all55
positive-input call checks, constructive Pell fixtures, independent full
quartic expansions for both variants in normal/-O modes, and exact
literal rebuilds. It invokes no coefficient recipe or proof assistant.
The complete original archive was already authenticated in the separate
congruence peer review. The new direct replay receipt is
`direct-oriented-power-compatibility.json`.

The ordinary numerical C222/CRT/compiler/refutation interpretation is
unchanged and remains an explicit inherited dependency. Neither the
finite checks nor this local power equivalence establishes consistency,
absence of zeros or the required internal object-ZFC derivation.
