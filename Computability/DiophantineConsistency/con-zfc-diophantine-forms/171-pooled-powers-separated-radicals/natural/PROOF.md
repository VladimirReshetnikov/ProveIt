# Natural pooled powers with a shared shifted syntax square

## 0. Exact result and retained calibration

The principal pre-basis equation has **202 independently nonnegative integer
coordinates and 154 quadratic residuals**. The polynomial is the sum of the
squares of precisely those residuals. `pooled202/equation.json` gives all of
them and `pooled202/expanded_polynomial.json` gives every collected coefficient.
Its exact degree is four; its pre-basis expansion has 10,104 nonzero monomials
and coefficient height 9,592,414,944. The 203-coordinate sparse companion has
155 residuals and 7,242 monomials. These are genuine reductions from the
inherited 206-coordinate endpoint, not a change from natural to integer
variables or a count of a subset of the coordinates. Row-basis companions
may improve the other measures without changing these counts.

The full round20 natural construction, ordinary proofs, offline compiler,
contraction certificates and calibrated logical source are preserved in
`inherited/`. The local nonnegative source polynomial and every syntax label
are unchanged by the present work. Its already established theorem is:
a natural zero exists if and only if the fixed effective ZFC presentation
in its C222/ZF/ZFC calibration has a finite syntactic refutation. The new
construction has the same equivalence, by the proof below. Consequently
ZFC proves that its no-natural-zero sentence is equivalent to `Con(ZFC)`.
This does not assert consistency, global minimality, or a newly kernel-checked
end-to-end ZFC derivation. The finite Python checks are exact algebra checks;
the unbounded Pell, domain, and calibration arguments are ordinary mathematics.

There are two new steps, proved separately: (i) exact sharing of three shifted
quadratic syntax wires and one affine factorial multiple, saving three
coordinates; (ii) a three-coordinate natural aggregate for the three exact
powers at base q, saving one more coordinate. The second step uses a stronger
cofinal lower Pell frame, with no additional coordinate. It does **not**
naively assume that deleting a power-output row preserves the orientation
of a consecutive Pell pair. Section 4 treats the one lost orientation.

## 1. Exact sharing of shifted quadratic syntax gates

Use the literal parent names. Write

    b=crt.encoded.b, M=mul.36, L=2b+M,
    G=(2L+6)(2L+7)=4L^2+26L+42.

The three parent defining rows state exactly

    mul.43  =4L^2+34L+72 =G+8L+30,
    mul.143 =4L^2+30L+56 =G+4L+14,
    mul.166 =16L^2+100L+156 =4G-4L-12.              (1)

Replace their three coordinates by the one natural coordinate G and the
quadratic defining row `G-4L^2-26L-42=0`. In the projected207/208 parent
charts the third retained wire is `add.171`, rather than `mul.166`; its
literal defining row gives instead

    add.171=8G+4b+2mul.60+13.                       (2)

Both forms therefore save two coordinates and two rows. Although the third
restoration in (1) has negative displayed coefficients, it is natural ON
the retained G row, because

    4G-4L-12=16L^2+100L+156>=0.

This is not an assertion of unconditional orthant positivity. Conversely,
an arbitrary parent zero supplies the nonnegative value G by its displayed
polynomial in L. All restored expressions, every substitution into another
row, and the duplicate row factors 1,1,4 (or 1,1,8) are checked exactly.
No divisibility condition or new semantic restriction is introduced.

The parent also has the two literal rows

    mul.366=F(4+4b+2M),  mul.370=F(6+4b+2M).

Replace `mul.370` everywhere by `mul.366+2F` and omit its duplicate defining
row. Its restoration is coefficientwise nonnegative. Hence this saves one
more coordinate and row, with a bijection on the appropriate natural solution
sets after the stated deterministic coordinate replacement. All source
values and all inherited local majorants remain exactly the same.

This gives the intermediate 203/155, 204/156 and 205/157 systems.

## 2. The stronger lower Pell frame

The inherited frame is a natural integer W, the sum of its displayed semantic
atoms plus a positive fixed offset. The source retains natural coordinates
`ell=shared.lower_A`, `sigma=shared.A_slack`, `z=shared.Zminus1` and
`A=ell+sigma`. Its old lower graph was

    P=W(z_old+1),  R=(W+1)P,  ell^2+P^2-R^2=1.

Make the literal substitution

    z_old=2z+1,

so now `P=2W(z+1)`. Every coordinate remains natural, with `z+1>=1`.
This is a cofinal strengthening, not a claim that every old lower witness
has an even second Pell coordinate. Every new witness restores an old one
by the displayed natural substitution.

Let X_j(B),Y_j(B) be the usual Pell coordinates, with B>=2. Classification
of the retained lower norm gives

    ell=X_e(W+1), 2W(z+1)=Y_e(W+1), e>0.

The second-order recurrence

    Y_0=0, Y_1=1, Y_(j+1)=2(W+1)Y_j-Y_(j-1)

reduces modulo 2W to the recurrence for j. Thus
`Y_j(W+1)=j (mod 2W)`, so `2W|e` and `e>=2W`. The Pell recurrence gives
`X_j(W+1)>=(W+1)^j`. Therefore

    A>=ell>4W^(2W),                                      (3)

because W>=2 and the binomial expansion yields
`(1+1/W)^(2W)>4` (its terms through degree two total `5-1/W>4`).

Conversely choose `ell=X_(2W)(W+1)` and
`z+1=Y_(2W)(W+1)/(2W)`, a positive integer. The later common-root choice
of A can still be made arbitrarily large in its unchanged congruence class;
put `sigma=A-ell>=0`. The parent completeness argument already chooses all
semantic atoms, including q and the denominator powers, BEFORE W, ell and A.
Thus the strengthened lower graph introduces no circular choice and costs
no coordinate or row.

## 3. Three-coordinate natural aggregate

The three q-base requests are indexed, in this order, by

    k0=t=2t0+4, k1=c=y+1, k2=x,

with outputs `m0=D_t`, `m1=D_y`, `m2=D_x`. Their explicit affine output
expressions in these endpoint charts are respectively

    1+choose0.modular_remainder+pooled_digits.t0.slack
      +crt.range.index.modular_remainder,
    1+crt.range.S.modular_remainder+pooled_digits.y.slack
      +crt.range.Sp.modular_remainder,
    1+crt.range.u.modular_remainder+pooled_digits.x.slack
      +crt.range.vq.modular_remainder.

Their consecutive pairs are `(Y0,Z0)=(index0.Y,index0.previous_Y)`,
`(Y1,Z1)=(index2.Y,index2.previous_Y)` and
`(Y2,Z2)=(index1.Y,index1.previous_Y)`. All pair norms are retained.
Write `n=q=pow2.output` and `T=2An-n^2-1` in the proof only.
The old graph used the natural T coordinate and three natural quotients h_i:

    T=2An-n^2-1,  nY_i-Z_i=m_i+T h_i.                    (4)

Delete exactly those four coordinates and four rows. Introduce three natural
coordinates U,Mp,K and the three quadratic residual equations

    U=sum_i Y_i^2,
    K=2sum_i Y_i(m_i+Z_i)+(2A-n)Mp-nU,
    sum_i(m_i+Z_i)^2+Mp=nK.                              (5)

Every factor in (5) is an affine expression or an existing coordinate.
In particular no cubic `A sum Y_i^2` occurs. The exact polynomial identity is

    sum_i(m_i+Z_i-nY_i)^2 = T Mp                         (6)

on (5). More precisely, if R0,R1,R2 are its residuals in the displayed order,
then the left side minus `T Mp` is `R2+n R1-n^2 R0`.
The independent checker expands this identity without using a Pell norm.

For canonical true powers and the old nonnegative quotients in (4), choose

    U=sum_i Y_i^2,  Mp=T sum_i h_i^2,
    K=2sum_i Y_i(m_i+Z_i)+(2A-n)Mp-nU.                   (7)

These are integers. U and Mp are nonnegative since T>0. By (6),

    nK=sum_i(m_i+Z_i)^2+Mp>=0,

so K is also natural when n>0. This is a natural-domain construction,
not a signed-witness relaxation. Integrality of K is supplied by its
polynomial formula, not by an unproved divisibility of the last expression.

## 4. Soundness, including the deleted orientation incidence

### 4.1 Authentication order

First restore the shared syntax gates and the old lower-frame coordinate.
The stronger frame proves A-1>W^3 before any exact power is interpreted.
The retained complete positive-center anchor identifies its ordinate at the
unchanged semantic label sum J. The merged error-square row authenticates
all thirteen requested seed ordinates exactly as in the parent.

There is one care needed: for a consecutive natural pair `(Y,Z)` define
`X=AY-Z`. Its retained conic gives `X^2-(A^2-1)Y^2=1`, so `|X|` and Y are
an ordinary nonnegative Pell pair. The merged cap proof only needs that
Y=Y_j(A), j>=0; it bounds j, reduces the sum of squared index errors modulo
A-1, and concludes j=k. Thus it authenticates the ordinate even before the
sign of X is known. The full anchor itself still has its unchanged positive
ordinary coordinates and private witnesses.

For the t and x seeds, a nonnegative output incidence survives: their
individual powers at bases `F^2-1` and B remain. In each case `bY=Z+R`,
R>=0, and `1<=b<A`. If Y=0 the norm gives Z=1, contradicting that row;
otherwise `Z<=bY<AY`, so X>0. The checker verifies these exact incidences.
Every other seed still has its unchanged positive modular-output incidence.
Only the c=y+1 seed loses its sole such incidence when (4) is pooled; it
may initially have either sign of X. We do not assume it is a predecessor.

The three unpooled requests recover the exact powers V, N and q by the
inherited frame argument. In particular `n=q>=1`; their base-positive
modulus rows and positive exponents are retained. This precedes interpreting
the pooled outputs. The literal frame gives `n,m_i,k_i<=W`. Therefore

    T=2An-n^2-1>=2A-W^2-1>A>4W^(2W)>0.                  (8)

### 4.2 Cleared errors and the additive frame budget

Let `c=y+1>=1`. Besides individual bounds, the literal frame satisfies

    c+t<=W-1, c+x<=W-1, 2c<=W-1, c+1<=W-1.             (9)

These are exact coefficientwise nonnegative polynomial differences in the
203-coordinate chart. In the projected charts first expand the retained
`add.594` row and then use the retained cofinal/floor identity
`F+F*r+F*s+r=y+1`; the same differences are coefficientwise nonnegative.
The checker verifies all four inequalities without factorial, binomial or
power assumptions. Its receipts include the literal and expanded frame.
This is why the frame factor 2 suffices despite the possible inverse power.

Modulo T, let `s=n-A`. Then `s^2=A^2-1 (mod T)`. For a canonical Pell pair
at k, the standard recurrence gives

    X_k+sY_k = n^k (mod T).

The conjugate has product one with it modulo T, so
`X_k-sY_k=n^(-k) (mod T)`, with inverses legitimate because `T=-1 (mod n)`.
For the actual signed abscissa `X=epsilon X_k`, `epsilon in {1,-1}`,

    nY-Z = n^k              (mod T) if epsilon=1,
    nY-Z = -n^(-k)          (mod T) if epsilon=-1.        (10)

The t and x signs are positive by Section 4.1. Multiply the errors in (6)
by n^c. Their three ordinary integer residues may be taken as

    delta0=m0*n^c-n^(c+t),
    delta2=m2*n^c-n^(c+x),
    delta1=m1*n^c-n^(2c)   if the c sign is positive,
           m1*n^c+1        if the c sign is negative.   (11)

Thus T divides `E=delta0^2+delta1^2+delta2^2`. By (9), each power term
and each `m_i*n^c` is at most `W^(W-1)`; 1 satisfies the same bound. Hence

    0<=E<=12W^(2W-2)<=3W^(2W)<T.                        (12)

The only divisible value is E=0. In the negative c case,
`delta1=m1*n^c+1>0`, a contradiction. Thus the c pair is also correctly
oriented. Each zero in (11) now gives `m_i=n^(k_i)` after canceling the
positive integer n^c. This recovers all three exact powers and the missing
predecessor orientation, without using either conclusion prematurely.

### 4.3 Restore the complete parent graph

The ordinary positive-power recurrence gives

    nY_k(A)-Y_(k-1)(A)-n^k
      =T sum_(j=0..k-1) n^(k-1-j)Y_j(A).

Therefore every old h_i in (4) is an explicitly defined nonnegative integer.
T is natural by (8). Restore those four coordinates, all shared syntax wires,
and `z_old=2z+1`. This recovers every row of the complete parent natural
system. In particular its local source-evaluation row was never dropped.
Parent soundness then recovers, in its proved acyclic order, the descending
even-horizon factorial identity, carry-free modular binomial ranges,
reciprocal CRT decoding, the identical local nonnegative source, factorial-
weight Horn flow, and the calibrated finite syntactic ZFC refutation.

## 5. Completeness and the exact logical boundary

Start with a finite syntactic refutation and use the retained round20
constructive completeness theorem. Choose the even horizon, F=t!, beta
representatives and x, then N, then the precision-N^2 CRT column lifts with
the canonical sign orientation. The unchanged derived-label sum supplies
the semantic anchor dominance. Choose the self-sized radix q and all exact
denominator powers, then the semantic frame W.

At this point replace the parent's auxiliary lower Pell choice by the one
in Section 2, with index 2W. Choose A in the same common-root congruence
class, sufficiently large above this new lower bound. The complete indexed
anchor and all canonical seed pairs and modular quotients are chosen afresh
at A, exactly as in the parent. The merged-error completeness estimate is
only strengthened by larger A. All representatives and local source signs
were fixed earlier and are unchanged. Define G by Section 1 and U,Mp,K by
(7). Every new coordinate is natural and all new rows hold. This completes
refutation-to-zero without claiming an arbitrary old auxiliary tuple lifts.

All arguments use ordinary finite polynomial identities, Pell recurrences,
Pell-solution classification, finite CRT choices and arithmetic induction.
They are formalizable in the internal natural numbers of ZFC and use no
assumption of consistency or arithmetic soundness. Composition with the
explicit retained C222/ZF/ZFC calibration gives the stated no-zero/Con(ZFC)
equivalence. The finite standard-library verifiers independently reproduce
all rows and all coefficients, but are not represented as proving this
unbounded theorem or the inherited proof-assistant closure.
