# Soundness of the short-geometry deletion-two tag case

Status: author and two independent complete proof/source reviews and fresh
verification runs passed without findings. The proof and arithmetic are
frozen. The published104 omission source and all predecessors are unchanged.

Every positive solution of the weakened104 source with

    beta=2, appendant length a>=2, R>=28H

specifies one of the two input words **00 or01**, in the established
leftmost-symbol-first convention. Both halt after one actual tag step,
regardless of the fixed appendant. This is a soundness theorem for the
stated range. It does not assume that R is a power of three or that H is
a Boolean ternary word.

The condition R>=28H is a theorem hypothesis, not an uncharged arithmetic
comparison added to the104 certificate. No unrestricted104 halting
equivalence or universal operation bound is claimed. The proof also gives
ordinary H=1 complete witnesses for both inputs, but makes no assertion
that there is a nonpower-R witness in this deletion-two range.

## 1. Retained equations and established structural facts

Use the exact source from `EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md`.
For beta=2 put

    K=9, Kh=3, B=3^(a-1), C=3^c>=27,
    Li=3^ell, ell>=2, 0<=Ni<Li/2,
    R=CA, A>Li, H(R-1)=q-1.

The original input Ni is Boolean ternary. The kernel and scalar field
recovery give q a power of three and the ten separate Boolean fields.
In particular M0,M1 and Gstar are Boolean, Gstar has unit trit1, and

    L=M0+M1=2(N+Nbar)+H,
    M1=2Q+S1, S0+S1=H, Gstar=Q+AH+S0.

The terminal theorem `EXPLORATION_TAG_TERMINAL_RESTRICTIONS.md` applies
in this range and supplies

    Lf=3,
    O=L+(B-1)M1=9H,
    L=Li+3(H-1).                                       (1)

The unconditional part of `EXPLORATION_NONPOWER_TAG_FIRST_SYMBOL.md`
supplies

    v3(L)=ell, digit_ell(L)=1,
    no M0 or M1 digit occurs below ell,
    S1 mod3=Ni mod3,
    3|A.                                                (2)

These assertions use neither H Boolean nor R a power. In particular the
stronger first-one conclusions of that note are not being imported with
their Boolean-H hypothesis omitted.

Subtract the equations in(1) to obtain the exact marker relation

    (B-1)M1=6H+3-Li.                                   (3)

## 2. The input has exactly two symbols

First suppose H=1. Geometry gives q=R. Equations(1) reduce to L=Li and
Li+(B-1)M1=9. Since Li>=9 and M1>=0, they force

    Li=9, M1=0.                                        (4)

Now suppose H>1. Let m=v3(R) and write R=3^m dR with 3 not dividing dR.
Since q>R and q is a power of three, its exponent is strictly larger
than m. The exact geometry identity

    (R-1)(H-1)=q-R

therefore gives

    v3(H-1)=m, (H-1)/3^m=dR modulo3.                   (5)

Write h=3^m. By(1), L=3^ell+3(H-1). If ell>m+1 its least exponent is
m+1, contradicting(2). If ell=m+1, its coefficient there is
1+dR modulo3, which is either2 or0 rather than the required1. Hence

    ell<=m.                                             (6)

If ell>2, the right side of(3), written as 9-Li+6(H-1), has valuation
exactly2: its first term has that valuation, while the latter term has
valuation m+1>=ell+1. Since B-1 is not divisible by3, this would give
v3(M1)=2<ell, contradicting the absence of low M1 digits in(2).
Thus ell=2, proving Li=9 in both cases.

## 3. The first symbol is zero without assuming H Boolean

For H=1, equation(4) and M1=2Q+S1 with nonnegative Q,S1 give S1=0.
The first-symbol identity in(2) then gives Ni=0 modulo3.

For H>1, substitute Li=9 into(3):

    (B-1)M1=6(H-1).                                    (7)

The right side is positive. Since B-1=2 modulo3, equations(5)--(7) give

    v3(M1)=m+1,
    M1/3^(m+1)=dR modulo3.                             (8)

The nonzero leading trit of the Boolean word M1 is1. Thus dR=1 modulo3.
This is the local leading-radix fact needed below. It has been derived
from M1, not from an assumption that all of H is Boolean.

Set j0=m-c=v3(A). The unit condition in(2) gives j0>=1, and c>=3 gives
j0<m. Geometry implies H=1 modulo h. Consequently both Boolean head
fields have zero digits at every position strictly between0 and m.
Also AH has its first nonzero trit at j0, and that trit is1 by(8).

Suppose for contradiction that the first selector is1. Then S1_0=1
and S0_0=0. The equation 2Q+S1=M1 starts a carry at the unit position.
Since M1 has no occupied trit below m+1 by(8), and S1 has no other trit
below m, this carry forces Q to have trit1 at every position0,...,m-1.

In the addition Gstar=Q+AH+S0, there is no carry below j0: only those Q
trits occur there. At j0 the summands give exactly1+1+0=2, contradicting
the Boolean mask on Gstar. Hence S1_0=0, and(2) gives Ni=0 modulo3.

We have proved Li=9 and first symbol zero for every a>=2. The proof uses
only B-1=2 modulo3; it is not restricted to the two-symbol appendant case.

## 4. Actual halting and positive witnesses

An encoded Boolean word of length two with first symbol zero is either
00 or01, with Ni=0 or3 respectively. Deleting its two symbols and applying
the rule 0->0 leaves the one-symbol word0. Thus both actual computations
halt in exactly one step, independently of the other appendant.

Conversely these two inputs have complete positive witnesses within the
range. Choose any sufficiently large power of three A>9, set R=CA,
q=R and H=1, and let e=Ni/3 in{0,1}. Use

    Q=S1=M1=0, S0=1, M0=L=9,
    N=Ni, Nbar=4-Ni, Nsum=4,
    E=e, Ebar=1-e, Gstar=A+1,
    Nfinal=0, Lfinal=3, T=e.

Both fixed generic content branches reconstruct N=3T because Q=S1=0.
Their content output T-E+U3*M1 is zero. The length source is
(R/3)*9=3q. All other outer sources and all ten masks hold. Positive
adapters equal one where a raw word vanishes, and the boundary slacks
A-9 and6 are positive. R>=28H follows by choosing A sufficiently large.

Let P be the unchanged ten-field packing and set

    D0=q^10, r=P+(D0-1)/2, betaP=D0-r.

The unit Gstar bit and Boolean masks give the exact native valuation;
all hypotheses of the general44 positive converse hold. It supplies the
seventeen positive Pell auxiliaries. The witnesses constructed here use
the power radix R=q; their role is to show that the scoped theorem is
nonvacuous, not to assert a new nonpower family.

## 5. Source checks and bounded evidence

`explore_tag_short_geometry_soundness.py` freshly verifies both complete
104 schedules and all40 source comparisons through the existing omission
checker. It expands the exact marker and geometry identities used above.

The separate finite tests check the least-marker valuation argument with
both possible nonzero leading units of H-1, exact integer marker quotients,
and exhaustive Boolean low Q words for the local guard contradiction.
They are explicitly structural tests, not asserted complete nonpower
source tuples.

Finally the checker constructs complete positive outer witnesses for
both actual inputs, every binary appendant of lengths2,...,5, and three
widths. It checks all nine outer comparisons, all ten masks, the actual
one-step computations, exact valuations and the generic44 hypotheses.
The huge positive Pell auxiliaries are supplied by the theorem rather
than materialized. General tuples with R<28H and unrestricted weakened104
halting semantics remain outside this result.
