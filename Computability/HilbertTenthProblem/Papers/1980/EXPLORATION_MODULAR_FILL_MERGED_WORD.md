# A modular filling lemma for a merged program word

This note concerns the proposed replacement of separate state and junk
masks by a mask on `F=C+V` and its complement in a fixed allowed word.
It gives an exact general way to satisfy the resulting scalar route for
an arbitrarily prescribed numerical counter trace, once enough neutral
loops are appended. This is an obstruction to that proposed interface,
not a defect in the published 101-operation construction, which keeps
the separate program fields.

The general lemma below does not assume a Sidon controller. Its toy
regression materializes complete counter words and their merged route,
but its toy constants are not asserted to be a compiled universal or
empty controller. Applying the lemma to an actual compiled graph is a
separate proof obligation.

## 1. Scalar route and allowed optional digits

Fix positive integers R,g,K,I,hs,hz, where R and g are powers of three,
g divides R, and

    T=R/g,   d=(K+1)T-1>1.

Assume T>1, so d is coprime to three and to R. Choose a Boolean ternary
word U<R, and one of its occupied digits c=3^a. Put B=U-c>0. Suppose

    (TK-1)B > T(hs+hz)+I(R-1).                            (1)

Fix a prefix of h rows and a repeatable neutral counter loop of p rows.
Let L be the multiplicative order of R^p modulo d and choose

    n=dL,   u=h+pn,   q=R^u,   H=(q-1)/(R-1).

The numerical trace determines Kplus and D, with
`0<=Kplus,D<=H`. It may also determine other fields; they do not enter
the filling step and will not be modified. The loop must preserve the
numerical endpoint, so its repeated insertion is legitimate independently
of the proposed controller mask.

Start with Fbase=B H. Select the n loop rows at offset zero, and retain
the following d positions among them:

    b_j=h+pLj,       0<=j<d.

At each retained position there is an independent option to add c R^b_j.
These positions lie inside the trace, and their optional trits are absent
from Fbase. Since R^(pL)=1 modulo d, all options change

    N(F)=T(F+hs*Kplus+hz*D)+I(q-1)

by the same unit

    w=T c R^h modulo d.

Choose the unique integer M with `0<=M<d` satisfying

    M w = -N(Fbase) modulo d,

and add the first M optional trits. Then d divides N(F), exactly. Define

    C=N(F)/d,   V=F-C.                                    (2)

Both are strictly positive integers. C is positive because N(F)>0.
For V, use F>=BH, Kplus,D<=H, and q-1=(R-1)H to get

    dF-N(F)
      =(TK-1)F-T(hs*Kplus+hz*D)-I(q-1)
      >=H[(TK-1)B-T(hs+hz)-I(R-1)]>0.

Thus `0<C<F` and `V>0`. Both F and UH-F are Boolean words below q:
at each row they are respectively B or U, and c or zero. No borrowing,
overlapping digits, or probabilistic search enters this construction.

Finally (2) is equivalent to the original route with the merged word:

    (RK-g)C=gI(q-1)+R(V+hs*Kplus+hz*D),
    F=C+V.                                                (3)

Indeed multiplying dC=N(F) by g and substituting F=C+V gives (3).
The construction therefore satisfies the route for every prescribed
choice of numerical labels in the stated bounds. Those labels need not
come from a compatible path in the intended controller. Proving that C
and V nevertheless have the original separate supports would require
an additional condition not present in this merged scalar interface.

## 2. A repeatable numerical trace with fixed small input

The following trace starts at [2,0,0], representing ordinary input x=1,
and ends at zero. Its first twelve serial signs, with phases cycling
0,1,2, are

    +++--- -++---.

The first six restore [2,0,0]; the next six decrease the first counter
by two and leave the others zero. Append n copies of +++---, each of
which takes [0,0,0] back to itself. Every update is nonnegative. Declare
the sole zero request at row one, where the second counter is zero.
Both signs, the zero word Z, and its complement D are strictly positive.
The maximum source value is three, independently of n.

For any R>=27, split every source value into two Boolean ternary tracks
A0,A1. Their initial value two ensures both tracks are positive. With
J=(q-1)/2 and t=(R-3)D/6, the four fields

    t-A0, A0, t-A1, A1

are Boolean: at each nonzero-request row t is the all-one lower
m-1-digit interval, and both tracks fit there; at the only zero request
both tracks are zero. The signs satisfy Kplus+Kminus=H, and Z+D=H.
The ordinary three-counter telescoping identity gives

    R^3(A0+A1+Kplus-Kminus)=A0+A1-2x.                     (4)

The paid input bound 2x<R holds. Thus increasing the number of loops
does not enlarge x or any source counter, unlike repeating a loop
whose net decrement would require an input proportional to its duration.

The modular filling changes only F,C,V and leaves these counter masks,
the time equation, input and zero tests intact. An actual fixed-graph
application must still supply U,c and the inequality (1), and distinguish
the intended accepted language from this constructed numerical trace.

## 3. Packed-index completion is independent of the route's correctness

For this trace u is even. Pack the ten Boolean fields

    Kplus,Kminus,Z,D,t-A0,A0,t-A1,A1,UH-F,F

in base q, obtaining P, and set scale=q^10 and r=P+(scale-1)/2.
The first raw digit is one because the first sign is plus. Hence r has
native ternary digits one or two and unit digit two. It satisfies
`r<scale<r^2` and the exact valuation

    v_3 binom(2r,r)=10mu,       R=3^m.

The ten fields have total `2H+2t+UH`, which is even because u and H
are even. Thus P and the added wide repunit are even, giving even r.
The general positive fixed-sign 43-operation kernel converse applies.
It supplies all positive kernel witnesses for this packed word without
asserting that its purported controller interpretation is correct.

## 4. Exact toy evidence and its limit

The companion `../verification/explore_modular_fill_merged_word.py/.json`
uses R=81,g=27,K=7,I=1,hs=1,hz=3,U=40,c=1. Here T=3,d=23 and
the left-minus-right margin of (1) is 688. It materializes the entire
trace, all ten masks, the chosen optional digits, positive C and V,
the exact route and time equations, and the packed index. It also checks
the abstract residue-filling argument over several small coprime moduli.

These constants provide an exact arithmetic example, not an instance
of the fixed Sidon controller. The classification of that toy's C/V
digits is not used as a universality or empty-language counterexample.
The enormous Pell auxiliaries are provided by the general converse;
the toy regression computes their scale/index conditions and valuation,
not the auxiliaries themselves. No operation reduction is claimed.
