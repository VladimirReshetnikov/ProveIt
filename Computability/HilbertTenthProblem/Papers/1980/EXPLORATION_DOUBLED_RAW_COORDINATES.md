# Doubled raw coordinates: a separate 105-operation construction

This construction starts from the complete positive-Z106 family in
`EXPLORATION_FACTORED_RAW_BLOCKS.md`. It doubles all raw coordinates,
including the repunit parameter, so the existing Pell-index register
can impose the packed equation without a final doubling. The count is
**105 operations: 56 multiplications and49 additions/subtractions**,
with34 positive unknowns and22 equations. The existing universal
frontier remains90. This is not a composition with either the eliminated
zero word or the complemented counter guards.

The source/checker is `../verification/explore_doubled_raw_coordinates.py/.json`.
All fixed numerals and the marked cyclic compiler remain unchanged.
The first prefix state has sign plus and nozero label one; these labels
are valid for its initial positive counter value2x. The next prefix lane
still carries its compulsory true-zero annotation.

The proof requires an additional carry argument. A ternary word with
digits zero or two has maximum q-1, so the earlier half-alphabet range
argument cannot simply be reused. In particular an isolated odd track
can be hidden by a carry from its guard. Section5 excludes that carry
using the actual initial input residue.

## 1. Source equations and the saving

Use the same source names as106. Here J,H,T,A0,A1,Kp,Km,Z,D,C,V denote
twice the old values. Write

    TC=C+J-SH, TV=V+Zstar H,
    Bprog=(1+q²)(C+qV)+q²[J+(q Zstar-S)H],
    Rest=Km+q Z+q²D+q³Bprog,
    G=(q+1)(A0+q²A1)+(1+q²)T,
    P=Kp+q(G+q4 Rest), L=q12.

Thus P has the same twelve conceptual fields

    Kp,A0+T,A0,A1+T,A1,Km,Z,D,C,V,TC,TV.

Its fields are eventually proved to be doubled Boolean words. The
retained outer sources are

    q=J+1, q=Wv, W=R³, H(R-1)=2J,
    Kp+Km=H, Z+D=H, 6(J-T)=(R-3)D,
    W(A0+A1+Kp-Km)=A0+A1-4x,
    4x+alphaI=R,
    (RK-g)C=(gI)(2J)+R(V+hs Kp+hz D),
    2r+1=L+P, r+beta=L.

The ten43-operation fixed-sign Pell sources are unchanged, with scale
D0=L. The mathematical TC/TV definitions are incorporated by the same
program factorization; the conceptual guards are incorporated by G.

The schedule changes only three instructions of106. Its q right side
uses J+1 in place of twice_J+1; twice_J=2J is still used by the head and
route equations. The input instruction becomes the single product4*x
instead of x+x. Finally delete the addition doubling the complete raw
packed word, and use L+P in the packed-index right side. Thus the count
is106-1=105, with one old addition replaced by a multiplication:

    55M+51A -1A -1A +1M =56M+49A.

The input bound is intentionally stronger than the divided predecessor
bound. The converse may choose a wider radix, rather than claiming a
same-width witness bijection for every predecessor solution.

## 2. All bounds before the Pell kernel

Initially J>0 implies q>=2, not necessarily that q is odd. The input
bound gives R>=5; W=R³ and q=Wv give q>=125. These facts do not depend
on a digit interpretation.

The lower eight-field polynomial is positive, since T,Ai and all flags
are positive. Let it be L8. Exactly as for the program factorization,
put Q*=V+(Zstar-S)H>0. Then

    P-Q*q11
      =L8+Cq8+Vq9+(C+J)q10+SH(q11-q10)>0.

From2r+1=L+P and r+beta=L one gets0<P<=L-1. Now
floor((L-1)/q11)=q-1=J, so Q*<=J. The fixed Zstar>3S gives J>SH,
and consequently TC=C+J-SH>0. Also TV>0 directly. All twelve
conceptual fields are now positive, so the top-field bound yields

    TV<=J, R-1=2J/H>2Zstar.

The original fresh high forbidden bit therefore still gives R>=9,
H<=J/4, q>=R³ and the fixed program-width inequalities. It also gives
R>2gI and R>g: the fixed construction has Zstar>gS>=gI.

The positive flag pairs imply0<Kp,Km,Z,D<H. The top equation gives
0<T<J. Put A=A0+A1>0 and delta=Kp-Km>-H. The time equation implies

    A<WH/(W-1)<9J/32.

In particular Ai+1<q and0<Ai+T<2q. A guard may exceed q, but its
following track cannot propagate an extra carry beyond that track.

For the route, O=V+hs Kp+hz D<TV<=J<q and V<TV<=J. Because K>=3,
R>g and R>2gI, one has RK-g>2gI+R. Therefore the route equation,
whose right side is less than(2gI+R)q, forces C<q. The possibly
larger test word has0<TC<q+J<2q.

Finally P>q11 and r=(L+P-1)/2>q11, while r<L. Thus
D0=L>=81, r>=27, r<2D0 and D0<r². These are every preliminary
hypothesis of the same43-operation kernel. Its soundness requires no
prior parity assumption on r. It recovers q as a power of three and
L dividing the central binomial coefficient of r.

## 3. Geometry and the doubled mask

Write q=3^e. Since R³ divides q and R>1, R=3^m for some m>=1.
The retained equation H(R-1)=2(q-1) suffices to recover whole rows;
one must not assume divisibility by R-1 after cancelling2 without proof.
Write e=um+s with0<=s<m. Reduction modulo R-1 gives

    R-1 divides2(3^s-1),
    0<=2(3^s-1)<=2(R/3-1)<R-1.

Hence s=0, q=R^u, u>=3, and H=2(1+R+...+R^(u-1)) is even.
Also J=q-1 is even. R>=9 means m>=2.

Because r<L, the direct native-mask theorem says that r has only
ternary digits one or two and its unit digit is two. Let
j=(q-1)/2 and jwide=(L-1)/2. Then

    P=2r+1-L=2(r-jwide).

The subtraction r-jwide has no borrow and has only digits zero or one.
Consequently P has only ternary digits zero or two, including unit
digit two. Every base-q chunk is therefore even and at most q-1.
Dividing such a chunk by2 gives a Boolean ternary word.

## 4. Decode the controller before the two tracks

The first field Kp is below H<q. Each following guard/track pair
has the form(Ai+T)+q Ai, with0<Ai+T<2q and Ai+1<q. Its only
possible internal carry is ci=0 or1, and it has no outgoing carry.
Therefore both pairs can be passed without assuming ci=0. The
following Km,Z,D,C,V fields, each positive and below q, are their
actual even chunks. In particular all five are even, as is Kp.

The program field TC=C+J-SH is now even. It is positive and below2q.
If it were at least q, its low chunk TC-q would be odd because q is
odd, contradicting the doubled mask. Thus TC<q. It and TV decode
without a carry, and both are even.

Divide these typed flags and program coordinates, along with J,H,
by2. The two head-pair equations and the whole marked-ROM equations
become precisely their106 equations. The support tests, fixed
coefficient bounds, marker count and one-state induction therefore
recover a genuine controller path and both labels independently of
any counter-track interpretation. The initial source vertex is the
fixed prefix state with nozero label one. It follows that D/2 has
unit digit one. This is a controller-label conclusion, not an
assumption that a still-undecoded counter is nonzero.

As D is even, write d=D/2. Since(R-3)/6 is an integer, the top source
also gives T even. With

    k=(R-3)/6=(3^(m-1)-1)/2,
    E=k d, t=T/2=j-E,

the word E is Boolean: k consists of m-1 consecutive one digits,
and d is a subset of row heads, whose copies do not overlap. In
the first R-block, E has the value h=(R/3-1)/2 because d's unit
head is one.

## 5. The initial input excludes both possible guard carries

Let ci be the internal carry of guard pair i. Its high doubled
chunk is Ai+ci, so write Ai=2ai-ci with ai Boolean. Its low
doubled chunk, divided by2, is

    ai+t-ci(q+1)/2.

If ci=0, then ai+(j-E) is Boolean. Both summands are Boolean and
their ternary sum has no carry; Booleanity means disjoint supports.
Thus ai is supported on E. Its first R-block lies between0 and h,
and the actual Ai residue is even, between0 and2h=R/3-1.

If ci=1, the low half-chunk is bi=ai-E-1, also Boolean. Thus
ai-bi=E+1. Let a,b be their first R-block values. Their difference
is congruent to h+1 modulo R and lies between-(R-1)/2 and(R-1)/2.
Therefore a-b=h+1, with no extra multiple of R. Split each Boolean
block into its highest trit and its lower m-1 trits. Equal highest
trits permit difference at most h, so they cannot occur. A smaller
highest trit for a gives a negative difference. Hence a has top
trit one and b has top trit zero. Their lower parts must differ
by-h, forcing a=R/3 and b=h. The actual track residue is exactly

    Ai mod R=2R/3-1.

If exactly one guard carries, the two actual track residues have
an odd sum below R. Hence A mod R is odd. If both carry, their sum
is4R/3-2; subtracting R gives R/3-2, again odd. But the time equation
implies A congruent to4x modulo W, and hence modulo R. The paid
bound gives0<4x<R, so A mod R=4x is even. This contradiction excludes
every guard carry. Both ci are zero.

All raw tracks and guards are consequently even actual chunks.
Together with the already decoded fields, every conceptual coordinate
is twice a positive Boolean word. Dividing J,H,T,Ai,Kp,Km,Z,D,C,V
and their computed guards/test words by2 therefore restores the full
positive106 outer system. The old input slack is
alphaI_old=alphaI_new+2x>0. The packed index r, beta and all Pell
coordinates are unchanged. Every source is the old divided source
or twice that source; the checker records the factors explicitly.
The complete old history/first-return theorem now proves acceptance
of the same ordinary input x.

## 6. Converse and scope

Given an accepting canonical106 history, choose its power-of-three
radix sufficiently wide that R>4x in addition to the existing bounds.
Double the eleven named coordinates and the twelve conceptual fields;
set alphaI=R-4x. All supplied coordinates remain strictly positive.
The source equations follow by scaling. P is twice the old raw word,
so the new equation2r+1=L+P uses exactly the old packed index r.
Its parity, unit condition, native divisibility and positive fixed-sign
Pell construction are unchanged at this chosen frame. Thus the new
system represents the same recursively enumerable set with ordinary
raw input and105 counted operations.

This is semantic equivalence with a stronger width condition in the
forward construction. It is not a claim that every old small-width
witness satisfies the new input bound. It is also not a proof of
composition with a negative reconstructed zero word or complemented
guards; their changed carry cases are explicitly outside this result.

The checker supplies every fresh source comparison, the conditional
divided-coordinate polynomial transport, finite geometry and first-block
carry regressions, and two fresh complete canonical outer tuples with
exact central valuations. It includes an isolated odd-track guard alias
to document why the global initial-residue argument is necessary.
Enormous Pell coordinates are supplied by the general positive converse,
not by the finite checker. Full independent proof/source reviews and
fresh complete verification pass.
