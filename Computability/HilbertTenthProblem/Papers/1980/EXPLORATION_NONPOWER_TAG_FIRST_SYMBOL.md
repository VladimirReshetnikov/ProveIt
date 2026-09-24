# The first tag symbol can be recovered without a power radix

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings on the corrected proof.
The proof and arithmetic are frozen.

This is a conditional structural lemma for the weakened104 tag interface.
It assumes its ten individual Boolean masks explicitly and proves neither
full104 soundness nor an operation saving. The radix R need not be a power
of three. Even so, the least length marker is the specified initial marker,
the first selector is the actual first input symbol. Under the additional
hypothesis that H itself is Boolean, a first-one input has its entire
initial content and deleted prefix recovered in the lowest 3-adic block.
No later-history induction is claimed.

The separate complete nonpower family in
`EXPLORATION_TAG_RADIX_DIVISIBILITY_OMISSION.md` remains unchanged.

## 1. Hypotheses and exact sources used

Use the constants and original encoded-input convention from
`EXPLORATION_GENERAL_SCALED_TAG_TRANSPORT.md`:

    K=3^beta, Kh=K/3, B=3^(a-1), a>=2,
    C=3^c>max(K,3^a,2U+3), cc=(Kh-1)/2,
    Li=3^ell, ell>=beta, 0<=Ni<Li/2.

The input Ni is Boolean ternary. The fixed symbol epsilon=U mod3 is zero
or one. Assume positive A,R,q,H with

    R=CA, H(R-1)=q-1, q a power of three, A>Li.

Thus q>=R, c>=beta+1, and m=v3(R)>=c. All ten words

    Gstar,Q,S0,S1,M0,M1,Ebar,E,Nbar,N

are nonnegative Boolean ternary integers less than q. Retain

    S0+S1=H, 2Q+S1=M1, Gstar=Q+AH+S0,
    L=M0+M1=2(N+Nbar)+H, E+Ebar=ccH,
    R[L+(B-1)M1]=Kh(L-Li+q Lf),
    R(N-3E-S1+UM1)=K(N-Ni+q Nf).

The two generic content branches imply respectively

    epsilon=0: N=3T+S1,
    epsilon=1: N=3T-2Q.

Only their congruences modulo3 are used below. All assertions concern
these exact integer equations, without treating multiplication by R as
a ternary shift.

For the intrinsic divisibility conclusion below, also retain the full
packed mask's fixed unit condition Gstar=1 modulo3. This condition is
separate from merely being a Boolean word.

## 2. The least length marker and the first symbol

Let T0=R/Kh, a positive integer divisible by three. The length equation
is exactly

    L+q Lf=Li+T0 M0+B T0 M1.                         (1)

Because M0 and M1 are Boolean, their sum L has literal digits at most2
and no ternary carries. Let j be its least occupied exponent. The least
possible exponent of either product on the right of(1) is strictly above
j. Also ell<log_3(q), because Li<A<R<=q.

If j<ell, the nonzero coefficient of L at j cannot be matched on the
right. If j>ell, the initial unit at ell cannot be matched on the left.
Thus j=ell. Both products vanish modulo3^(ell+1), so the coefficient of
L there is exactly1. This proves

    v3(L)=ell, digit_ell(L)=1.                         (2)

In particular M1 has unit digit0. Reducing 2Q+S1=M1 modulo3, with both
Q and S1 Boolean, gives Q_0=S1_0. Either generic content branch therefore
gives N=S1_0 modulo3. Dividing the content equation by K is legitimate,
and R/K is divisible by three because C>K. Since q is also divisible by
three, that equation gives N=Ni modulo3. Consequently

    S1_0=Q_0=Ni mod3.                                (3)

Thus the first selector cannot be changed by the nonpower-radix freedom.

There is also a new intrinsic divisibility constraint. Geometry gives
H=1 modulo3. Since Q=S1 modulo3,

    Gstar=AH+H+Q-S1=A+1 modulo3.

The fixed unit1 condition therefore forces **3|A**, or equivalently
v3(R)>=c+1, without assuming H Boolean. This rules out geometries with
v3(R)=c before any later-row interpretation.

## 3. A first-one input forces enough 3-adic space

For this section and Section4, add the explicit hypothesis that **H is
Boolean ternary**. The equation S0+S1=H does not establish that hypothesis:
the two Boolean words can have common occupied digits, giving H digits2.
No general recovery of H's Boolean property from the weakened104 source
is claimed here. Sections1--2 do not need it.

Set h=3^m. Geometry modulo h gives H=1 modulo h. Its Boolean digits
therefore have no occupied positions strictly between0 and m.
Moreover R/h=1 modulo3. To see this, if q>h, reduce geometry modulo3h:
H=1+R modulo3h, so its digit at m is the nonzero residue of R/h and
must be1. If q=h, q>=R and v3(R)=m imply R=q, which gives the same result.

It follows that AH has its first occupied digit1 at position m-c.
Suppose Ni has first symbol1. Equation(3) gives Q_0=S1_0=1 and S0_0=0.
If m=c, Gstar would have unit digit2, impossible. Thus m>c.

Write j0=m-c, so 0<j0<m. Before j0 there are no nonunit H bits and no
AH bits. The addition defining Gstar has no carry before j0; at j0 its
digit is 1+Q_j0, because S0_j0=0. The Boolean mask therefore forces
Q_j0=0.

The carry in 2Q+S1=M1 starts at position0. Until its first M1 marker it
continues through Q digits1, since a zero Q digit ends it by emitting
an M1 digit1. There are no intervening S1 bits before j0. By(2), M1
has no digit below ell. Thus ell>j0 is impossible, and

    ell<=m-c,  m>=c+ell.                             (4)

At this stage it has not yet been proved that the marker at ell belongs
to M1. The carry could, on these facts alone, pass an M0 marker before
ending at a later M1 marker. The length transport resolves that order next.

## 4. Recover the initial content and its deleted prefix

Both M0 and M1 have no occupied digit below ell by(2). Without assuming
which channel contains the marker at ell, the lowest possible exponent
in T0 M0 is therefore at least

    (m-beta+1)+ell>=m+1.

For B T0 M1 it is at least

    (a-1)+(m-beta+1)+ell=m+ell+a-beta>=m+2.

Reduce(1) modulo h. Since h divides q and Li<h by(4), this first gives

    L mod h=Li.

The sum M0+M1 has no ternary carries, so the marker at ell is their only
occupied digit below m, in exactly one channel. The Q carry starts at0
and must end by j0<m, as proved in Section3. Its ending emits an M1
marker below m. That marker must consequently be the unique one at ell.
Only now do we conclude

    L mod h=Li, M0 mod h=0, M1 mod h=Li.              (5)

Put Ns=N+Nbar. Its addition has no ternary carry because both summands
are Boolean. Containment gives 2Ns+H=L. If b=Ns mod h, then
2b+1=Li modulo h with 0<=b<h. The possible extra carry1 is excluded
by parity: 2b+1 and Li are odd, whereas h is odd. Hence

    Ns mod h=(Li-1)/2,
    0<=N mod h<Li/2.                                (6)

The content equation divided by K gives N=Ni modulo h/K. By(4) and
C>K, both N mod h and Ni are strictly below h/K. Therefore

    N mod h=Ni.                                     (7)

The prefix masks give E mod h as a subset of cc, since H=1 modulo h.
Thus d0=(3E+S1) mod h is between0 and K-1. Equation(7) implies that
the right side of the divided content equation is divisible by h.
Writing R=h dR with dR coprime to3, its left side is

    (h/K)dR (N-3E-S1+UM1).

It follows that K divides the parenthesized expression. Equation(5)
and K|Li now give d0=Ni modulo K. Its range identifies the exact deleted
prefix:

    d0=Ni mod K.                                    (8)

The first selected length, content, read symbol and deleted prefix are
therefore all correct. This establishes a genuine first tag step for a
first-one input, but does not identify any later encoded block with its
successor. That remaining implication cannot be obtained by treating R
as a power of three.

## 5. The zero-leading boundary is still open

Equation(3) holds for first-zero inputs too, but the Q carry used in(4)
does not start. One must not assume Nsum=N+Nbar is Boolean. For example

    H=28=1+27, L=324=81+243,
    N=121=1+3+9+27+81, Nbar=27

satisfy 2(N+Nbar)+H=L with both content words Boolean and both length
markers Boolean. The first L exponent is4, above the first nonunit H
exponent3. At the second H bit, the content-sum digit2 permits an
outgoing carry2. This is a local containment example only: no length
transport or complete source tuple is asserted for it.

Thus neither arbitrary zero-leading first-row recovery nor the stronger
first-one statement for non-Boolean H nor full104 halting semantics is
established here.

## 6. Fresh checks and scope

`../verification/explore_nonpower_tag_first_symbol.py` checks300 exact
length tuples, including189 with a nonpower multiplier T0, for(2).
It separately constructs776 complete ordinary tag histories containing
2,006 source rows. The first-one conclusions(4)--(8) execute on338
histories, all with Boolean H;438 start with zero. The232 runs reaching the test cutoff
remain unclassified. It also checks the first-symbol conclusions on
three complete positive nonpower-radix families from the predecessor.

The checker additionally records a local projector example with H=55,
S0=28, S1=27, Q=0, C=27, q=3^20, R=63396081 and A=2348003.
Its geometry and Boolean projector words hold, but H has a digit2.
Its Gstar has unit0, so it fails the full kernel's fixed unit1 requirement;
this is only a local warning against silently deriving H's Boolean type.

The existing full outer-source and Pell proofs are not replaced by these
tests. The ten separate masks are explicit hypotheses of this lemma,
and the stronger assertion separately assumes Boolean H;
no new mask-realization count, universal bound, or later causal-prefix
claim is being supplied.
