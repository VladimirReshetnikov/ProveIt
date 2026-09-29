# Normalized-square support does not recover coordinate support

This exploration concerns a proposed removal of the first packed
mask, first investigated at the 94-operation frontier and continued
after the independent 93-operation factoring improvement. It is not
a lower-operation construction or a counterexample to either proved
system.
It gives exact obstructions to a proposed replacement support lemma.

Let S={0,1,5,25,...}, truncated at any sufficiently large fixed
power of five. With raw polynomial coefficients, the intended
support argument is sound: a positive constant term in C(T),
nonnegative coefficients, and supp(C(T)^2) contained in S+S imply
that every j in supp(C(T)) has j and 2j in S+S. Base-five digits
then give j in S. The problem is that a bit mask tests the
normalized digits of C(B)^2, not its raw polynomial coefficients.

Both counterexamples below satisfy the stronger condition that
every normalized square digit outside S+S is exactly zero. Thus
permitting digits 0,1,2,3 at those positions cannot repair the
obstruction.

## 1. No fixed unit anchor

Let B=2^h>=16 and a=2^ceil(h/2). Then 2a<B and
a^2/B belongs to {1,2}. For

    C=1+a*B^2,

we have the exact base-B expansion

    C^2=1+2a*B^2+(a^2/B)*B^5.

Its normalized support is {0,2,5}, contained in S+S, although
C has the forbidden support position 2. This works for both
square and nonsquare powers of two B.

## 2. An exact unit anchor at position one still does not suffice

Suppose a replacement source relation forces

    C=x+B+B^2*v, x<B, v>=0,

so the actual input is the unit digit and the next digit is
exactly one. There is still an arbitrarily large family of
counterexamples with actual input x=1.

Choose s=2^k>=8 and B=s^2. Put

    a=B/2-s+1, y=s-1,
    C=1+B+a*B^2+y*B^3,
    v=a+y*B>0.                              (1)

Both a and y lie strictly between zero and B. Therefore (1)
has exactly the required input and unit anchor, but has forbidden
coordinate positions 2 and 3.

Its square has the exact normalized expansion

    C^2 = 1 + 2B + (B-2s+3)*B^2
              + (B/4+3s)*B^5 + (B-s-2)*B^6. (2)

Every displayed coefficient is in [1,B-1] for s>=8. The
normalized support is consequently {0,1,2,5,6}, contained in
S+S because 2=1+1 and 6=1+5. Positions 3 and 4, which would
detect the bad physical coordinates at the raw level, are
exactly zero after carrying.

Here is an explicit derivation of those carries. Before carrying,

    C^2=1+2B+(1+2a)B^2+(2a+2y)B^3
                    +(a^2+2y)B^4+2ay*B^5+y^2*B^6.

The coefficient at position two is

    1+2a=B-2s+3<B,

so it has no outgoing carry. At position three,

    2a+2y=B,

which leaves digit zero and carry one. Position four then has

    a^2+2y+1=B*(B/4-s+2),

again leaving digit zero. The coefficient at position five,
including that carry, equals

    2ay+B/4-s+2
        =(s-3)B+(B/4+3s).

Thus its digit is B/4+3s, and the final digit is

    y^2+s-3=B-s-2.

This proves (2) for the entire family, without a finite-search
assumption. For example, B=64 gives a=25, y=7 and

    C=1+64+25*64^2+7*64^3,
    C^2=1+2*64+51*64^2+40*64^5+54*64^6.

## 3. Replacing the square by C(C-B) also fails

The raw coefficient contributed by the known unit anchor to a
cross product at position j+1 is halved if one tests C(C-B)
instead of C^2. This does not remove the support obstruction.

Keep s, B, a, and y from (1), but now put

    x=B/2+1,
    C=x+B+a*B^2+y*B^3.

There is again an exact normalized expansion supported in S+S:

    C(C-B)=1+(3B/4+2)*B+(B-2s+2)*B^2
                 +(B/4+3s)*B^5+(B-s-2)*B^6. (3)

All displayed coefficients belong to [1,B-1] for s>=8. To
derive (3), let A be the x=1 integer in (1). Then C=A+B/2,
so C(C-B)=A^2-B^2/4. In the expansion (2), subtracting B^2/4
borrows only between the already allowed positions one and two:
the new digits there are 3B/4+2 and B-2s+2. Every other digit
is unchanged. This proves the identity for arbitrarily large
power-of-two radices, while the forbidden coordinates at two
and three remain nonzero and the exact anchor C_1=1 is retained.

## 4. Why the fixed-index size and source gaps do not remove it

Square powers of two B in this family are arbitrarily large.
They can exceed every fixed lower bound on the radix, including
the enormous admissibility bound on H0. For the shifted affine
source, choose B>H+5 and put b=B-H-4 and beta=b-1. Then
b=x+beta with x=1 and beta>0, so the usual input gap is satisfied.
The extra anchored variable v in (1) is positive as well. For
the modified-product family (3), choose B>2H+10; then its input
x=B/2+1 still satisfies x<b=B-H-4, with positive beta=b-x.

Equation (2) gives C^2<B^7. Thus C^2<q=B^L holds whenever L>=8.
For the proposed layout placing all D_code shifts above L/2,
take L>14. Its uncontaminated low square region contains this
entire example, and every zero support test outside S+S in that
region passes. Increasing the fixed index or the separation of
the high code targets does not address these low carries.

The exact identity identifies a failure of the proposed decoding
lemma. It does not by itself provide a positive solution of all
equations for a particular represented system: the high circuit
targets have not been analyzed here. A replacement proof would
need another mechanism that rules out this family before it
invokes raw coordinate support.

One possible direction at this stage was a longer fixed low prefix,
such as an extra forced zero after the unit anchor; another was a
second independent product mask. Neither had been proved or costed to
give a saving below 94. Sections 6 and 9 now also rule out the stated
long-prefix support formulation. The direct support mask, the one-unit
anchor, and the single replacement product C(C-B) are therefore
rejected as sufficient support mechanisms.

## 5. The existing mask is weaker than an exact zero test

The actual third mask uses B-4, so a tested digit may be any of
0,1,2,3. With D's constant coefficient one, even a carry-free
square C=1+B^N+B^j can pass every support test: all its raw
coefficients are at most three when its three monomial weights
are distinct. A support repair must address this before using
any exact-zero support lemma.

One admissible change is D_const=2, making e_0's constant digit
three. The input cross coefficient becomes 4xC_j, which detects
a positive forbidden coordinate when no carry is present. This
does not suffice in general after normalization.

## 6. Arbitrarily large odd strides fail under the actual mask

Let N>=1 be odd, S_N={0,N,5N,25N,...}, and

    j=(5N-1)/2>N,
    C=1+B^N+(B/4)*B^j,

where B>=16 is a power of two. This respects the complete
anchored-prefix source relation

    C=x+B^N+B^(N+1)*v

with x=1 and positive integer v=(B/4)*B^(j-N-1). In particular,
every position between the input and the unit anchor is zero.
Nevertheless its forbidden coordinate j survives all ordinary
B-4 support tests applied to the doubled square:

    2C^2=2+4B^N+2B^(2N)+B^(j+1)
                    +B^(N+j+1)+(B/8)*B^(5N). (4)

The large coefficients occur only in S_N+S_N. Every digit
outside that support equals zero or one. All displayed positions
are distinct, and their coefficients are below B. Thus even an
arbitrarily large odd common stride and a complete fixed prefix
do not justify the proposed support recovery with D_const=2.

This obstruction initially left an even-stride formulation open.
Section 9 gives an arbitrarily large family for that case as well.

## 7. Modified-product large strides with an internal anchor

There is another exact obstruction if one fixes C_0=x and C_N=1
but does not force all positions between them to zero. It applies
to any N>=3, including even N, for the modified product
2C(C-B^N). Put

    alpha=(sqrt(6)-2)/2,
    x=ceil(alpha*B), C=x+B+B^N.

There are arbitrarily large powers of two B for which the
fractional part of alpha*B is at least 1/4. Indeed, if the
fractional parts were eventually always below 1/4, successive
doubling, starting from a nonzero fractional part, would
eventually leave that interval. Irrationality excludes zero.

For such B>=16, let epsilon=x-alpha*B, so 0<epsilon<=3/4.
The identity 4alpha+2alpha^2=1 gives

    4x+floor(2x^2/B)
       =B+floor(2sqrt(6)*epsilon+2epsilon^2/B)
       =B+r, 0<=r<=3.

Also 2x<B. The exact normalized digits of 2C(C-B^N) are then

    position 0: 2x^2 mod B,
    position 1: r,
    position 2: 3,
    position N: 2x,
    position N+1: 2.

All off-(S_N+S_N) digits are at most three, although the forbidden
coordinate C_1=1 is nonzero. This family does not respect the
stronger complete-zero-prefix relation of Section 6, and is
recorded only against the weaker internal-anchor formulation.

## 8. A bounded even-stride search and its limits

For an even stride N>=4 with the full anchored prefix, a bounded
search examined the subfamily

    C=x+B^N+aB^(2N)+bB^(3N), 0<x<B, 0<=a,b<B.

Here the seven raw coefficients of 2C^2, in powers of B^N, are

    2x^2, 4x, 2+4xa, 4a+4xb, 2a^2+4b, 4ab, 2b^2.

Since N>=4 and every coefficient is below B^4, there is no
carry between these blocks. At blocks zero, one, two, five,
and six only the first digit is exempt from the at-most-three
test. At blocks three and four every digit is tested. This
reduces the search to short integer coefficient conditions.

There are toy counterexamples, including B=256 with
(x,a,b)=(13,10,14), and B=1024 with (35,22,14). For the latter,
the seven coefficients are

    2450, 140, 3082, 2048, 1024, 1232, 392.

Each required digit is at most three. These examples apply to
arbitrarily large N, but only to their stated small radices;
they do not defeat an admissibility condition forcing B above
an enormous fixed H0.

The bounded search found no example in this subfamily for
power-of-two radices 2048 through 2^24. The script is
`../../tmp/search_even_stride_square_fast.py`; this is temporary
exploration evidence, not a general verification receipt. It
does not search arbitrary additional coordinate positions.
Neither the absence of examples nor the toy examples settled
the even-stride problem with a sufficiently large radix. The
next section resolves it with an additional coordinate position.
No valid support replacement or count below the independently
proved 93 follows from this lane.

## 9. A full-prefix counterexample for every even stride

The strong-prefix support formulation also fails for every
even N>=4 and arbitrarily large admissible radices. In fact,
the following family works for every integer N>=4, irrespective
of parity.

Let s=2^k>=8, B=s^2, R=B^N, and put

    x=s/2,
    C=s/2+R+s*R^4.                              (5)

These are canonical base-B digits: x, 1, and s are all positive
and smaller than B. The only occupied positions are 0, N, and
4N. In particular,

    C=x+B^N+B^(N+1)*v,
    v=s*B^(3N-1)>0,                            (6)

so (5) has exactly the proposed strong prefix. All digits between
the input and the anchor are zero, the anchor digit is one, and
even the next 3N-1 digits after the anchor are zero. Nevertheless,
4N does not belong to S_N={0,N,5N,25N,...}.

Squaring gives the exact raw expansion in powers of R:

    2C^2=B/2+2s*R+2R^2+2B*R^4+4s*R^5+2B*R^8.

Since 4s<B for s>=8, its exact normalized base-B expansion is

    2C^2=B/2+2s*B^N+2B^(2N)+2B^(4N+1)
                          +4s*B^(5N)+2B^(8N+1). (7)

All displayed positions are distinct, and all displayed digits
belong to [1,B-1]. The positions 0, N, 2N, and 5N belong to
S_N+S_N. The remaining occupied positions, 4N+1 and 8N+1,
do not: every member of S_N+S_N is divisible by N. Both of
their digits equal two. Thus every actual B-4 mask test outside
S_N+S_N passes, even though C has the forbidden coordinate 4N.

The mechanism is exact and does not depend on a search bound.
The input cross term and the bad coordinate's square each have
coefficient 2B, so they carry to the immediately following
forbidden position as the admissible digit two. The unit-anchor
cross term lands at the allowed position 5N. The longer stride
separates these carries without eliminating them.

The same family also defeats the modified product with this
strong prefix. Subtracting 2B^N*C from (7) gives

    2C(C-B^N)=B/2+s*B^N+2B^(4N+1)
                            +2s*B^(5N)+2B^(8N+1). (8)

Every displayed digit is again canonical. The only two
off-support digits are still two, and C-B^N>0. Thus the
replacement C(C-B^N) does not repair the implication either,
even with the complete zero prefix that Section 7 did not have.

For example, take N=4, s=8, and B=64. Then

    C=4+64^4+8*64^16,
    2C^2=32+16*64^4+2*64^8+2*64^17
                              +32*64^20+2*64^33.

Only positions 17 and 33 are outside S_N+S_N among these
occupied positions, and both have digit two.

For any fixed shifted-affine index H, square powers of two B
in this family are arbitrarily large. Consequently one may
require both B>H+4+s/2 and any fixed admissibility bound on H0.
Then b=B-H-4 and beta=b-x are positive and satisfy b=x+beta.
The global bound does not help: (7) implies C^2<B^(8N+2), so
C^2<q=B^L holds for every fixed L>=8N+2. If all D_code shifts
are above L/2, choosing L>16N+2 puts the entire example below
the high code contributions. Every low support test in that
uncontaminated region still passes.

As in Section 4, this is a counterexample to the proposed
support-decoding implication. It does not assert a positive
solution of all equations for any particular represented system;
the additional high circuit targets are not asserted to pass.
Any replacement compiler must supply another argument excluding
(5) before it may recover raw coordinate support. The exact
strong prefix, an arbitrarily large even stride, D_const=2, and
the existing at-most-three digit mask do not supply that argument.

As a separate finite arithmetic check, the expansion, canonical
digits, prefix, and all off-support digit tests for both (7) and
(8) were verified for
N in {4,6,8,10,12} and s in {2^3,2^4,2^5,2^8,2^16,2^32}:
30 cases with radices through 2^64. This check corroborates (7);
the displayed identities establish the infinite family.
