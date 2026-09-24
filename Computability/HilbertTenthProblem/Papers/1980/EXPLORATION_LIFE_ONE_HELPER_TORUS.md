# An exact one-helper Life torus interface in 36 conditional operations

The new one-helper Life relation composes with the existing rectangular
torus convolution. Including the all-ones equation, the result costs
**36=21M+15A**, improving the old conditional37 interface while using one
Boolean local helper instead of five. The left Boolean seam already forces
the row stride to align with radix512; its separate alignment equation is
redundant. A separately supplied, already paid all-ones word reduces this
subtotal to35. The count36 includes that word's defining equation.

The construction recovers the actual inclusive neighbor sum from its
integer congruence and the new local field's range bound. It does not
assume that an independently supplied sum is correct. The source still
assumes the Boolean/mixed-mask predicates, their ranges, and a power-of-two
geometry premise. It supplies no complete universal certificate.

The checker and receipt are
`../verification/explore_life_one_helper_torus.py` and the adjacent JSON.
Dependencies are the exact geometry and seam derivation in
`EXPLORATION_LIFE_TORUS_CONVOLUTION.md` and the local truth table in
`EXPLORATION_LIFE_ONE_FIELD_MASK.md`. Those published sources are unchanged.

## 1. Rectangular geometry and both exact edges

Use radix b=512. For width m>=1 and height n>=1 write

    W=b^m,  q=W^n,  A=W/b,
    h=(q-1)/(W-1),  J=(q-1)/511.

Cells (i,j) occupy digit i+mj. All neighbor multiplicities are retained
when either dimension is1 or2. Assuming the surrounding kernel proves
q is a power of two, the following six primitives and four comparisons,
together with the Boolean left seam below, establish this geometry:

    wm1=W-1; qm1=q-1;
    hwm1=h*wm1;       hwm1=qm1;
    wquot=W*quot;     wquot=q;
    a512=512*A;       a512=W;
    allones=511*J;    allones=qm1.                              (1)

All geometry inputs are positive. First, 511J=q-1 makes q=512^N:
the order of2 modulo511 is9. Divisibility W|q gives W=2^a, with
a>=9 from512A=W. Since W-1 divides q-1, a divides9N. Write
n=9N/a, so h=sum_(j=0)^(n-1) 2^(aj). At this point a need not yet
be divisible by9. Cost:4M+2A. Paying for J is included.

Let C be the preimage word. With nonnegative L,R,Xl,Xr, impose

    C+h   = Xl+2L,
    C+A*h = Xr+2A*R.                                          (2)

Require C,Xl,L,Xr,A*R to be Boolean radix512 words below q. The left
equation supplies the missing alignment proof. Consecutive set bits of h
are at least9 positions apart, so each radix512 digit of h is zero or
one of1,2,4,...,256. On the other hand, h=Xl+2L-C has coefficients
in[-1,3]. Subtracting the two expansions gives coefficients in[-257,3],
all of absolute value less than512. Reducing modulo512 and inducting
forces equality coefficient by coefficient. Every digit of h is therefore
0,1 or2.

If a mod9 is in2..8, the bit at position a contradicts this conclusion;
n>=2 because a*n is divisible by9. If a mod9 is1, n is a multiple of9,
and the bit at position2a contradicts it. Thus9 divides a after all.
Write a=9m. This proves W=512^m and q=W^n without the old equation
511d=W-1, saving its multiplication and eliminating d.

With this alignment established, both sides of each seam equation have
digits in0..3, so these are carry-free half-adder equations. They force
L to be the first-column bits of C, and A*R to be its last-column bits.
Thus R is the last-column word shifted to first-column positions.
The eight-operation schedule includes A*h and A*R and costs4M+4A.
It remains valid at width1, where the two masks coincide.

## 2. Recover the inclusive sum rather than assuming it

Supply a nonnegative integer S, the Boolean output Y, and a Boolean
helper U. Form the shifted local field

    Vprime=28S+2C+16Y+118U+41J.                               (3)

The nine operations cost5M+4A. Require

    0<Vprime<q,       Vprime AND(144J)=0.                     (4)

The range and the mask in (4) are external predicates in the36 subtotal.
The positive wrapper in `EXPLORATION_LIFE_POSITIVE_BOOTSTRAP.md` addresses
an important part of this range problem, under its own explicit domain.

Set

    K=W^2+W+1,
    Hnum=262657C+(W-1)(L-512R),

where262657=512^2+512+1. Impose the single signed-quotient equation

    K*Hnum=512W*S+z(q-1),       z an integer.                 (5)

For the actual rowwise horizontal triple H, exact edges (2) give
Hnum=512H. The established torus identity gives

    K*H= W*Strue modulo(q-1),

where Strue is the actual inclusive3-by-3 sum. Whole-row rotation is
multiplication by W modulo q-1; the exact horizontal seams were already
handled in Hnum. This is a rectangular torus, not a helical row-major
rotation. Since512W is coprime to q-1, equation (5) yields

    S=Strue modulo(q-1).                                     (6)

All terms of (3) are nonnegative, and J>0. Hence (4) gives
28S<Vprime<q. Meanwhile0<=Strue<=9J=9(q-1)/511. Both S and Strue
are strictly below q-1, because q>=512. Their congruence therefore
forces equality as integers. In particular the digits of S are the
actual counts in0..9; they were not assumed to have that interpretation.

Now each digit of (3) is precisely2v+1 for the local scalar expression
v=14s+c+8y+59u+20. It lies in[41,429], so there is no carry. Condition
(4) is exactly the one-helper Life rule at every cell. Conversely, any
finite rectangular Life preimage supplies Strue, the unique local helper,
the edges in (2), and an integer z satisfying (5).

## 3. Exact count, field obligations, and integration boundary

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Geometry, repunit and seam-forced alignment (1) | 4 | 2 | 6 |
| Both edge checks (2) | 4 | 4 | 8 |
| Hnum, K and K*Hnum | 5 | 4 | 9 |
| 512S, W*(512S), z(q-1), final addition | 3 | 1 | 4 |
| Shifted local field (3) | 5 | 4 | 9 |
| Total | 21 | 15 | 36 |

The checker records every primitive and independently verifies all seven
comparison residuals and the local field polynomial. In particular the
extra multiplication512S is charged. The old homogeneous Life relation
absorbed that scalar into existing coefficients; reusing that old count
with a supplied S would be incorrect.

The Boolean assertions are C,Y,U,L,Xl,Xr,A*R: seven words, plus the mixed
field Vprime and its bound. If the target construction has already typed
Y, six Boolean words and one mixed field remain to be packed. Their mask
implementation is not included in36. For comparison, the old torus source
had eleven Boolean words and no separate mixed field. Thus the new source
changes the mask problem substantially while the local/geometry
arithmetic subtotal decreases by one.

The potentially zero supplied inputs are C,Y,U,S,L,R,Xl,Xr. A generic
strictly-positive representation value=positive_value-1 takes eight
subtractions; z=zplus-zminus takes one more. This gives an explicit
45-operation adapter for the same conditional predicates. It does not
prove that those predicates themselves have a positive certificate.

Against the new positive27 local wrapper, the nine operations for (3),
the repunit equation, and q-1 are already paid. The additional displayed
torus arithmetic is therefore

    geometry4 + exact edges8 + convolution13 = 25.            (7)

Appending these instructions to its conditional70 ledger gives95 paid
operations before extending the mask to the four new edge words. This
is a partial cost ledger, not a complete95-operation system. The changed
packing, scale, and raw-field bounds must be derived anew, and the zero
edge fields and signed z need positive-domain handling. Further sharing
could change the count. Equation (7) identifies the currently unpaid
work rather than claiming a new universal upper or lower bound.

The arbitrary-period target interface remains separate exactly as in the
old torus note: for a target of periods a,b, the witness width and height
must be compatible multiples, and the target must be repeated into the
witness rectangle. Fixed-width strips and a single helical cyclic shift
are not substitutes for this interface.

## 4. A seven-operation combined edge check and its real mask cost

There is a correct arithmetic saving when width m>=2. The column masks
h and A*h are then disjoint. Use Boolean C,X and sparse words L,R satisfying

    0<=L,R<q,
    L AND(q-1-h)=0,   R AND(q-1-h)=0.                         (8)

These conditions say exactly that L and R are Boolean words supported
on the first-column positions. Impose

    C+h+A*h=X+2(L+A*R).                                     (9)

Every digit is a carry-free half-adder, and the supports of L and A*R
are disjoint. Thus (9) uniquely recovers both actual edge columns.
Its schedule computes A*h, then+h, then+C; A*R, then+L, then times2,
then+X. It costs7=3M+4A and replaces four old edge fields by X,L,R.

The width restriction matters. For m=n=1, C=0,L=1,R=X=0 satisfies
(8)-(9), although the true two edges are zero. To use (9) in a source,
one can set A=a0+1 with positive a0, paying one addition; since A is a
power of512 after geometry, this forces m>=2. Completeness can repeat
any witness horizontally to width2m while preserving its periodic target.
That extra addition cancels the standalone arithmetic saving.

This replacement assumes the aligned geometry. It does not automatically
inherit Section1's deletion of511d=W-1, whose proof uses the separate left
seam. A complete source using (9) would need to pay for alignment or prove
it again for the changed equations. The count36 retains both exact seams.

The sparse masks are also not ordinary Boolean masks. Put N=mn.
The word h has n set bits, while q has9N bits, so

    popcount(q-1-h)=9N-n.

Two such fields introduce a term-2n into the binomial valuation threshold.
It is not a fixed integral power of q when both torus periods vary.
That term cannot be silently omitted from the kernel scale.

One exact, but not free, compensation is a zero padding field with mask
3h+4J. The digits of this mask are7 at first-column positions and4
elsewhere, giving popcount N+2n. For example the seven fields

    [Vprime,C,U,X,L,R,0]

may use respective masks

    [144J,510J,510J,510J,q-1-h,q-1-h,3h+4J].                  (10)

Their total mask popcount is45N. With total length q^7, the exponent is
63N+45N=108N, exactly the scale q^12. This repairs the bit-count identity,
but adds padding, larger powers and h-dependent mask construction.
No improved full count follows from the seven-operation edge relation
alone, and (10) is not presented as an optimized mask source.

Finally, packing L and R together as L+2R does not remove separate typing.
At radix16,width2,height3 let W=256,A=16. The true edges L0=0,R0=W^2
give D=L0+A*R0. The false nonnegative values

    L=75776, R=60800

satisfy L+A*R=D and L+2R=3W+3W^2, whose column digits are all in0..3.
Thus those two aggregate relations and a two-bit sparse mask do not
recover the individual Boolean edges.

## 5. Fresh finite evidence

The checker verifies the36-operation source symbolically and exercises
all682 Boolean tori with width and height in1..3, including all dimension1
and2 multiplicities. It checks5,506 physical cells, all source comparisons,
the local helper/mask, and682 deliberately corrupted outputs. The quotient
tests include negative, zero and positive z.

For the combined-edge lemma it exhausts38,192 column-pair candidates on
widths2,3 and heights1,2,3, accepting exactly668 genuine edge pairs. It
checks the variable-height mask popcounts and compensation, and reproduces
both failed shortcuts above. These finite checks support the general
conditional proofs; they do not provide the omitted global arithmetic
compiler or a universal count.

The separate alignment check covers504 power geometries, including288
misaligned strides rejected by the necessary left-seam digit condition.

Review status: author and an independent complete scoped proof/source
review pass. Fresh read-only verification exactly matches the saved JSON.
