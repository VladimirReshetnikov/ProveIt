# Moving-frame Boolean histories at the same 86-operation count

This note changes one operand in the finite-history component system of
`round39_1980_boolean_history_components.py`. The exact new certificate is
`../verification/round40_1980_moving_frame_components.py`. It still has
86 instructions, 31 positive unknowns, and 21 equations. This is a theorem
about finite Rule 110 histories, not a new universal Diophantine certificate.
Cook's prescribed periodic-tail simulation is not replaced by an unproved
finite-input universality assertion.

## 1. The single arithmetic change

Retain every register, unknown, and equality from round39, except replace

    time_rhs = B + Q*F

by

    time_rhs = C + Q*F.

The product Q*F already exists as a register; the changed instruction is
therefore still one addition. The temporal source equation becomes

    I + W*Y = C + Q*F.                              (1)

In particular, do not add a multiplication by four to the temporal left
side: the previously supplied equality B=4C already provides that shift.
The source residual changes only from `I+v^2*Y-B-q^2*F` to
`I+v^2*Y-C-q^2*F`. The retained triangular Pell correction is unchanged.
The independent symbolic checker verifies all 21 source equations and
86 primitives: 46 multiplications and 40 additions/subtractions.

As before, I and F are row parameters. They denote quarter-rows in the
moving frame; the physical initial and final words are 4I and 4F.

## 2. Bounds, powers, bitness, and geometry are retained

Use Q=q^2, W=v^2, H=hrow, A=4B, and the same positive arithmetic
equations

    q=v*quot, Q-1=H*(W-1), B=4C,
    B+C=X+2D, A+D=Z+2E, Y+E=X+D,
    A+B+C+alpha=Q, I+alphaI=W.

Before interpreting any digits, these give Q>=22, W>=4,
0<H<Q/3, and all six fields B,D,X,E,Z,B+H strictly below Q.
They additionally give a useful stronger bound:

    4Y <= 4(X+D) <= 4(B+C) = 5B < (21/4)B < Q.     (2)

The first inequalities can be made strict with positive D,E; the
displayed weak inequalities are sufficient. The changed temporal equation
still implies F<W, because I<W, Y<Q, C>0 give QF<I+WY<WQ.

Thus the same six-plane Horner word P lies between zero and Q^6. With
L=Q^8, n0=Q^6 as proof notation, n0^2=Q^12 as the only computed scale,
and 3*lambda=L-1, the same polynomial packing gives

    r=(L-P)*(L-1)+2*(L-1)/3,
    n0^2<r<Q^16<n0^3.

These pre-power bounds justify the retained 43-operation first-Pell
kernel exactly as in `EXPLORATION_PERIODIC_DIGIT_MASK.md`. The kernel
proves q a power of two and n0^2 divides binom(2r,r). The exact periodic
mask then proves each packed field Boolean. Because v divides q, the
geometric equation yields W=4^m, Q=W^t and

    H=1+W+...+W^(t-1), m,t>=1.

The simultaneous Boolean tests of B and B+H force each row of B to start
with zero. Thus C=B/4 is an ordinary digit shift with no row-crossing
contamination: its j-th row is precisely b_j/4, where b_j is B's j-th
row, and each row of C is strictly below W/4.

## 3. Exact moving-frame temporal and spatial meaning

The same local Boolean equations prove that the digits of Y are Rule
110 outputs; write y_j for its j-th row. Since all operands in (1)
have the previously proved base-W ranges, unique row decomposition gives

    I=b_0/4,
    y_j=b_(j+1)/4 for 0<=j<t-1,
    F=y_(t-1).                                      (3)

In particular y_j<W/4 for every j<t-1. Bound (2) also gives
y_(t-1)<W/4. Hence every successor row has last digit zero.

At a row's last cell the right-neighbor plane C has digit zero, since
the next B row starts with zero, or the complete word ends. Rule 110
has f(a,b,0)=b. Therefore the just-proved zero last digit of every y_j
forces every b_j's last digit to be zero as well. The left-neighbor
plane A=4B consequently has no nonzero wrap from an earlier row. Even
without this deduction, a first-cell wrap would be harmless because
its center bit is zero and f(a,0,c)=c. Thus each y_j is exactly the
zero-exterior Rule 110 update R(b_j), without a cyclic boundary.

Equations (3) now say

    b_0=4I,
    b_(j+1)=4*R(b_j) for 0<=j<t,
    b_t=4F.                                         (4)

The extra final row in (4) is defined by 4F, rather than packed in B.
It fits below W because F<W/4. Multiplication by four shifts a row
one cell to the right, so (4) is exactly Rule 110 viewed in a frame
that moves one cell left at each time step. The first cell stays zero,
and the checked evolution agrees with the infinite-line zero-exterior
evolution on every represented cell.

Conversely, any finite sequence satisfying (4), with first and last
cells zero in each pretransition row and last cell zero in each raw
successor R(b_j), satisfies the exact row identity (1). The other
alignment and local equations follow by their definitions.

## 4. Unbounded duration for one fixed initial word

For any nonzero finite configuration, its leftmost one moves left by
one under ordinary Rule 110, while its rightmost one remains fixed.
The former follows from f(0,0,1)=1 and the absence of a farther-left
nonzero neighbor; the latter follows from f(a,1,0)=1. After the extra
right shift in (4), the leftmost position therefore stays fixed, and
the rightmost position increases by one at each step.

Let I be any positive Boolean word, and let k be the largest base-four
digit position occurring in 4I. Starting with 4I, the infinite moving
frame sequence has its leftmost one at a position at least one and
its rightmost one at k+j after j steps. For any desired t>=1, choose

    m >= k+t+2.

Then every required row and its raw successor fits within m cells,
with enough zero space at the right. Its first cell is zero. Hence
increasing the width supports arbitrarily long moving-frame histories
of this same I. The old bound t<=v4(I) does not apply to this relation.

This observation does not make exact endpoint reachability universal.
If I,F are both fixed nonzero row words and (4) holds, their rightmost
positions force

    t = floor(log_4 F) - floor(log_4 I).

The apparent logarithms here denote digit positions in a proof of
decidability, not uncharged certificate operations. A prescribed exact
endpoint can therefore be checked by simulating that single possible
number of steps. An existential endpoint with a finite pattern
condition would be a different relation and needs its own paid
arithmetic interface and a valid universality theorem.

## 5. Positive witnesses and the unchanged Pell necessity

Construct B from the pretransition rows of (4), and construct all local
planes from their Boolean definitions. The highest digit of B is zero,
so B<Q/12 and A+B+C=(21/4)B<7Q/16<Q. Thus alpha is positive, and
I<W gives a positive alphaI. The choices v=2^m, q=2^(mt),
quot=2^(m(t-1)) and H=(Q-1)/(W-1) are positive integers satisfying
the geometry. B,C,Y and F are positive because the rightmost one
persists before the moving shift. X is positive at a rightmost one,
where b=1,c=0; Z is positive immediately to its right, where
a=1,b=c=0. Those cells fit by the stated width choice.

D and E are positive as soon as one pretransition row contains 111.
For t>=3 this is automatic for every nonzero finite initial row.
Indeed, inspect its rightmost consecutive run of ones. If its length
is at least three, the claim holds already. A run of length one grows
to at least two in the next ordinary update, since its preceding zero
has neighborhood (a,0,1) and output one. A rightmost run of length
two grows to at least three: the preceding zero and both existing
ones output one. Thus 111 appears within two steps. Translating by
one cell each step preserves this assertion. For t=1 or t=2, the
same construction gives positive supplied local planes whenever an
actual pretransition row contains 111; no artificial motif is inserted.

Every packed field is Boolean, so the special mask gives n0^2 dividing
the central binomial coefficient. B's unit digit vanishes, making P
even and r even. Choose U=2^(2r+1),
Ypell=floor((U+1)^(2r)/U^r), w=U/n0^2, s=Ypell/n0^2,
and the remaining positive first-Pell witnesses exactly as in
`BASE_TWO_PELL_90_PROOF.md`, Section 6. Its integral positive interval
gaps, norm and index quotients, and first exponential quotient use
only the scale, parity, and divisibility just established. The generic
construction in `HALF_PARAMETER_PELL_92_PROOF.md` supplies positive
i,f,j,o,y_aux because 2r+1 is 1 modulo four. All 31 positive unknowns
and all 21 equations therefore have witnesses for every such history.
No second index or second exponential occurs in this component system.

## 6. Exact finite regression and scope

`explore_moving_frame_boolean_history.py` checks 5,050 proposed Boolean
histories at widths 2--5 and heights 1--3. Of these, 2,513 satisfy the
shared numerical bound, 16 satisfy moving alignment, and three have
all local supplied planes positive. It checks the equivalence between
the integer row equation and direct cellwise moving evolution, including
the last-column zero deduction.

Seven further positive canonical histories share the same I=277 and
have heights 1,2,3,4,8,16,32. They verify every outer bound, all six
Boolean planes, parity, and the exact popcount threshold. Huge Pell
necessity witnesses are proved above rather than numerically instantiated.

This is a same-count improvement to the finite-history architecture.
The encoding of an arbitrary numerical input into a universal initial
configuration, faithful periodic tails or a suitable finite machine,
and a final event predicate remain unresolved. The published universal
certificate remains at 90 operations.
