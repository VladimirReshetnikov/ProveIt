# Simultaneous raw-register histories with a shared six-field mask

A fixed number of raw numerical counters can share the six fields of the
77-operation zero-target component. The complete frame-guarded variants
cost **80 operations for two registers (40 products, 40 additions)** and
**81 operations for three registers (41 products, 40 additions)**. Each
has 33 positive unknowns and 23 equations. The single positive parameter
x initializes the registers at [2x,0,...,0]; all final values are zero.
Every counter changes by either +1 or -1 at each time step and remains
nonnegative. The first register's first step is +1.

The three-register case is a potential arithmetic interface for a later
machine controller; no controller or zero-branch test is included here.
In particular no strong raw-input universality claim is made for either
register count. The exact schedules, source polynomials, and finite receipts
are in `../verification/explore_simultaneous_raw_ternary_counters.py/.json`.
The single-register predecessor remains unchanged in
`EXPLORATION_RAW_TERNARY_ZERO_TARGET.md`.

## 1. Additional geometry, with no per-register track duplication

Fix the register count k, equal to two or three in the checked schedules.
Use the seventeen kernel unknowns and fourteen outer unknowns of the
77 component, adding positive R and Htime. Here R is one counter-block
radix and W is the radix of an entire time frame containing k blocks.
Retain every predecessor equation except the two replacements

    H(R-1)=2J,                                    (1)
    2x+alphaI=R.                                 (2)

Add

    W=R^k, Htime(W-1)=2J.                        (3)

The other geometry remains q=2J+1 and q=Wv. The six fields, their order,
and their bounds remain

    FKplus,G0,F0,G1,F1,FKminus,
    FKplus+FKminus=2J+H, 3T=2J+H,
    F0+F1+alpha=q+J, G0=F0+T, G1=F1+T.

Write A=F0+F1-2J and delta=FKplus-FKminus. The mixed history equation
is unchanged as an integer equation:

    2x+(W-1)A+W delta=0.                         (4)

The packed word P is the predecessor's same six-field Horner word, with
r=P and D0=q^6. The fixed plus-sign 43-operation kernel is unchanged.
The lookup of a value at variable exponent k is not free: W=R^2 uses
one product; W=R^3 uses R^2 followed by multiplication by R.

The two geometric masks have distinct meanings. H marks every counter
block; Htime marks complete time frames. The present frame-guarded source
retains both equations in (3) and makes no inference that a field width is
automatically a complete time frame.

## 2. Pre-power bounds and complete-frame recovery

Equation (2) gives R>=3 directly, because x and alphaI are positive.
Equation (1) therefore gives 0<H<=J. All predecessor field bounds follow:

    0<F0,F1,FKplus,FKminus<3J,
    0<T<=J, 0<G0,G1<4J.

They give exactly the same strict packing bound

    q^5<P<3(q^6-1)/2.

Consequently the general-scale kernel recovers q as a power of three and
the direct unit-two mask makes P native. None of these steps uses a prior
counter-block or time-frame interpretation. In particular signed A before
decoding is still allowed.

From W=R^k and q=Wv, R divides a power of three, so R=3^m with m>=1.
Write q=3^ell. The time-frame equation Htime(W-1)=q-1 gives
3^(km)-1 dividing 3^ell-1. Division with remainder on ell proves km
divides ell. Thus

    q=W^t=R^(kt), t>=1,
    H=(q-1)/(R-1)=1+R+...+R^(kt-1),
    Htime=1+W+...+W^(t-1).                       (5)

The first-control and adjacent guard/base decoding arguments from the
77 proof apply verbatim. They use only the displayed field bounds and the
strict packing window, not W as the counter-block radix. All six fields
are native and below q. The raw Boolean control words sum to H, so exactly
one sign is attached to each counter block. Also

    3T=2J+H=RH, T=(R/3)H.

Both raw numerical tracks have a zero highest ternary digit in every
counter block, by the same least-overlap native guard proof. Each block
value a_b is an ordinary nonnegative integer less than R/3.

## 3. Independent counter updates from one signed polynomial

Expand A and delta in base R over b=0,...,kt-1:

    A=sum a_b R^b, delta=sum epsilon_b R^b,
    0<=a_b<R/3, epsilon_b in {-1,+1}.

Multiplication by W=R^k shifts exactly k counter blocks. In (4), the
coefficients of the first k positions are

    2x-a_0, -a_1, ..., -a_(k-1).

The paid bound 0<2x<R makes each coefficient's absolute value less than
R. Successively reducing modulo R proves the initial vector is precisely
[2x,0,...,0]. The interior coefficients are

    a_(b-k)+epsilon_(b-k)-a_b, k<=b<kt.

Their absolute values are at most R/3<R. The same induction makes each
zero. Thus each counter updates from the preceding time frame according
to its own sign, with no carry or borrow into a different counter. The
last k coefficients are a_(b-k)+epsilon_(b-k) for kt<=b<kt+k, and are
exactly zero. Hence every final register value is zero. Nonnegativity of
all source blocks and the final values excludes decrementing zero.

The first native flag has unit digit two, so epsilon_0=+1. All other
initial registers have value zero and must also increment at their first
step; their first signs are therefore +1 as a consequence of the ordinary
counter semantics, not an extra mask promise.

This derives the full register history directly from signed integer
coefficients with magnitude smaller than R. It does not treat a sum of
small packed coefficients as a bitwise operation, or assume that separate
counter tracks were provided for free.

## 4. Positive converse and the fixed-sign kernel

Take a finite simultaneous history of k nonnegative counters, initial
[2x,0,...,0], final all zero, every sign +/-1, and first sign of the first
counter plus. Choose R=3^m large enough that all counter values appearing
before updates are below R/3. Set W=R^k, q=W^t and all geometric masks
as in (5). Split each ordinary ternary block value into two Boolean tracks
with a zero top digit, concatenate across all counters and frames, and add
J to obtain positive native fields. The two sign words are complementary
counter-block head sets. No field becomes zero even if a whole raw track
or a raw control is zero.

The raw aggregate A is bounded by (R/3-1)H<=J, so alpha>=1. The choice
of R gives alphaI=R-2x>=1. The top masks and all new geometry witnesses
are positive. Every outer equality holds with the same six-field word.

Each register starts at an even value and finishes at zero after t +/-1
steps. Hence t is even. The head mask H has kt terms of odd powers, so
H is even. As in the predecessor,

    P=FKplus+FKminus+G0+F0+G1+F1
      =2J+H+2(F0+F1)+2T=H modulo 2,

and r=P is even. The fixed plus-sign kernel's positive converse therefore
constructs all sixteen remaining auxiliaries for the already fixed r,D0.
Its soundness did not require even r before the decoding, so this is not
a circular parity argument.

## 5. Count and finite evidence

Relative to 77, computing R-1 adds one subtraction. Reusing the already
computed W-1, the time-frame product Htime(W-1) adds one product. W=R^k
costs its explicit addition-chain number of products. The replaced
counter-head product and input-bound comparison have unchanged costs.
For k=2 and k=3 the totals are therefore

    k=2: 77+1+1+1=80=40M+40A,
    k=3: 77+1+1+2=81=41M+40A.

More generally the same construction costs 77+ell(k)+2 when a specified
multiplication chain of length ell(k) computes R^k. This is a formula for
the supplied chain, not a claim about an optimal addition chain.

Both exact receipts verify all source residuals against the full primitive
list. The extra equations are W-R^k and Htime(W-1)-2J; all retained
kernel corrections are unchanged. The two-register regression checks 22
complete short joint control histories, one alternative track split, and
30 longer cleanup/excursion families. The three-register regression checks
104 joint histories, eight alternative splits, and 60 longer families.
Both also check 1,640 exact signed local transition cases in small block
radices. Full large Pell coordinates are supplied by the positive-converse
theorem, not materialized by these finite tests.

## 6. What a machine composition still has to enforce

At a purely arithmetic level, two microsteps can realize logical register
updates on even physical values 2n. An increment uses signs +,+, a valid
decrement uses -,-, and a hold uses +,-. All counters can therefore move
at every microstep even when only one logical counter changes. A global
+,- prefix preserves the raw initial vector and meets the first-plus
convention. These are elementary compilation facts about supplied sign
sequences, not counted controller constraints.

A machine verifier must still restrict every two-step sign pattern to the
proper instruction, enforce each zero-test branch, advance the finite
program state, preserve the shared variable frame, and recognize halting.
The present component proves none of those relations for free. In
particular three available numerical registers do not by themselves prove
that a universal machine has been encoded, and no strong raw-input
universality claim for two counters is made.
