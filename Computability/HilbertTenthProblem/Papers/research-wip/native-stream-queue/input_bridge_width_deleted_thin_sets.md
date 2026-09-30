# The width-deleted affine-carry family cannot be universal

For any fixed integer coefficients, if the literal width-deleted source
with its affine carry equality represents only positive powers of two,
then its represented input set is decidable. Consequently this particular
source family cannot represent every recursively enumerable set. This is
a nonuniversality theorem for a specified arithmetic architecture, not a
new universal bound and not a claim about a redesigned overflow machine.

The theorem combines the independently reviewed
[exact source classification](pell_kernel_width_deleted_classification.md)
and [width descent and fixed-width decision](input_bridge_width_descent.md).
The established complete universal bound remains76.

## 1. Exact family and operation count

Start with the [63-operation source](native_dualrail_fifo63.md). Delete
only the defining addition for `6x+beta=W`, that comparison and its
positive witness beta. Keep every other equation and positive coordinate.
The resulting literal62 source retains

    A=F0+F1-q+1, D=F2+F3-q+1,
    D=6x+WA, q=WL, A+D+alpha=q,
    r=F0+qF1+q^2F2+q^3F3.                             (1)

Here A,D are computed registers, not positive supplied witnesses. They
may have either sign until the source equations prove otherwise.

For any fixed integers `c0,c1,c2,c3,lambda,delta`, add exactly

    sum_i ci*Fi + lambda*(q-1) = delta.                 (2)

The register `q-1` is already paid. Four coefficient multiplications,
three summation additions, one multiplication by lambda and one final
addition cost9=5M+4A; comparison with fixed delta is free. The combined
source is71=38M+33A, with15 equations and25 strictly positive witnesses
besides the ordinary positive input x. It is a concrete failed universal
architecture. The checker executes the full combined instruction list
and checks the independent polynomial residual of(2); the underlying62
residual audit is imported unchanged.

Let S be its represented subset of positive integers. The theorem is:

> If S is contained in `{2^n:n>=0}`, then S is decidable, uniformly from
> the fixed coefficients in(2).

The algorithm does not test that containment promise. For arbitrary
coefficients it still terminates and every YES answer is sound; the
promise is what proves completeness of its finite search.

This family includes any fixed affine carry controller on the four
Boolean labels. On native fields write `Fi=H+Bi`, `H=(q-1)/2`, and put
`K=sum ci`. Equation(2) becomes

    -delta + (K+2lambda)*H + sum_i ci*Bi = 0.

Thus it is exactly the length-t carry relation

    3k_next = k + h + sum_i ci*label_i,
    h=K+2lambda, cs=-delta, cf=0.                      (3)

The labels are ordered append0, append1, read0, read1. For an original
controller with arbitrary integer data `ci,h,cs,cf`, clearing its possible
factor of two gives the member

    2 sum_i ci*Fi + (h-K-2cf)*(q-1) = 2(cf-cs).

No parity restriction on the fixed controller coefficients is needed.
On nonnative fields, (2) is retained as its literal polynomial equality;
no Boolean-label interpretation is silently imposed there.

## 2. All nonnative witnesses have a computable finite bound

The exact classification proves that every positive solution of the62
source has `q=3^t`, `t>=2`, and `W=3^m`, `0<=m<=t`. Its supplied fields
are already the literal normalized chunks of its even packing r, and
belong to exactly one of four digit strata.

The short stratum is native: all4t ternary digits are1 or2, with units2.
It has A>=1. The other three strata have4t+1 digits, top1 and exactly one
zero, at the last position of one of the first three q-fields, followed
by2. For the first two, A<0 and `q<=D<6x`. For the third, W=1 and
`q<18x`. In particular A never vanishes, and **every nonnative solution
has q<18x**, regardless of(2).

For a numerical input x, there are only finitely many powers q in that
range. For each, the retained joint bound is

    sum_i Fi <= 3q-3.

It gives a finite enumeration of all positive supplied field tuples.
Test even packing, the exact nonnative stratum, each power width W
between1 andq, transport(1) and controller(2). All these tests are
computable integer operations. The source classification includes a
strictly positive Pell converse throughout `r<3q^4`; hence passing these
finite tests is equivalent to existence of all remaining positive
witnesses. There is no unbounded Pell-coordinate search in this step.

## 3. Native widths at least27 violate the powers-of-two promise

Suppose a native positive solution has `W=3^m>=27`. Then A>=1. The
width-descent theorem preserves every retained source polynomial when
one replaces W by W/3 or W/9, sets `L'=q/W'`, and changes the input to

    x_j = x + (W-W/3^j)*A/6, j=0,1,2.                 (4)

All three widths remain positive powers divisible by3, so the changes
in input are integers. They are strictly positive and
`x_0<x_1<x_2`. Every other positive coordinate, every field and every
kernel coordinate stays unchanged. In particular (2) stays unchanged.
Thus all three inputs belong to S, and direct subtraction gives

    x_0 - 4x_1 + 3x_2 = 0.                            (5)

Three distinct increasing positive powers of two cannot satisfy(5).
Indeed write `x_j=2^nj`, with `n0<n1<n2`, and divide by `2^n0`. The
first term is odd and both remaining terms are even, a contradiction.
Therefore the promise `S subset {2^n}` forbids every native witness
with W>=27. All remaining native widths are exactly1,3,9.

For a concrete full positive family, take `W=3^m`, m>=3, q=3W, A=1 and
D=W+6, with ordinary input x=1. Split the ternary digits of D into two
Boolean read rails; use append rails1 and0, and add H to all four fields.
The packing is even, the units digit is2, and A+D<q. The positive kernel
converse applies. At m=3 the three accepted inputs from(4) are1,4,5,
with widths27,9,3, satisfying `1-4*4+3*5=0`. This illustrates the
preserved-source mechanism; the proof above covers every native witness
and every fixed controller that accepts its unchanged fields.

## 4. Explicit finite decision at widths1,3,9

For each fixed W, use the finite native graph proved in the width-descent
note. Start its numerical state at N=6x. A label has scalar append
`a=a0+a1` and read `d=d0+d1`, each in{0,1,2}. Permit precisely the
integer transitions

    N_next=(N+Wa-d)/3.

Nonnegativity and the remainder condition give
`0<=N<=max(6x,W)` along every path. This formula includes W=1, where
the read is `(N+a) mod3`; no ordinary FIFO interpretation is assumed
at that endpoint.

Couple N to the carry in(3). Its integral states lie in[-B,B], where

    B=max(abs(cs),ceil((abs(h)+sum abs(ci))/2)).

An additional carry e in{0,1}, initially0, advances by
`e_next=floor((e+a+d)/3)` and ends at0 precisely when A+D<3^t.
An age counter capped at `max(1,m)` enforces q divisible by W and
positive length. Require append rail0=1 on the first edge, as forced
by the native units digit of r. Accept exactly at N=0, k=cf, e=0,
and the capped age. Ordinary finite graph reachability decides whether
such a path exists, without any zero-padding or absorbing-endpoint
assumption.

Every native source witness supplies a path. Conversely every accepted
path yields `q=3^t`, positive fields `Fi=H+Bi`, `L=q/W`, and positive
`alpha=q-A-D`. The first-append condition forces the packed units digit2.
Transport with even6x and oddW gives A+D even; since q is odd, this also
makes r even. The native doubling carries give the required4t valuation.
The positive kernel converse then supplies every retained witness.
An accepted path of length1 would have q=3, A>=1 and D>=6, contrary
to A+D<3; thus the classification's t>=2 threshold is automatic.

The algorithm is now complete: first run the finite nonnative search in
Section2, then the three native graph searches for W=1,3,9, and answer
YES if any succeeds, NO otherwise. It always terminates. Under the
powers-of-two promise, Section3 proves that there are no omitted native
widths, so it decides S.

## 5. Consequence for universal representation

Take an undecidable recursively enumerable set K of nonnegative integers.
Its computable image `{2^n:n in K}` is recursively enumerable and
undecidable: deciding membership of2^n would decide membership ofn in K.
If the fixed-coefficient architecture(1),(2) represented that set, the
preceding theorem would decide it, a contradiction. Therefore the
literal width deletion followed only by this affine carry equality
cannot be a universal certificate family, at any claimed operation count.

The argument is confined to this exact polynomial family, ordinary input
6x, retained joint bound and kernel, and fixed coefficients. Additional
arithmetic conditions involving x or W can break width descent and are
outside the theorem. A redesigned compiler or different source also
requires its own analysis. This does not lower the established complete
bound76.

## 6. Evidence

The [checker](input_bridge_width_deleted_thin_sets.py) audits the literal
combined71 schedule, verifies the affine three-input relation symbolically,
and checks six full positive outer families whose enormous Pell tuples
exist by the proved converse. It implements the terminating decision
procedure, runs it on numerical fixed programs and inputs, and checks
every admitted nonnative field/width tuple through q=27 against the
finite bound and direct controller equality. A finite powers-of-two
comparison supplements, rather than replaces, the elementary parity
proof of(5). No arbitrary tested program is assumed to satisfy the
powers-of-two promise.

The two source lemmas have independent proof/source/default review PASS.
Independent full proof/source/default review of this combined theorem
PASS (pell_kernel), with no findings. Default execution checks the saved [receipt](input_bridge_width_deleted_thin_sets.json).
