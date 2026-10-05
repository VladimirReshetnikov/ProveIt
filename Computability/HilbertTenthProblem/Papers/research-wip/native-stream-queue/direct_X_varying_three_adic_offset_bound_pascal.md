# A finite bound for all offsets in the canonical three-adic index family

For each fixed radix B=2^d, even allowing the offset e-3k to vary does
not give an unbounded family of literal packed indices of the form

    q=B*3^k,       R=2*3^e-3.

The repunit divisor and retained numerical index window imply the explicit
bound `3^k<=3B^3(B-1)`. They also bound e, leaving a finite computable set
of candidate pairs for each fixed B. Root proposed the argument below;
I independently checked its integer, sign and endpoint steps.

When the authentic no-wrap input theorem is additionally invoked,
any complete positive zero in this precise class must have ordinary
input x equal to1 or2. This rules out an unbounded-input route through
the family, not every possible false positive at those two inputs.

This is a necessary-condition theorem for this precise family. It does
not assert that the finite candidate set is empty, decide all canonical
nondyadic scales, or prove soundness of the direct-X83 proposal. No
arithmetic source or universal operation count is changed.

## 1. Exact hypotheses and conclusion

Let d,k,e be positive integers and put

    B=2^d,  m=B-1,  t=3^k,  q=B*t,  R=2*3^e-3.

Assume

    J=(q-1)/m is a positive integer,
    J divides R,
    (2q-1)*(q^2-1) < R < q^3*(q-1).                (1)

Then

    3^k <= 3B^3(B-1).                              (2)

The conditions in (1) are necessary on an authentic positive direct-X83
zero with the specified q and R. The literal packed index is

    R=(q*U-Z)*(q^2-1)+(MC+q*MF_source)*J,
    q=(B-1)*J+1,

so J divides R regardless of signs of U,Z or masks. The displayed
numerical window is already established by the full positive-zero
bootstrap, before ordinary-input decoding. No mask interpretation,
canonical half-binomial divisibility, or auxiliary completion is assumed
in the proof of (2).

The theorem permits all d>=1. If d is even then3 divides m, whereas
q-1 is not divisible by3, so its repunit premise cannot hold. No unit
order is presumed for such a d. On any tuple satisfying (1), the exact
equality mJ=q-1 directly implies that both m and J are units modulo3.

## 2. Clearing the varying offset at each candidate

Here q>=6. The lower numerical window is stronger than R>q^3, because

    (2q-1)*(q^2-1)-q^3=q^3-q^2-2q+1>0

for q>=3. Set the integer c=e-3k. Since

    2*3^c=(R+3)/t^3 > B^3,

and B^3>=8, c must be positive. Thus negative or zero offsets have
already been excluded by the lower window, rather than silently omitted
from the argument.

Define

    Gamma=2*3^c/B^3=(R+3)/q^3,
    N=2*3^c-3B^3.

Multiplying the identity R=Gamma*q^3-3 by B^3 gives

    B^3*R=2*3^c*q^3-3B^3.

Since J divides R and q=1 modulo J, this implies J divides N. This
step does not divide modulo J by B^3. Also N is nonzero: equality
would give `3^(c-1)=2^(3d-1)`, impossible because the binary exponent
is at least2. Therefore

    a=N/J

is a nonzero integer. As c>=1, N is divisible by3, and J is a unit
modulo3. Consequently

    3 divides a.                                      (3)

## 3. Contradiction above the bound

Suppose, for contradiction, that

    t>3B^3m.                                         (4)

Since t>1,

    J-t=(t-1)/m>0,

so J>t>3B^3. On the other hand N>-3B^3. It follows that a=N/J>-1.
As a is a nonzero integer, a>=1. Together with (3), it is in fact
at least3. This sign deduction is essential; J dividing N alone would
not permit treating a as positive.

The upper numerical window gives

    Gamma=(R+3)/q^3 < q-1+3/q^3 < q.

Hence

    N=B^3*(Gamma-3)<B^3*(q-3)<B^3*(q-1),
    0<a<B^3*(q-1)/J=B^3m.                            (5)

There are now two exhaustive cases.

If c<k, then `N<2*3^c<2t<2J`, so a<2. This contradicts the positive
multiple-of3 conclusion (3).

If c>=k, multiply aJ=N by m and use mJ=Bt-1:

    a*(Bt-1)=2m*3^c-3B^3m.

Reduction modulo t=3^k is legal because t divides3^c. It gives

    a = 3B^3m modulo t.                             (6)

But (4)--(5) place these two representatives strictly inside [0,t):

    0<a<B^3m<3B^3m<t.

They are distinct and therefore cannot be congruent. Both cases
contradict (4), proving (2).

## 4. Finite candidate bounds and exact scope

Put `Q_B=3B^4(B-1)`. Then q<=Q_B. The same strict upper window gives

    2*3^e=R+3<q^3*(q-1)+3<q^4<=Q_B^4.             (7)

Thus the finite necessary list may be specified without rounded
logarithms by

    k>=1, 3^k<=3B^3(B-1),
    e>=1, 2*3^e<Q_B^4,

followed by the exact tests in (1). Every quantity is an ordinary
integer defined from the fixed radix. No efficient enumeration or
arithmetic-gate bound for that enumeration is asserted. Still less
does this decide existence of a complete compiler zero among the
remaining candidates.

**Corollary (root's ordinary-input bound on the no-wrap branch).**
Suppose additionally that a full positive zero on an authentic fixed
compiler slice lies on the canonical branch with no first-index wrap,
with q and R of the forms in Section1. The inherited input recovery
theorem then gives

    W=2^(2d*x+b)<q,  x,b,d>=1.

From (2),

    q<=3B^4(B-1)<3B^5.

If x>=3, however,

    W>=2^(6d+b)=B^5*2^(d+b)>=4B^5,

a contradiction. Thus **x is1 or2**. The finite arithmetic theorem
in Sections1--3 needed no input decoding; this additional corollary
does. It must not be applied to wrapped zeros without proving the same
input identity and width bound there.

**Review remark 1 (the earlier varying-offset question is narrowed).**
The frozen fixed-offset note leaves changing c(k) as a possible way to
avoid its constant-remainder bound. For the precise form
`q=B*3^k,R=2*3^e-3` with the full numerical window, changing c no longer
supports an unbounded family: (2)--(7) settle that narrower question.
The earlier note remains correct, and its frozen bytes are unchanged.
No conclusion about other canonical q/R relations is silently imported.

**Review remark 2 (a finite bound is not a universal exclusion).**
The stronger inference that this proof rules out every positive zero
with any q=B*3^k would be unsupported. The proof assumes the particular
index R=2*3^e-3 and leaves a finite set of possible exponents; it does
not check the remaining scale, packed-index, input, transport or native
equations at all such candidates. They remain separate obligations.

**Open question 1.** Do any of those finite candidates on an authentic
fixed compiler meet every remaining canonical direct-X83 condition
at ordinary input1 or2?
Neither this proof nor its bounded candidate list supplies a source
zero. General wrapped cases and other nondyadic canonical index
families remain outside this theorem.

## 5. Attribution, dependencies and evidence

Root supplied the contradiction using a=N/J and the split c<k versus
c>=k, and subsequently the ordinary-input corollary. My independent
challenge checked the omitted-sign danger,
both strict endpoint inequalities, the unit premise modulo3, all
offset cases admitted by the lower window, and the resulting finite
e bound. No scientific code or numerical source fixture is needed.

The literal equations and window are read from
`direct_X_authentic_outer_root.md`, lines1--49, with the additional
no-wrap input interface read at lines117--135; its whole-file SHA256 is
`35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617`.
The complete fixed-offset proof is
`direct_X_fixed_offset_repunit_divisor_root.md`, SHA256
`8e54b2963256a1a239e91a495f22c6c43c26d439c287f724b0e2679f96827717`,
read in full with its frozen metadata. The previously proved scale
family and marker obstruction are in
`direct_X_radix_compatible_three_adic_pascal.md`, SHA256
`f6f0a690d5d8f0ff2c782ea5ccd5b2e3eb08690997f7b5882ce8ca0f4792c4b8`;
the present argument does not require its valuation or population
theorems. The modified radix definition B=2^d is bound by
`complete75_half_binomial_compiler.md`, lines1--70, SHA256
`68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.

The accompanying receipt authenticates bytes and read spans only.
No predecessor, supplied, archived or frozen helper or program is
executed or imported; no source array is evaluated or propagated.
No astronomical scalar, actual compiler parameter or native tuple
is materialized, and no repository or Git edit occurs.
