# Independent review of the varying-offset three-adic obstruction

**PASS.** Under the stated repunit, literal-index divisibility and strict
numerical window, the proposed bound

    3^k <= 3B^3(B-1)

holds for all positive integers d,k,e with B=2^d, q=B*3^k and
R=2*3^e-3. The additional authentic no-wrap input theorem implies
x is 1 or 2. No author correction is requested. This review is independent
of root's proposed proof and Pascal's writeup; it checks their argument
and the exact inherited interfaces, without scientific execution.

## 1. Hypotheses and sign audit

Write m=B-1 and t=3^k. The literal packed index in the authenticated
outer note is a multiple of J because q-1=mJ and hence J divides q^2-1.
Thus J divides R is a necessary condition independently of the signs
of the packed coefficients. Both sides of the numerical window agree
with that same note. The theorem may allow synthetic B as small as 2;
the authentic compiler satisfies stricter size and radix conditions.

Since q>=6, the lower window implies R>q^3. Therefore c=e-3k is an
integer satisfying 2*3^c>B^3>=8, and c>=1. This excludes zero and
negative offsets before using an integral power 3^c.

The identity

    B^3 R = 2*3^c q^3 - 3B^3

and q=1 modulo J give J dividing N=2*3^c-3B^3. There is no modular
cancellation by B. Equality N=0 would imply
3^(c-1)=2^(3d-1), impossible since the positive binary exponent is at
least 2. Thus a=N/J is a nonzero integer. Because mJ=Bt-1 is not
divisible by 3, neither m nor J is divisible by 3. As c>=1, 3 divides N
and therefore 3 divides a.

These observations alone do not make a positive. Under the contradiction
hypothesis t>3B^3m, however,

    J-t=(t-1)/m>0,  J>3B^3,  N>-3B^3.

It follows that a>-1. Integrality and nonvanishing give a>=1, and the
multiple-of-3 property strengthens this to a>=3. This is the required
sign argument, including the possible negative N case.

## 2. Both offset cases and the strict endpoints

The upper window gives Gamma=(R+3)/q^3<q-1+3/q^3<q. Hence

    0<a=N/J < B^3(q-1)/J = B^3m.

If c<k then N<2*3^c<2t<2J, so a<2, contradicting a>=3.
If c>=k, the exact equation

    a(Bt-1)=2m*3^c-3B^3m

reduces modulo t to a=3B^3m modulo t. But

    0<a<B^3m<3B^3m<t.

The two residues are distinct representatives in [0,t), again a
contradiction. The cases exhaust the integer c admitted by the lower
window. The signs and strict inequalities do not rely on an implicit
large-parameter approximation.

The resulting q<=Q_B=3B^4(B-1) and the upper window yield

    2*3^e=R+3<q^3(q-1)+3<q^4<=Q_B^4,

since q^3>3. Thus both exponents have a finite computable necessary
list at every fixed radix. This conclusion does not determine whether
any remaining candidate extends to a complete source zero.

## 3. Input corollary and retained scope

The original outer note's no-first-index-wrap argument gives exactly
W=2^(2d*x+b)<q on a full positive zero. It does not require the present
family's scalar valuation argument. Under that additional interface,

    q<=3B^4(B-1)<3B^5.

If x>=3 then W>=2^(6d+b)=B^5*2^(d+b)>=4B^5, a contradiction. The
positive input is therefore 1 or 2. Without the no-wrap interface the
proof does not recover W and supplies no ordinary-input bound.

The fixed-offset note explicitly left varying offsets as a direction
requiring further work. The present theorem settles the unbounded-family
question for this precise q/R form with the full window. It does not
settle the remaining finite candidates, other index forms, wrapped
input decoding, or the general direct-X83 soundness obligation.

No wrong or unproved new claim arose in this review. The author's
Review remark 1 records how the earlier varying-offset question is
narrowed; Review remark 2 retains the unsupported inference from a
finite bound to total exclusion. Open question 1 keeps completion of
the remaining candidates explicit. No arithmetic source or operation
count is changed.

## 4. Read and verification scope

I read the entire new author note and metadata receipt. I also read the
complete fixed-offset note and its metadata, the authentic outer note
at lines 1--49 and 117--135, and the modified compiler's radix definition
at lines 1--70. I authenticate the author's five dependency files and
all declared read-span bytes; that metadata check is not a claim to
have re-read the radix-compatible valuation proof or the older native,
Pell and source constructions.

The companion reviewer receipt binds the final author note/receipt,
records those proof-read spans, and verifies the author's dependency
byte and span pins. No predecessor, supplied, archived or frozen helper
is executed or imported. There is no scientific test program, source
array evaluation, degree propagation, candidate enumeration, or native
witness construction. All mathematical conclusions above follow from
the all-size integer proof and the stated inherited input interface.
