# A linear central-binomial mask in odd prime bases

This is a new conditional digit-test component, not a smaller universal
certificate. It changes the prime underlying the arithmetic encoding.
The base-two Pell kernel cannot be used unchanged to certify the new
divisibility condition. The subsequent
[base-three proof](EXPLORATION_BASE_THREE_PELL_KERNEL.md) supplies that
adaptation at the same 43-operation kernel cost, with an even-word
positive converse. A complete computation encoding still needs the
packed-word bound, parity and the different digit alphabet.

## 1. An exact mask theorem

Let p be an odd prime, N>=0, L=p^N, and 0<=P<L. Define

    D0=p^2 L, r=D0-pP-1.                         (1)

Then

    D0 divides binom(2r,r)
      iff every base-p digit of P is at most (p-1)/2.  (2)

Moreover the valuation is exactly N+2 when (2) holds; it never exceeds
N+2 under these hypotheses. For p=3, this is precisely a Boolean-word
test in radix three: all digits of P are zero or one.

Here is a complete proof. Write

    P=sum_(j=0)^(N-1) e_j p^j, 0<=e_j<p.

Subtracting pP from D0-1 has no borrow, so the base-p digits of r, from
low to high, are

    p-1, p-1-e_0, ..., p-1-e_(N-1), p-1.          (3)

There are N+2 digits, including when P has leading zeros. By Kummer's
theorem, the valuation in (2) is the number of carries in r+r. Its first
digit p-1 produces a carry. If a carry enters an interior position, its
outgoing carry equals one exactly when

    2(p-1-e_j)+1 >= p,

or equivalently e_j<=(p-1)/2. The final digit p-1 always propagates an
incoming carry. Consequently every one of the N+2 positions carries
exactly when all interior inequalities hold. If one fails, at least one
carry is missing; a later carry cannot compensate by giving more than
one at any position. Beyond the top position the incoming carry is one
and both summands have digit zero, so no further carry is possible.
This proves (2), its exact valuation, and its maximality.

The only external number-theoretic ingredient is the usual carry form
of Kummer's theorem; see [Granville, introduction to binomial coefficients
modulo prime powers](https://dms.umontreal.ca/~andrew/Binomial/intro.html).
The particular affine mask and the consequences below are derived here.

## 2. Counted arithmetic and pre-power bounds

Given L and P, (1) uses four operations:

    D0=p^2*L, t=p*P, s=D0-t, r=s-1.

Both p and p^2 are free fixed numerals; their products with variables
are counted. No repunit variable or geometric-mask equation is needed.
If L=q^4 is constructed by q2=q*q and L=q2*q2, the entire displayed
mask arithmetic costs six operations, four multiplications and two
subtractions. This excludes packing, field bounds, row geometry, and
the Diophantine realization of the divisibility and power predicates.

For that L=q^4 choice, D0=(p*q^2)^2 is an actual integer square before
any prime-power decoding. Put n0=p*q^2 in the proof only. If q>=2 and
0<=P<q^4, ordinary integer arithmetic gives

    (p^2-p)q^4 < r < p^2 q^4 = D0 = n0^2,
    n0 < r < n0^3.

The first strict lower bound follows from P<=q^4-1. Thus the scale
and index have strong preliminary bounds of the form used by indexed
Pell arguments. The upper bound P<q^4 must still be supplied before
using this bootstrap. Positivity of r alone does not give it.

Since p and L are odd after decoding, r and P have the same parity.
A positive converse using the existing even-r half-parameter argument
therefore needs even P, or a separately proved parity adaptation. This
is different from the radix-eight periodic mask, whose parity depends
only on the least digit. Here all ternary digits contribute to parity.

## 3. What this does and does not replace

The displayed six-operation arithmetic is shorter than the ten
power-and-mask operations in the radix-eight 80-operation component.
It is not a four-operation improvement to that component. There are
two concrete reasons.

First, the present 43-operation kernel proves a power of two and
two-adic central-binomial divisibility. It does not prove a power of
three or the three-adic divisibility required by (2). Replacing its
main shift a+2 by a+p and its exponential modulus 4a+3 by
2pa+p^2-1 preserves the syntactic costs of those particular expressions,
but does not by itself establish the changed ratio, exponent, index,
and positive-witness proofs. For p=3, those separate proofs are now
provided in `EXPLORATION_BASE_THREE_PELL_KERNEL.md`; they yield a
49-operation conditional mask-and-kernel component. Other prime bases
are not established by that specialization.

Second, a Boolean ternary word is not a Boolean word in radix 9, 27,
or another grouped radix. For example P=3 passes the p=3 mask: its
ternary digits are 10. But it has the forbidden single digit 3 in
radix nine. Grouping k ternary positions gives the 2^k digit values
whose individual ternary digits are zero or one, rather than only the
two values zero and one. Our present Rule 110 relation needs radix at
least eight for its raw coefficient bounds six and seven.

Even a half-adder shows why simple replacement of the radix fails.
For individually Boolean ternary words,

    A+B=S+2D

can hold without being a digitwise half-adder: A=3, B=0, S=1, D=1
gives equality, with a carry from the overlapping low S,D bits. The
same false local pattern persists with all four words strictly positive
by taking A=12, B=9, S=1, D=10. Their digits are all zero or one and
both sides equal 21. A new ternary local verifier must address carries.

These explicit obligations leave a distinct research direction: choose
a computation or constraint system suited to lower-half prime-base
digits, and adapt the joint power/binomial kernel. The mask theorem
itself is unconditional under its stated elementary hypotheses; a
complete universal system using it remains open.

## 4. Reproducible checks

The companion [checker](../verification/explore_odd_prime_half_digit_mask.py)
and its JSON receipt enumerate all words in stated small prime bases.
They compare the criterion with an independent factorial-valuation
calculation, check carries separately, and evaluate actual central
binomial coefficients for a smaller complete range. They also check
the six-instruction arithmetic, pre-power bounds, parity, and both
explicit grouped-radix/carry obstructions. The proof above establishes
the general assertion; the finite calculations corroborate it.
