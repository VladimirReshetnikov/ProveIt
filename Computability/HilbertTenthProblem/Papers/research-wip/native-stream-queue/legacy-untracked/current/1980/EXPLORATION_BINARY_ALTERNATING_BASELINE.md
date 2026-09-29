# Binary coefficient coding: a valid local idea with an arithmetic obstruction

This is a bounded exploration of the 97-operation system checked by
`../verification/round29_1980_composed_certificate.py`. It is not a new
certificate or a universal-equivalence proof. All fixed numerals are free.
No frozen checker or article source is changed by this note.

## The tempting saving

The present shared coding block uses

    theta=B-4, lambda=(q^2-1)/(B-1),
    tl=theta*lambda, Tcoef=tl+1,
    three_lambda=3*lambda, R2=Tcoef+three_lambda,
    Omega=lambda-e, P2=tl*q.

It has three multiplications and three additions, with subtraction counted
as one reversed addition. The equality `q^2=R2` is the geometric equation.
Replacing the fixed radix four by two would change theta to B-2 and give

    q^2=Tcoef+lambda.

This deletes the multiplication by three if all other constructions can
be retained. They cannot simply be retained: the current coefficient code
has digits 0, 1, and 2, whereas the binary digit mask only permits 0 and 1.

## A parity construction does produce binary coefficient digits

Let a polynomial baseline have coefficient one in odd positions and zero
in even positions. Require positive coefficients of D to have even
exponents and negative coefficients to have odd exponents. Then

    e0(T) = sum_(odd j<K) T^j + D(T)

has coefficients in {0,1}, provided D has coefficients in {-1,0,1}.
The local parity requirements of the homogeneous circuit can be met with
fresh copies. For an ordinary target `2F+delta^2`, its target position is
even. A positive cross term XY requires X and Y to have equal weight
parities; a negative cross term W*delta requires their weight parities
to differ. Addition gates require both positive operands to have delta's
parity and the negative output to have the other parity. A copy can relate
opposite parities; two copies through an intermediate coordinate give a
fresh copy of the original parity. Negating a copy equation changes its
orientation without changing its meaning.

Prescribed parities are compatible with monomial uniqueness. For example,
take the positive coordinate weights `Q*3^i+p_i`, where Q>=3 and p_i is
zero or one. A sum of two weights determines the base-three part and then
its small remainder, so the usual unique quadratic monomials remain
unique. Widely separated target intervals can independently be given the
required parity.

There is no need to pair F with -F in this binary version. At delta=1,
the target test is

    0 <= 2F+1+epsilon <= 1, epsilon in {-1,0},

which forces F=0 for either possible incoming carry. A target delta^2
forces delta in {0,1} even without a known incoming carry: its possible
raw values are 0,1,2, and only the first two are squares.

The first target can be the direct guard

    2u*delta-x^2.

Its target position is odd, and u has parity opposite to delta. Its sole
negative D term is at the target position itself because x has weight
zero. All earlier contributions in its isolated interval are nonnegative,
so its incoming carry is zero. At delta=0 it fails for positive x. At
delta=1, choosing u=ceil(x^2/2) gives the allowed raw value zero or one.
Consequently this guard supplies the needed nonzero delta without a
copied input. If an explicit unit coordinate X is wanted, the target
`2X*delta-delta^2` has an odd position and forces X=1 once delta=1.

These observations address the local circuit/parity obstruction. They
do not establish the complete canonical-code, alias, or Pell arguments
for a new binary system.

## Exact accounting of the missing baseline

After the exponent is recovered, write

    mu = 1+B^2+...+B^(2L-2) = (q^2-1)/(B^2-1),
    nu = B*mu,
    lambda = nu+mu.

For the odd baseline, the third-block coefficient must be `Omega=nu-e`.
The most direct shared block is therefore

| Instruction | Operation |
| --- | --- |
| nu=B*mu | multiplication |
| lambda=nu+mu | addition |
| tl=theta*lambda | multiplication |
| Tcoef=tl+1 | addition |
| R2=Tcoef+lambda | addition |
| Omega=nu-e | addition |
| P2=tl*q | multiplication |

This is **seven operations: three multiplications and four additions**,
one more than the present six-operation block. The calculation has
already removed `3*lambda`; adding that proposed saving again would
double count it. An even baseline has the same cost: form B+1, multiply
by mu to get lambda, and use Omega=mu-e.

Changing the geometry directly to `mu*(B^2-1)=q^2-1` does not by itself
remove this issue. The packing mask and its positive offset still need
the full repunit lambda. Computing that repunit, or the corresponding
full mask, must be included in any proposed complete schedule.

There is a second independent accounting issue if the current main Pell
parameter is retained. It is A=a+4, so theta=B-2 changes its shared
exponent difference from `a-theta` to `a-theta+2`. A binary proposal must
either pay for that additional addition, change the main parameter and
prove the associated exponent/rounding statements, or find another
shared expression. The table above does not charge this possible extra
Pell operation.

## Why a constant binary baseline is not a repair

With a constant baseline one, binary e digits make the coefficients of
e-lambda nonpositive. With a constant baseline zero, they are
nonnegative. Under the current small-coefficient, carry-zero-or-minus-one
analysis, a coefficient polynomial of only one sign cannot directly
encode the required mixed-sign arithmetic targets. In particular, a
nonpositive polynomial times the nonnegative digit polynomial C(T)^2
has nonpositive coefficients everywhere; the binary mask can only accept
its zero target values. It does not furnish the positive and negative
terms of a general gate equation. Reversing the subtraction changes all
signs together and has the same limitation.

This is an obstruction to the displayed uniform-baseline constructions,
not an arithmetic-circuit lower bound and not an impossibility theorem
for binary encodings. A useful continuation would have to absorb at
least one of the two baseline-conversion instructions into an independently
needed packing operation, or change which global masks are required.
No count below 97 is claimed here.
