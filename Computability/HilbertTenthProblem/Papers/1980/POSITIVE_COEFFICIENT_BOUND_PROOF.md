# A positive computed coefficient removes the square bound

The exact checker `../verification/round10_1980_certificate.py` verifies 108
arithmetic instructions: 60 multiplications and 48 additions. There are
34 positive unknowns and 22 equations. The seven fixed-numeral instructions
give 115 operations under that stricter convention. The 109-operation
system and all earlier certificates are unchanged.

## Equations and the arithmetic saving

Keep the fixed index, homogeneous masks, and input-unit code `C=x+g` from
`INPUT_UNIT_PROOF.md`. Replace its bound

    Y+C^2+alpha=q^2,    where Y=ell+eq,

by

    Y+alpha=q^2.

Introduce a positive unknown `Omega` with the equality

    Omega=Z lambda-2e.

The right-hand side is already computed in the old schedule, up to its
sign. Reverse that subtraction and use

    P_1=(Z lambda-2e)C^2,
    P_2=B lambda(1+q),
    S_3=P_2-P_1.

These have exactly the same arithmetic cost as the old subtraction,
product, and sum. The value of `S_3` itself is unchanged. The equality
`Omega=Z lambda-2e` is a free test between a positive system input and an
existing computed register. As before, a separate positive unknown
`sigma` satisfies `sigma=S_3`. Only the addition of `C^2` to `Y` is
removed. All other equations, including both Pell blocks and the mask
factor `B-4`, remain unchanged.

The name `Omega` denotes the new positive system unknown. It is distinct
from the old Pell abbreviation `U=wn^2` and from the encoded guard
coordinate `u`.

## The weaker initial size bound is enough for packing

Before any decoding, the new bound gives

    0<ell<Y<q^2,    0<e<q.

The geometric equation and positivity of `lambda` still give

    B<=q^2,    q>5,    B<=n=q^8,
    b<N=(B-Z)lambda<q^2-1,
    P_2=B lambda(1+q)<2q^2(1+q)<3q^3.

Both `Omega` and `sigma` are positive integers. Consequently

    0<S_3=P_2-Omega*C^2<P_2,
    C^2<P_2/Omega<=P_2<3q^3<q^4.

In particular `g<C=x+g<q^2`. This is weaker than `g<q`, but the first
packing block has width `q^2`, so it is sufficient. The integer bounds

    0<=g<q^2,    0<=Y<q^2,    0<S_3<q^4

give `0<S=g+q^2(Y+q^2S_3)<q^8=n`.

The packed mask `T` is unchanged. Its bounds use only `ell<q^2`,
`B<=q^2`, and `b<N<q^2-1`, and therefore hold without a bound on `C`.
Explicitly, with

    d=floor((b-1)ell/q^2),    u_0=(b-1)ell-dq^2,

the three normalized blocks are

    T=(q^2-1-u_0)+q^2(N-d)+q^4(B-4)ell.

They lie in `[0,q^2)`, `[0,q^2)`, and `[0,q^4)`, respectively. Thus
`0<=T<n` and `r>=n^2-1>=n`.

Every hypothesis of the Pell argument in `PELL_RELAXED_RADIX_PROOF.md` is now available.
Its Pell argument uses no further bound on `C` or `g`, and gives
`q=B^L`, the required powers of two, and `tau_2(S,T)=0`. There is no
use of `q>B` before this conclusion.

## Recovering the stronger bound before digit decoding

Now `q=B^L>B`, so

    lambda=(q^2-1)/(B-1)>q.

As `e<q` and `Z>=4`,

    2e<2q<2lambda<=Z lambda/2,
    Omega=Z lambda-2e>Z lambda/2.

Positivity of `S_3=P_2-Omega*C^2` therefore sharpens the earlier bound:

    C^2<P_2/Omega
         <2B(1+q)/Z
         <=B(1+q)/2
         <q(q+1)/2
         <q^2.

Thus `C<q` and `g<q` have been proved before either is needed in the
digit-decoding argument. All later steps of `INPUT_UNIT_PROOF.md` now
apply without alteration: the first-block borrow vanishes; the packed
code is decoded; the high mask removes the quotient ambiguity; and the
two-valued homogeneous target tests force `delta=1` and every original
quadratic residual to vanish. This proves soundness.

## Positive witnesses and cost

For genuine encoded witnesses, the preceding 109-operation construction
already has `e<q`, `lambda>q`, and positive `S_3`. Set

    Omega=Z lambda-2e>0,
    alpha=q^2-Y>0.

All other positive unknowns remain valid. This proves necessity with
the new positive domain fully accounted for.

The exact schedule reverses the old coefficient subtraction and the
final sign of its product in `S_3`, adds one free equality test to the
fresh positive unknown, and deletes one addition. No coefficient is
silently assumed positive and no extra arithmetic is hidden in the
positivity requirement. The resulting certificate has 108 arithmetic
instructions, 34 positive unknowns, and 22 equations, as checked by the
primitive and polynomial-residual receipt.
