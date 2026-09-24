# Putting the input in the unit position: 109 operations

The exact checker `../verification/round9_1980_certificate.py` verifies 109
arithmetic instructions (60 multiplications and 49 additions), 33 positive
unknowns, and 21 equations. The same seven fixed-numeral instructions give
116 when these numerals must be generated from 1. Previous certificates
and their receipts remain unchanged.

## Remapping two coordinates in the fixed encoding

Use the homogeneous quadratic construction in `UNIT_DIGIT_PROOF.md`, with
the same 1830 original basis rows, the guard `u delta-x^2`, and the special
target `delta^2`. Keep all its numerical layout constants, including

    v_i=1+3(6963i+i^2),  0<=i<=59,
    t_*=18218358574,    K=18218358575,
    L=5^16=152587890625>3K+2.

Only the input and the unit coordinate exchange positions. The input `x`
now has weight zero, the encoded coordinate `delta` has weight `v_0=1`,
the 58 original existential coordinates have weights `v_1,...,v_58`,
and `u` has weight `v_59`. The dummy coordinates retain their target
positions. In particular the support mask is now

    ell_0(B)=sum_{i=0}^{59} B^(v_i)+sum_{r=0}^{1831} B^(t_r).

It excludes the unit position, which belongs to the supplied input.
There are still 1892 encoded non-input coordinates and 1893 coordinates
including the input. The sum-of-coefficients bound `1900b` is unchanged.

Regard every ordinary homogeneous residual as a polynomial of total
degree exactly two in `x,delta,X_1,...,X_58,u`. For each monomial use
coefficient `2a/c` in its complementary position, where `a` is the
residual coefficient and `c` is the monomial's multinomial coefficient
in the square of the coordinate code. The same 1891 monomial weights
are distinct; which variable has weight zero does not affect the
Sidon proof. The special target `delta^2` uses coefficient 1 at position
`t_special-2`, since `delta` now has weight 1. Thus it still produces
exactly `delta^2` at its target, not twice that value.

The guard's two terms have weights `v_59+1` and 0. All monomial weights
remain between 0 and `2v_*`, so every support-separation and coefficient
bound from the 110-operation construction remains valid. Define `D(B)`
with these remapped complementary positions and retain

    e_0(B)=z sum_{j=0}^{K-1} B^j+D(B),
    V=ell_0(Z)+e_0(Z)Z^L,
    H>max(2Z^(2L+1),4^(t_*+3)Z1900^2,3L,16),

with the same power-of-two choices and strict coefficient bounds.
These are fixed, effective indices of the represented set, independent
of the input value.

## The arithmetic change

Replace `C=xB+g` in the 110-operation equations by

    C=x+g.

Everything else, including the mask `(B-4)ell`, the reversed packed code
`Y=ell+eq`, the bound `Y+C^2+alpha=q^2`, and the positive equality
`sigma=S_3`, remains unchanged. This removes the multiplication `xB`.

One must reprove the bounds before the Pell step: `C>B` is no longer
available from this definition. The geometric equation supplies the
weaker inequality that is sufficient.

## Noncircular bounds with `B<=q^2`

Positivity and the new bound imply

    ell<Y<q^2,   e<q,   C<q,   g<q.

The geometric equation `lambda(B-1)=q^2-1`, with the positive integer
`lambda>=1`, gives

    B<=q^2,       B<=n=q^8.

As `B=Hb^2` and `H` is larger than the fixed index bounds, this already
implies `q>5`. The positive quantity `N=theta lambda=(B-Z)lambda`
satisfies

    N>=B-Z>b,    N<q^2-1,
    B lambda = B(q^2-1)/(B-1)<2q^2.

The enforced positive unknown gives `S_3>0`. Independently of decoding,

    S_3=(2e-Z lambda)C^2+B lambda(1+q)
         <2q^3+2q^2(1+q)<5q^3<q^4.

Therefore `S=g+q^2(Y+q^2S_3)` again satisfies `0<S<n` with block widths
`q^2,q^2,q^4`.

For the third mask, the weaker geometry still gives the needed bound

    0<T_3=(B-4)ell<(B-4)q^2<q^4.

The complete packed mask is positive even if its first raw block is
negative:

    T+1=q^2(1+N)-(b-1)ell+q^4T_3>q^2.

Its upper bound uses the integer block range. Since `N<q^2-1`,

    T+1<q^4+q^4T_3<=q^8,

where `T_3<=q^4-1` because it is an integer. The first inequality is
strict, so `0<=T<n`. Consequently

    r=S(n^2-n)+(T+1)(n^2-1)>=n^2-1>=n.

No decoding or unproved lower bound `q>B` entered this argument.

## Checking the hypotheses of the existing Pell implications

The independent dependency audit is recorded in `PELL_RELAXED_RADIX_PROOF.md`.
The preceding proofs of the shifted Pell parameter and the Pell gap use
`r>=n`, `n>=2`, the large arithmetic lower bound on `a`, and the comparison
`B<=n`. All are now available. The fixed parameter satisfies `3L<B`.
In particular the power comparison previously used to bound `B^(3L)`
can be made directly:

    B^(3L)<=B^B<=n^n<=U^R<a,

with `U,R,a` as in the unchanged Pell argument. Also `a>B` follows
from the unchanged lower bound `a>n`. Thus the same exponent and
positivity implications apply and give `q=B^L`, together with the
required powers of two and `tau_2(S,T)=0`.

Only at this point do we infer `q>B`, since the fixed exponent `L>1`.
This makes the later borrow and digit estimates identical to those
already proved for 110 operations.

## Decoding, quotient uniqueness, and the unit value

Normalize the possible first-block borrow as before:

    d=floor((b-1)ell/q^2)<b.

After `q=B^L`, subtracting `d` from `theta lambda` changes only its
unit digit. The middle no-carry condition implies
`Y<Zq^2/(B-1)+b`; the fixed radix bounds then give
`(b-1)ell<q^2`, hence `d=0`. The packed congruence decodes

    ell=ell_0(B)+mq,    e=e_0(B)-m,    0<=m<e_0(B).

The low first mask, together with `g<q`, forces the digits of `g` to
occur exactly at allowed positive-weight positions, each less than `b`.
In particular its unit digit is zero. Because `b=x+beta`, the input
satisfies `x<b<B`; therefore `C=x+g` now has exactly the supplied input
as its unit digit and no addition carry. Its coefficient at position 1
is the encoded `delta`, and its remaining coefficients are precisely
the intended witness and dummy coordinates.

The polynomial `C` still has degree at most `t_*`, positive coefficient
sum, and sum less than `1900b`. Hence the high-mask uniqueness proof
applies word for word: `2eC^2<q`; every digit of `X=(B-4)m` is at most
`ZA-1`, where `A=C(1)^2`; and evaluation of its digit polynomial at 4
forces `X=m=0` by the fixed bound on `H`. The position of the positive
input changes neither this coefficient sum nor the high digit window.

The canonical third mask permits target coefficients 0 or 1. Its
ordinary target coefficients are even, so all homogeneous original
residuals and the guard vanish. The special coefficient is `delta^2`,
so `delta` is 0 or 1. The guard `u delta-x^2=0`, with `x>0`, forces
`delta=1`. All original inhomogeneous residuals consequently vanish.

## Positive witnesses and the exact saving

Conversely, from any genuine solution set `delta=1` and `u=x^2`, choose
a power of two `b` larger than the input and all coordinates, and use
the remapped canonical code. Its `delta` digit at position 1 guarantees
`g>0`; the unit position of `g` is zero. The established support margins
and coefficient bounds supply positive `alpha`, positive `sigma`, and
the positive packed quotient. Every mask has its required value, and
the earlier Pell necessity constructions supply the remaining unknowns.

The 110-operation schedule computed `xB` and then added `g`. The new
schedule adds `x` and `g` directly. This removes one multiplication and
changes no equality test or positive-system-unknown count. The exact
checker verifies the resulting 109 primitive instructions and all 21
source residual identities, including their triangular corrections.
