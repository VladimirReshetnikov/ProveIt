# High digits when the third block uses only B lambda q

This is an independent audit of the high-mask quotient argument for the
proposed single-offset successor to the 104-operation certificate. It
proves the needed lemma for

    S3=(2e-Z*lambda)*C^2+B*lambda*q,

with the existing third mask `(B-4)*ell`. The fixed support and H bound
are unchanged. The separate low-target proof changes the ordinary
coefficient targets to `4F_i^h+delta^2` and retains the special target
`delta^2`. This note concerns high digits only; it does not by itself
assert a complete new certificate.

## Hypotheses at the point of use

The preceding decoding has established

    B=H*b^2, q=B^L, lambda=sum_(j=0)^(2L-1) B^j,
    K=t_*+1, L>3K+2,
    ell=ell0+m*q, e=e0-m, 0<=m<e0<B^K,
    C=sum_(j=0)^(K-1) c_j B^j, 0<=c_j<b,
    C(1)<1900*b, C(1)>=1,
    0<e<B^K, (B-4)*ell0<q.

The fixed admissibility bound is exactly the existing one:

    H>4^(t_*+3)*Z*1900^2.

Write `A_C=C(1)^2`. Then

    0<Z*A_C<Z*1900^2*b^2<B/4,
    2e*C^2<2B^(3K)<q.

The first inequality follows with a much larger margin from the given
H bound. The second uses C<B^K and L>3K+2. The no-carry relation for
the third blocks is already available from the binomial argument.

## Exact high digits from one Euclidean division

Consider the polynomial value

    V=Z*lambda*C^2.

Every coefficient of this product is between zero and Z*A_C, hence
strictly less than B. Consequently its formal coefficients already are
its base-B digits; no normalization carry is needed. Since the degree
of C^2 is at most 2K-2, its coefficients sum to A_C, and lambda has
coefficient one at every position from zero through 2L-1, the digits
of V at positions L through L+K are all exactly Z*A_C. Indeed

    2K-2<=L, L+K<=2L-1.

Write V=q*V_high+V_low with 0<=V_low<q. Since 0<2e*C^2<q,

    epsilon=floor((2e*C^2-V_low)/q) belongs to {-1,0}.

The exact quotient of the new third block is therefore

    floor(S3/q)=B*lambda-V_high+epsilon.         (1)

At its unit position, B*lambda has digit zero and V_high has digit
Z*A_C. Thus the normalized unit digit of (1) is

    B-Z*A_C+epsilon,

and its carry to the next position is -1. At every following position
from one through K, B*lambda has digit one, V_high has digit Z*A_C,
and the incoming carry is -1. The normalized digit is therefore

    B-Z*A_C,

again with outgoing carry -1. Higher coefficients cannot affect these
lower positions. Hence the S3 digits satisfy the exact formulas

    digit_L(S3) in {B-Z*A_C-1, B-Z*A_C},
    digit_(L+j)(S3)=B-Z*A_C for 1<=j<=K.         (2)

All displayed digits are in [0,B-1], since 0<Z*A_C<B/4 and B>8.
This proof does not require the lower coefficients of 2e*C^2 to be
small, and does not assume that their individual carries vanish.
The inequality 2e*C^2<q is used only at the exact integer division.

## The high quotient must vanish

Put X=(B-4)*m. Since `(B-4)*ell0<q`, the quotient of the third mask
by q is exactly X. Since m<B^K,

    0<=X<B^(K+1).

Write `X=sum_(j=0)^K x_j B^j` with 0<=x_j<B. The binary no-carry
condition implies that the sum of the two base-B digits is less than
B at every position. Applying (2) gives

    x_0<=Z*A_C,
    x_j<=Z*A_C-1 for 1<=j<=K.

The weaker common bound x_j<=Z*A_C is enough. Let
`F(T)=sum_(j=0)^K x_j T^j`. Because B=4 modulo B-4 and
F(B)=X is divisible by B-4, F(4) is divisible by B-4. But

    0<=F(4)
      <=Z*A_C*(4^(K+1)-1)/3
      <Z*A_C*4^(t_*+2)/3
      <B/12
      <B-4.                                    (3)

For the penultimate inequality, use A_C<1900^2*b^2 and
H>4^(t_*+3)*Z*1900^2. Thus F(4)=0. Its coefficients are
nonnegative, so every x_j is zero. Therefore X=0 and m=0.

The canonical values ell=ell0 and e=e0 are consequently recovered.
No increase in H, no additional support position, and no additional
equation is required. The single-offset change loses one unit of
the lower bound at the first high digit, but the existing geometric
margin in H already absorbs that difference.

The deterministic companion
`../verification/single_offset_high_digits_check.py` checks formula (2)
and high-mask rejection on bounded integer examples. Those finite
regressions supplement the proof; they do not establish its universal
quantifiers or the rest of the encoding theorem.
