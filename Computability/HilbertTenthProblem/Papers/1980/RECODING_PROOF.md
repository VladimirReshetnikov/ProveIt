# Three operations saved by recoding

This note concerns the basic straight-line measure, in which integer
numerals and supplied input parameters are free. It accompanies
`../verification/round4_1980_recoded_certificate.py`.

Let `L=5^59`, `M=5^58`, and let `(z,u,y)` be an admissible Jones triple for
a normalized quartic polynomial in 59 variables including its input. Encode
that triple instead by `(Z,u,y,H)`, where `Z=2z` and `H` is any power of two
strictly greater than

    max(2 Z^(2L+1), Z 60^4, 3L).

The input of the universal system is `(x,Z,u,y,H)`. Constructing this
admissible index happens when the represented recursively enumerable set is
encoded. In particular, `H` is explicitly an additional parameter, not an
unchecked auxiliary witness that the certificate may choose arbitrarily.

In the original 20-equation modified system make these changes:

1. Set the radix to `B=H b^4` wherever the old radix `b^5` occurred.
2. Replace E1 by `b=x+beta` and `e l g^2+alpha=q^2`, with positive
   `beta,alpha`.
3. Replace E3 by `theta+Z=B`, and replace the coefficient
   `2(e-z lambda)` in E7 by `2e-Z lambda`.
4. In the exponent-replacement equations E18--E20 use the base `B` and
   exponent `L`: thus
   `mu=q+kappa(a-B)+rho(2aB-B^2-1)` and
   `kappa=L+Delta(a-1)`. Retain the strengthened E13'.

All other equations are retained. The program implements `B=H b^4` as
three instructions, so B need not be a separate unknown or equation.

## The coding proof still applies

The role of `b>xy` in section 4 of the corrected 1982 paper is to ensure
`b>x`, a sufficiently large radix for the digit-extraction lemma, and a
large enough radix to prevent carries. Here these requirements follow
separately from `b>x` and the admissibility of H:

* `B=H b^4 > 2 Z^(2L+1)`, as required by Lemma 2.9 with the old
  digit base `Z=2z` and length `2L`.
* Every coefficient of the product of the coded polynomial and the
  fourth power of the code has absolute value less than
  `z 60^4 b^4 < B/2`.
* Since H and b are powers of two, B is a power of two.

Use the original, uncombined U1 and U6 form of the proof, with U1 now
simply `x<b`. The bound `e l g^2<q^2` immediately gives
`e<q^2`, `l<q^2`, and `g<q`. Therefore the original masks,
`lambda=(q^4-1)/(B-1)`, and the three no-carry conditions work without
changing their lengths. The digit-extraction conclusions give the same
coefficient polynomial and therefore the same set of inputs x.

The bounds needed even before applying the exponent lemma also follow
directly from the polynomial equations. For an admissible index `u,y>=Z`;
positive t,m give `l>=u+theta>=B` and `e>=y+theta>=B`.
Thus `q^2>e l g^2>=B^2`, so `q>B>=3L`. In particular b>=2.
The geometric equation gives `lambda>q^3>e`, since q>B, so
`0<D0=z lambda-e<z lambda`. For the third S-block put
`C=1+xB+g`. Integer g<q implies

    C <= xB+q < (b+1)q.

Since b>=2, `(b+1)^4 <= (3b/2)^4 < 6 b^4`, and H>12z. Therefore

    2 C^4 D0 < 12z b^4 lambda q^4 < B lambda q^4.

This proves positivity of `S3=-2 C^4 D0+B lambda(1+q^4)` without
assuming the intended exponential equation. For its upper bound,

    S3 < B lambda(1+q^4)
       = B(q^8-1)/(B-1) < 2q^8 < q^9.

Also `T1=q^3-1-(b-1)l` lies between zero and q^3 because
`l<q^2` and b<q. Integer e,l<q^2 give `S2=e+lq^2<q^4`, while
`T2=(B-Z)lambda<(B-1)lambda=q^4-1`. Finally
`S1=g<q<q^3` and `0<T3=(B-2)q<q^2<q^9`. Thus all three blocks
lie in their prescribed widths, before using q=B^L or b being a power
of two. Their positivity also gives `r>=n^2-1>=n`, with `n=q^16`.

The hypotheses `3<3L<=B<=q<=n<=r` of Lemma 2.26 now follow from
the polynomial system alone. The remaining hypotheses of Lemma 2.25
follow from `q>B>b` and the displayed bounds. Those lemmas give
simultaneously `b` a power of two, `q=B^L`, and the required central
binomial divisibility. H was already a power of two by admissibility,
so B and q are powers of two as required to unpack the no-carry
conditions. Applying the digit argument above proves membership.

## Necessity for actual codes

Choose a power-of-two b large enough to bound x and all witnesses of a
solution to the representing polynomial; take `B=H b^4` and `q=B^L`.
For the actual codes the original estimates give

    l < 2 B^M,  e < 2z B^L,  g < b B^M.

Consequently

    e l g^2 < 4z b^2 B^(8M) < B^(8M+1) < B^(10M)=q^2,

because H>4z and `2M>1`. This proves the new alpha is positive;
beta=b-x is positive. The digit congruence witnesses t,m remain positive
because B>Z and the encoded polynomials increase strictly with the base.
The remaining carry and Pell constructions are the same as in the source
proof, with exponent base B and exponent L. The Pell witnesses exist with
positive rho,Delta and the strengthened E13' as in the satellite's
necessity proof, using `3L<=B<=q<=n<=r`.

## Operation accounting

The old seven-operation E1 is replaced by five instructions: the square
`g^2`, products `e l` and `(e l)g^2`, addition of alpha, and `x+beta`.
Computing `B=H b^4` takes three multiplications, the same as `b^5`.
The old separate multiplication `2z` disappears, while evaluating
`2e-Z lambda` takes three instructions, the same as `2(e-z lambda)`.
The exponent-base replacement changes operands but no instruction count.
Hence this recoding alone takes `129-2-1=126` instructions. The program
checks all 21 residuals by exact polynomial arithmetic. Further changes
to the shared Pell or packing computations can be applied independently.
