# A 120-operation packed recoding

Let `L=5^59`, `M=5^58`, and let `(z,u,y)` be an admissible Jones index,
for a normalized nonnegative quartic polynomial in 59 variables including
the input. Put `Z=2z` and

    V = y + u Z^(2L).

Choose a power of two H strictly greater than

    max(2 Z^(4L+1), Z 60^4, 3L).

Then `(Z,V,H)` is the new admissible index. Its construction is part of
encoding the represented set, not an arithmetic task hidden in the
certificate. In particular H and V are fixed inputs, not arbitrary
existential witnesses. The complete parameter list is `(x,Z,V,H)`.

## Explicit system

Define `B=H b^4` and `C=1+xB+g` as abbreviations. Begin with the
20-equation modified system in the satellite, and change it as follows:

* Replace every occurrence of the old radix `b^5` by B.
* Replace E1 by `b=x+beta` and `e l C^2+alpha=q^2`.
* Replace E3 by `theta+Z=B`.
* Replace E4 and E5 together by `e+l q^2=V+t theta`; delete m.
* Replace `2(e-z lambda)` in E7 by `2e-Z lambda`.
* Replace E13' by `c=kappa+phi`.
* Use exponent base B and exponent L in E18--E20, so E18 is
  `mu=q+kappa(a-B)+rho(2aB-B^2-1)` and E20 is
  `kappa=L+Delta(a-1)`.

The system has 20 equations and 32 positive unknowns: it adds beta and
removes m. B and C are abbreviations whose computations are charged by
the schedule. All other source equations retain their original meaning.

## Noncircular bounds for the Pell lemmas

Assume the polynomial system has a positive-integer solution, before
assuming either b is a power of two or `q=B^L`. The new bound gives

    e<q^2, l<q^2, C<q.

Also b>x>=1 and `C=1+xB+g>B`, so q>B>b>=2 and g<q. The
geometric equation gives

    lambda=(q^4-1)/(B-1)>q^3.

Putting `D0=(Z/2)lambda-e=z lambda-e` yields
`0<D0<z lambda`. Consequently the third S-block satisfies

    0 < -2 C^4 D0+B lambda(1+q^4)
      < B lambda(1+q^4) < 2q^8 < q^9.

The lower bound follows from `C<q` and `B>2z`, since
`2C^4D0<2z lambda q^4<B lambda q^4`.
The other block bounds are elementary:

    0<g<q<q^3,
    0<q^3-1-(b-1)l<q^3,
    0<e+lq^2<q^4,
    0<(B-Z)lambda<(B-1)lambda=q^4-1,
    0<(B-2)q<q^2<q^9.

For the second bound use l<q^2 and b<q. For the third, integer
e,l<=q^2-1 give `e+lq^2<=q^4-1`. With widths
`N1=q^3,N2=q^4,N3=q^9`, all packed quantities S,T therefore lie
in `[0,n)`, where `n=q^16`. They are positive; hence E7 gives
`r>=n^2-1>=n`. Admissibility of H gives

    3<3L<=B<q<=n<=r,

and the remaining bounds in Lemma 2.25 follow. To restore the version
of E13' required by Lemma 2.26, apply the elementary Pell spacing lemma
proved in PELL_GAP_PROOF.md: since a>=20r, positive Pell ordinates
c>kappa satisfy `c-kappa>=2a-1>2r+1`. Thus
`phi_old=c-kappa-(2r+1)>0` restores E13'.

Lemmas 2.25 and 2.26 now apply to the polynomial system and give b a
power of two, `q=B^L`, and `n^2 | binomial(2r,r)` simultaneously.
As H is an admissible power of two, B,q,n are powers of two. Lemmas
2.16 and 2.11 therefore recover all three separate no-carry conditions.

## Decoding the single coefficient congruence

Let `e0(B)` and `l0(B)` be the intended polynomials with digit values
specified by (4.5)--(4.6), and put

    F(B)=e0(B)+l0(B) B^(2L).

The first summand has degree at most L and the second uses exponents
`2L+5^i` for `1<=i<=58`. Their digit positions are disjoint, all their
digits lie in `[0,Z)`, and `F(Z)=V`. The highest exponent is `2L+M<4L`.

Take `Y=e+lq^2`, m=k=4L and the digit base Z in Lemma 2.9. Its
hypotheses hold because

* `Y=V+t(B-Z)` is the new congruence;
* `Y<q^4=B^(4L)<Z B^(4L)`;
* the second no-carry condition is
  `tau_2(Y,(B-Z)lambda)=0`, with the mask extending over 4L digits;
* `B>=H>2Z^(4L+1)`.

The lemma gives `Y=F(B)`. Since e,l<q^2 and the intended e0,l0 also
lie in `[0,q^2)`, uniqueness of quotient and remainder in division by
q^2 implies `e=e0(B)` and `l=l0(B)`. Thus the original two coefficient
codes are recovered exactly; packing loses no information.

The first no-carry condition then shows g encodes positive-witness
values with bound b, and C encodes input x and those values. The
coefficient bound `z 60^4 b^4<B/2` follows from admissibility of H.
The third no-carry condition therefore proves the original quartic
polynomial vanishes, exactly as in section 4 of the source. This proves
soundness for the same recursively enumerable set.

## Necessity

For an actual solution of the represented quartic equation, choose a
power-of-two b bounding x and all its witnesses. Set B=H b^4 and
q=B^L, and form the actual codes. The normalization ensures g>0.
The source bounds are `e<2zB^L`, `l<2B^M`, `g<bB^M`.
Since `x<=b-1` and `M>=1`,

    1+xB <= bB <= bB^M,
    C=1+xB+g < 2bB^M.

It follows that

    e l C^2 < 16z b^2 B^(L+3M)
             =16z b^2 B^(8M)
             <B^(8M+1)<B^(10M)=q^2.

Here H>16z and b>=2 justify `16z b^2<B`; L=5M and 2M>1
justify the last inequality. Thus alpha and beta are positive.

The packed polynomial F has nonnegative digits and positive degree;
since B>Z, `F(B)>F(Z)=V`. The difference is divisible by B-Z, so
`t=(F(B)-V)/(B-Z)` is a positive integer. This constructs the new
single congruence witness. All three no-carry conditions hold by the
original digit proof. The remaining Pell witnesses, including positive
rho and Delta, follow from the same necessity construction as the
satellite, using exponent base B and exponent L. The new phi is
`c-kappa>0`, as implied by the original stronger gap.

## Count and exact verification

The H,Z recoding and split E1 give 126 operations. Sharing the existing
C^2 replaces the formerly separate square g^2 and saves one. Combining
the two congruences saves one multiplication and one addition, giving
123. The common product UM and E2/E3 substitution save one
multiplication each; the Pell gap saves one addition. The final count is
120: 68 multiplications and 52 additions (subtractions included).
The companion program verifies the actual histogram, every equality,
and the triangular E7 residual identity. This is a proved upper bound,
not a lower bound or an optimality claim.
