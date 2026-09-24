# Two operations saved with a positive remainder interval

Replace the original E10 by the two equations

    c=k s n^2+eta, k=eta+zeta,

where eta,zeta are positive integers. In the notation of
`PELL_PARITY_PROOF.md`, these assert

    0<C/K-Y<1.

The comparison costs three operations: k(sn^2), addition of eta,
and eta+zeta. The original quadratic comparison costs five, so
this saves two operations, adding one positive witness and one
free equality test. Combined with the alternate-Pell parameter
alone it gives 117 operations, 33 positive unknowns, and 21
equations; the companion verifier is
`../verification/round4_1980_interval_optimized_certificate.py`.

## Sufficiency

The positive interval implies |C/K-Y|<1, so every step of
`PELL_PARITY_PROOF.md` applies unchanged. In particular, that proof
establishes the exact Pell indices, the two exponential relations,
and N even before its parity rounding step. It concludes

    Y=floor(xi), xi=(U+1)^(2R)/U^R,
    |C/K-Y|<1/2,

and recovers the original E10 with the positive slack
K^2-4(C-KY)^2. Thus the new interval equations imply every
requirement of the previous system after re-choosing its E10 slack.

## Necessity: the remainder is strictly positive

Consider any solution of the original stronger system, or of the
weaker quadratic system already justified in `PELL_PARITY_PROOF.md`.
The conclusions of that proof give Y=floor(xi) and

    xi-Y<1/4, xi<2Y,
    xi-C/K < R xi/[M(U+1)]
             =xi/[Y(U+1)] <2/(U+1)<2/U.           (1)

The binomial expansion in Lemma 2.24 has a positive term of order
1/U with coefficient binom(2R,R-1). Since its entire fractional
tail is less than 1, it follows that

    xi-Y >= binom(2R,R-1)/U >= 2R/U >2/U,          (2)

where R>=8. The middle inequality follows from the elementary
unimodality of the binomial coefficients: every coefficient at a
position from 1 to 2R-1 is at least binom(2R,1)=2R.

Subtracting (1) from (2) proves C/K>Y. The already established
upper bound |C/K-Y|<1/2 proves C/K<Y+1. Therefore

    eta=C-KY>0, zeta=K-eta>0

are integers satisfying both interval equations. All other witnesses
can be preserved. This proves necessity, including the strict
positivity that would not follow from an unsigned absolute-error
estimate alone.

## Exact verification and domain boundary

The companion program replaces only the approximation block in
the preserved 118-operation parity certificate. It checks the two
new equation residuals exactly, preserves and verifies both
triangular residual identities, verifies every primitive instruction,
and records all 33 positive unknowns and 21 equalities. Its count is
66 multiplications and 51 additions, totaling 117; constructing the
same numerals from 1 adds 11 operations, giving 128.

The mathematical interval proof is independent of the particular
digit widths in the packed encoding. It only uses the initial
bounds R>=N>=8, b<=N, the exponent-lemma bounds 3L<=B<=q<=N<=R,
and the fact that admissibility makes B even. Therefore it also
applies when a separately justified code optimization replaces
N=q^16 by N=q^8, and when another separately justified Pell
parameter replaces the version in E17.
