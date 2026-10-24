# Two smaller positive-domain equations

The full displayed equations and mathematical proof are in
`positive_reductions.tex`, intended as a section of the main article.
The source snapshot is ProveIt `cf4a5218a5a4e4358d3f5314151b6b05d4aa384e`.

| Construction | Variables | Domain | Exact degree | Binary gates |
|---|---:|---|---:|---:|
| Source 70 | 11 | strictly positive integers | 325 | 113 |
| This component | 11 | strictly positive integers | 269 | 111 |
| Source 69 | 12 | strictly positive integers | 82 | 102 |
| This component | 12 | strictly positive integers | 78 | 102 |

All four coefficient ports use the same complete source-44 compact tuple,
with beta = 2^590069 - 1. Its actual numeral payloads and
`native/ACTIVE_BINDING.json` are supplied; no coefficient is a free unknown.
The supplied builders generate ordinary integer polynomial circuits.

## Eleven variables: exact changes to source 70

1. Replace `I=i*q*(q-1)*c^2` by `I=i*c^2`. Source 69's rational Pell
   saturation theorem supplies the missing integrality of the auxiliary
   rational root. Thus the earlier coprimality condition is unnecessary.
2. Keep the universal radical majorant `L=3*Df*(c*T+Rhat)`, but use the
   separate transport multiplier `h=Df*c*T` and `W=1+(q-1)*h`.
   The weighted carrier's soundness uses only `h>0`. For canonical
   witnesses, `F+alpha<q`, `Rhat<2*q^4<c<=c*T`, hence `L<6*h`.
   The canonical first carrier gives `r>q*W-2*k>6*h>L`, so the new
   coordinate `n=r-L+f+y` is strictly positive.
3. Use `S=q*Y`, `U=q*S` in the main carrier. The source-74 cofactor
   argument retains the missing factor three: with `g=gcd(3,Y)` and
   `q^3|Y`, `gcd(q,g)=1` implies `q^3|(Y/g)`, so
   `q*Y/g>=q^4>R`. This proves the same exact index recovery.
4. The final product needs no additional parity restriction: its norm
   residual N8 is a square modulo 4, so N8 cannot equal -2. Therefore
   `(N8+1)*(A1+1)=1` forces both factors to be 1, even if A1 is not
   separately a square residue modulo 4.

The three-root rational extraction, separation inequalities, and signed
root treatment are reproduced in the article. The source-69 rational
Pell descent is also reproduced. In particular, all roots extracted from
the octic norm are rational before any integrality is asserted, and the
exceptional zero sum is excluded by a dominant-root estimate.

The exact top-degree coefficient of

`j^36*i^24*eta^57*X^42*Y^93*T^8*alpha^8*gamma`

is `8*(3*beta)^36>0`, independent of K0, MC, and MF. Together with the
symbolically checked degree upper bound this proves exact degree 269
after the actual numerical specialization.

## Twelve variables: exact changes to source 69

Keep its saturated two-witness merger unchanged. Replace the main modulus
`U=q^5`, `S=q^4` by `U=q^2*Y`, `S=q*Y`. The preceding cofactor argument
restores the same source witnesses. The residual degrees are now
15, 13, and 50. The product finalizer gives exact total degree 78.

The coefficient of

`j^18*F^2*eta^11*X^12*Y^23*t^8*n^2*gamma*alpha`

is `64*(6*beta)^18>0`. The three residuals are squares modulo 4 because
q is even in this construction, and the merger's last subtracted term
contains an explicit factor 4. The product is therefore equivalent to
their simultaneous vanishing.

## Verification and its limits

Run `python3 verify.py` for the complete offline replay, including fixed
coefficient reconstruction in a temporary directory. For the separate
algebra checks run `python3 build11.py`, `python3 build12.py`,
`python3 verify11.py`, and `python3 verify12.py`. These use only Python's
standard library. The two
verifiers do not import the builders. They check literal formulas and
universal identities by exact sparse integer-polynomial arithmetic, all
gate dependencies and live inputs, exact leading forms, the displayed
nonzero coefficients, and operation counts. The second also replays
small canonical local Pell examples and two negative controls.

The audits certify finite algebra. They do not decide consistency and
do not replace the unbounded proofs or the inherited compiler/calibration
theorems. This component claims ordinary mathematical reductions
formalizable in ZFC, not a new end-to-end Lean or Rocq certificate.
