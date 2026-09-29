# Proof audit and boundaries

## Mathematical dependencies

1. A nonempty well-ordered subset E of the positive reals has a positive least
   exponent delta. Neumann's two-factor support lemma plus the bound k*delta <=
   gamma gives finite ordered input words ending at each exponent gamma. Bounded
   support is NOT assumed finite.
2. In a fixed Jordan basis A0=S+N, ad(N)^(2m-1)=0 and spectral-difference masks
   commute with ad(N). The finite geometric inverse is on the complement of the
   resonant mask, not an inverse on the whole matrix space.
3. Positive-support Picard differences gain at least delta in valuation, which
   proves coefficientwise existence and uniqueness. The resonant part has finite
   exponent support because the matrix spectrum is finite.
4. B=N+sum R_rho is block triangular by increasing real eigenvalue, with nilpotent
   diagonal blocks. Hence B^m=0. This argument does not assume S and B commute.
5. The identity x^S B x^(-S)=N+R(x) verifies Y=H x^S exp(B L). The constants of
   C((x^R))[L] are exactly C; the derivative cannot produce a nonzero x^0 residue.
   These facts imply the complete logarithmic filtration and its minimality.
6. The input coefficients contributing to a resonant output are leaves of finite
   positive-exponent words. This establishes polynomial dependence on finite
   critical ancestry, not unconditional computability of that ancestry.
7. Analytic sufficiency uses the induced column-sum matrix norm. Coordinate masks
   are contractive, and the uniform scalar divisor gap bounds the inverse by
   C=sum_{k=0}^{2m-2} (2||N||)^k / eta^(k+1). The fixed-point map is a contraction
   on ||F|| <= 2a when C*a <= 1/8, with contraction factor at most 5/8.
8. Analytic necessity uses a spectral eigenmatrix U with U^2=0 and [A0,U]=rho U.
   Choosing coefficients (rho-gamma_n)/n along gamma_n increasing to rho makes
   the forcing absolutely summable and the normalized gauge a divergent harmonic
   coefficient sum. The universal input class is all positive Gamma-supported
   coefficient series.
9. The explicit p-family is independently verified by the scalar equation
   (D-2)h=a. Subtraction of the x^2 term occurs before summation. The p<=2 case
   must never be split into its two divergent sums.
10. The uniform crossover is a half-line Euler–Maclaurin formula with mesh 1/t.
    Complete monotonicity of f_p bounds the fourth derivative integral by
    |f_p'''(c)|, giving the stated 1/360 remainder constant.

## Assumptions and exclusions

- Real exponents and a positive least input exponent are essential to the finite
  word-depth argument used here.
- Real spectrum is used for the monomials x^lambda in the specified Hahn field.
- The log-degree classification concerns polynomial L over the log-free Hahn
  field, not arbitrary hidden special-function representations.
- Absolute convergence is stronger than having every finite asymptotic prefix.
- Failure of the gap condition need not make every individual input divergent.
- The necessity theorem is not asserted with an arbitrary smaller fixed support E.
- A finite number of formal Picard iterations can still involve infinite series.
- The crossover is a joint N,t truncation statement, not a newly assigned canonical
  coefficient at the accumulation exponent.
- No general irregular/transseries differential-equation classification is claimed.

## Computational checks

Recorded output: verification/results.json.

- 33 exact finite gauge systems.
- 292 exact coefficient checks, including the scalar accumulating example's
  coefficient divisions.
- 36 high-precision crossover cases, all satisfying the proved tail and remainder
  bounds numerically.
- No randomized numerical matrix residuals are substituted for exact arithmetic.
- Numerical results are not outward-rounded interval certificates.
- The verification script does not establish arbitrary infinite-support statements.
- No Lean proof has been supplied or tested for these theorems.

## Novelty and source limits

The ordinary-integer-exponent Fuchsian normal form is classical. The repository
already contains finite-residue-obstruction work; that general philosophy is not
claimed anew. The proposed contribution is the spectral-accumulation universal
analytic criterion and its sharp failure family, joined to the finite-ancestry
formulation and certified truncation crossover.

The literature check was targeted. The article does not assert exhaustive
historical priority or independent peer review. The large canonical TeX volume
could not be fully retrieved through the connector, so absence of overlap with
all of its text has not been proved. The mathematical arguments in the article
are self-contained apart from established Hahn support facts and standard finite
linear algebra and elementary analysis, which are identified in the text.
