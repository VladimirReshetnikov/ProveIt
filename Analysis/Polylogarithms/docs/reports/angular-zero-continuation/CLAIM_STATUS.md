# Claim status and exact hypotheses

All status claims are relative to ProveIt revision `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`. The report does not assert worldwide priority for the established methods or every consequence.

| Result | Status | Hypotheses and scope |
|---|---|---|
| Level-four rank formulas | Proved analytically | Every integer weight w >= 2, for exactly the coefficient matrix defined in the report. Odd-weight ranks are 5w-6 and (9w-11)/2; both even-weight matrices have full column rank. |
| Explicit kernel and normal form | Proved analytically; implementation checked exactly | Odd integer weights. Rational vector spaces; integer-coordinate witnesses do not imply integral saturation. |
| General-level rank formula | Proved analytically by an S3 character calculation | N >= 3 and integer w >= 2. This is a coefficient-matrix rank, not a period-space dimension. |
| Uniform obstruction for S_(2m) | Proved analytically | Only rational linear combinations of the fixed-weight depth-two product rows specified in the manuscript. Does not exclude all-depth, transformation, or distribution proofs. |
| S4 identity | Proved by analytically justified relations and an exact finite certificate | Integer indices, principal admissible iterated-integral values. 869 rows; 946 formal imaginary coordinates; two independent exact replays. |
| S2 identity and Li3 form | Proved by an exact finite certificate and an inherited Li3 evaluation | 25 rows; 34 formal imaginary coordinates; two independent exact replays. The full small coefficient table is printed. |
| Principal-branch nonvanishing | Proved analytically | Real a >= 1, real b > 0, z in C minus [1,infinity), z != 0. The origin is a double zero. |
| Signed real-order kernel | Proved analytically | Real a >= 1 and b > 0. Fractional integration, direct rescaled monotonicity, exact Mellin moments. |
| Angular existence, uniqueness, simplicity and basic bracket | Proved analytically | Real a >= 1, b > 0, 0 < rho <= 1. The zero lies between arccos(rho) and pi/2. |
| Strict angular order in a, b, rho | Proved analytically | Integer a >= 1, b > 0, 0 < rho <= 1. Outer-order comparison is between successive integers; b and rho derivatives have strict signs. |
| Sixth-root sign theorem | Proved analytically | Integer a >= 2 and b > 0 gives Im F(exp(i*pi/3)) > 0. At a = 1 the sign is the sign of b-1. |
| Endpoint comparisons in b | Proved analytically | Integer a >= 1, every 0 < rho <= 1; includes limiting signed measures with endpoint atoms. |
| Expansion at every finite exponential order | Proved analytically | Real a tends to infinity; uniform for all b > 0 and 0 < rho <= 1, for each fixed cutoff B > 1. No infinite-series convergence claim. |
| All coefficient rows below scale 9 | Exact finite identities | 17 scales, 21 nonzero monomials. Replayed by direct substitution at the requested cutoff. |
| Six reported angular brackets | Exact rational certificates | The specific positive integer parameter pairs and truncations in `zero_brackets.json`; acceptance uses no floating point. |
| Universal Euler constant one | Proved analytically, and uniformly optimal | Real a >= 1, b > 0. Exact rational finite endpoints require positive integer a and b. |
| Small-radius coefficient of normalized angle | Proved analytically | Each fixed real a >= 1, b > 0. The local implicit-function theorem yields the displayed rho-squared coefficient. |
| Normalized-radius monotonicity | Conjectured | Integer a >= 1, b > 0; predicted direction stated in the article. 360 floating-point roots give evidence but no all-parameter proof. |
| Full real-order parameter motion | Open research question | The integer integration proof does not establish all needed fractional-order ratio/log-concavity properties. |
| Independence/minimality/completeness of period bases | Not asserted | Exact matrix ranks do not supply these arithmetic conclusions. |
| Convergence of the full infinite exponential-scale expansion | Not asserted | Every fixed finite order is proved; coefficient growth and infinite summation remain questions. |

## Corrections versus improvements

The two local zero-geometry text mistakes and the logical rank “equivalence” are proposed corrections. The sharper Euler constant, new global zero theorem, angular-order theorems, and all-order expansion are improvements or extensions. The source's restricted S4 obstruction and its distinction between certified proximity and exact equality remain valid.

## Validation boundaries

The exact certificate and rational interval checks use integer and `Fraction` arithmetic. SymPy is used for independent finite matrix checks. mpmath, NumPy, SciPy, and Matplotlib are optional discovery, diagnostic, or rendering tools; their floating outputs do not determine whether either harmonic identity certificate is accepted.

