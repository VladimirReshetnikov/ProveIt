# Status and claim boundaries

Date: 20 September 2026.

## Target

Bishal Deb and Alan D. Sokal, *Higher-order Stirling cycle and subset
triangles: Total positivity, continued fractions and real-rootedness*,
arXiv:2507.18959v1, Conjecture 1.4(d), printed page 10.

The selected target is the r >= 3 negative assertion for **subset** row
polynomials. This is not the subset row-log-concavity assertion in part (c),
and is not the all-order positive assertion for **cycle** polynomials.

## Proved in the article

1. For every integer r >= 3 and every positive shift a, the adjacent 3-by-3
   Hankel determinant has order exactly five at x=0 and a negative leading
   coefficient.
2. An exact partial-binomial-sum formula and an explicit strictly negative
   upper bound hold for this coefficient.
3. At shift one the coefficient has the displayed closed rational
   factorization times binomial(2r−1,r−1)^2.
4. Explicit positive rational intervals exclude Stieltjes and Hamburger
   moment representations of scalar specializations.
5. Exact formulas at r=3,4 and asymptotic formulas at fixed r or fixed shift
   one follow.

The sign proofs use finite counting, determinant-preserving operations,
Pascal's identity, positive-ratio inequalities, and rational polynomial
factorization. They are not extrapolations from computed data.

## Imported or credited

- Definitions and conjecture: Deb and Sokal.
- The proposed shift-one 3-by-3 witness: Deb and Sokal, Appendix C, page 50.
  It was not discovered for the first time here.
- Coefficientwise Hankel positivity at r=1,2: previously known. The r=2
  Ward-polynomial continued fraction is due to Elvey Price and Sokal.
- The full “if and only if r=1,2” classification combines this article's
  negative proof with those known positive cases.
- Central-binomial asymptotics are classical and are not a novelty claim.

## Executed checks

`data/verification.json` records all standard-library checks as passed.
These comprise 270 independent partition counts, 96 complete determinants,
1,120 truncated determinants, 100 first-shift factorizations, and 2,665
finite log-concavity inequalities. The optional SymPy 1.14.0 rational
identity check also passed. The PDF was compiled and visually inspected.

No proof assistant, Lean, Wolfram connector, or external referee was used.
Finite tests and computer algebra are supporting audits, not universal
proof certificates in the formal-verification sense.

## Not claimed

- A verified global priority claim: the source search was finite.
- New discovery of the shift-one witness, or of the low-order positive cases.
- Results about total positivity of the numerical triangle or its row reversal.
- Results about row log-concavity or the cycle-polynomial conjectures.
- A minimum possible size of a negative-coefficient Hankel minor.
- A formula for the shift-zero determinant from the rank-one argument.
- Failure of scalar moment representations at every positive x, or a uniform
  x-interval independent of r and a.
- Independent refereeing or formal proof-assistant verification.

## Relation to the supplied manifest

The manifest was read in full to avoid duplication. Its corresponding
entry treats Conjecture 1.4(c). We inspected the manifest's description, not
the underlying report. Its proof claims are neither needed nor re-certified.
The original manifest is included unchanged solely as the selection record.
