# Statement audit

The PDF contains the detailed theorem-by-theorem audit. This file gives the compact artifact-level summary.

## Completed exact/effective developments

| Topic | Status | Where |
|---|---|---|
| Unique real Bring root | Effective with PR modulus | PDF §3 |
| Odd/decreasing/unbounded | Exact + effective | PDF §3 |
| 1-Lipschitz and residual bound | Exact/effective | PDF §3 |
| Fifth-root asymptotic | Effective explicit error | PDF §3 |
| Bring Taylor coefficients | Exact finite truncations | PDF §4 |
| Hypergeometric coefficient identity | Exact + effective tails | PDF §4 |
| Exact radius and four branch points | Effective + exact resultant | PDF §4 |
| Cockle–Harley ODE | Exact rational elimination | PDF §4 |
| General quintic depression | Exact | PDF §5 |
| Principal-form reduction | Exact quadratic certificate | PDF §5 |
| Scaling `x^5+p*x+q` | Exact | PDF §5 |
| Generic Abel–Ruffini obstruction | Fully developed finite argument | PDF §6 |
| `AGL(1,5)` solvability criterion | Exact finite-group theorem | PDF §6 |
| `x^5-x+1` has group `S5` | Exact modular certificates; Galois bridge formalization planned | PDF §6 |
| `x^5+x+3` has group `S5`; `BR(3)` not radical | Same status | PDF §6 |
| de Moivre quintic | Exact cyclotomic identity | PDF §7 |
| MathWorld four-resolvent expansion | Exact cyclotomic identity | PDF §7 |
| Explicit radical/cyclotomic examples | Exact quotient-ring checks | PDF §7 |
| Celestial-mechanics quintic | Exact denominator clearing | PDF §9 |

## Certificate-complete but witness expansion omitted

- Universal quartic Tschirnhaus/Bring–Jerrard transformation: the resultant verifier and soundness theorem are complete; the universal symbolic witness is intentionally not expanded.
- Inversion of the Tschirnhaus map: exact subresultant/gcd certificate interface is complete.
- Brioschi transformation: any proposed parameter witness can be checked exactly.
- Spearman–Williams root formulas: the universal four-resolvent verifier is complete; the page’s long parameter substitution is a generated-certificate target.
- Doyle–McMullen iteration: complete trapping-disk/contraction theorem; no claim about an uncertified random start.

## Formalization outlines, not completed global proofs

- Hermite–Kronecker–Brioschi theta-function formula and its branch choices
- Klein icosahedral global continuation
- full published Runge/Spearman–Williams iff parameter classifications
- the historical classification of exactly five solvable `x^5+a*x^2+b` shapes
- Kondo–Brumer and other parameterized families
- global casus irreducibilis ordered-field tower module
- the exact linear combinations in MathWorld’s chosen all-five-roots hypergeometric basis

## Machine checks

`certificates/verification_report.json` records 17/17 passed check families. The group checker enumerates all 156 subgroups of `S5`, not only conjugacy-class representatives.
