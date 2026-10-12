# Proposed research-status updates

Source snapshot: `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.
These are proposed changes for integration. The repository has not been edited.

## Alternating Tails and Higher Spectral Defects

Source archive: `docs/incoming/ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11.zip`.

| Source question | Proposed status | Article labels |
| --- | --- | --- |
| Q1, two remaining moment progressions | Order ten is now complete for every b >= 6. Order eight was already completed in the quartic incoming report. Retain neither progression as open. | `ten:main`, `ten:B17`, `ten:congruence`, `ten:range` |
| Q2, full gap-six family | Remains open uniformly in the smaller order. Fixed cases covered by earlier work and this order-ten theorem do not prove the family. | `future:sec` |
| Q3, all unequal even orders | Complete when the smaller order is at most ten; the unrestricted theorem remains open. | `ten:main` |
| Q4, bilinear adjacent-tail certificates | Resolved for the stated two-adjacent-product rational ansatz. Exact condition: P/Q = c S(x) S(x-1), with outer color +/-1. | `rat:classification`, `rat:root-orbits`, `rat:kernels` |
| Q5, continuation of the ordinary square law | Resolved, including all nonpositive-order contacts and spectral derivatives, with explicit cutoff translation. | `cut:normal`, `cut:contacts`, `cut:translation` |
| Q6, independent shifts and orders | New alternating counterpart with Gamma-determined weights. Retain the original ordinary-Hurwitz product with independent outer order and full moving-pole catalogue as open. | `bil:master`, `bil:stieltjes-all` |
| Q7, complementary cyclotomic sector | Keep the full generator question. Mark the first coefficient as already implied by proved manuscript reductions. | `audit:coefficient` |

### Exact Q7 cross-reference to add

With `lambda_3 = Im Li_3((1+i)/2)` and the source convention
`Z(2,1;i,-i) = sum_{k>m>=1} i^k (-i)^m/(k^2 m)`,

```tex
\Im Z(2,1;i,-i)
 =\lambda_3-\frac{\pi\log^2 2}{32}-\frac{\pi^3}{128}.
```

This follows from:

- `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`,
  `inverse:eq:mixedb1`, and its integral `inverse:eq:mixedintegral`;
- `chapters/04-shuffle-parity.tex`, subsection
  `gaussian:subsec:gaussian-triples`, based on
  `gaussian:eq:height-one-general`.

Retain the source's credit for the classical height-one trilogarithm
reduction. Do not claim a further reduction or independence of `lambda_3`.
This is a correction to research status, not a discovered false theorem.

## Finite Difference Determinants

Source archive: `docs/incoming/ProveIt_Finite_Difference_Determinants_2026-10-11.zip`.

The second topic in `sections/09-questions.tex`, “When does determinant
degree equal harmonic rank?”, now has a complete answer for nonzero real
rational weights over the rational cutoff field. The degree equals the
generic pencil rank. At numerical cutoffs, an exact compression criterion
finds the finite exceptional set; signed examples can be deficient. Preserve
this distinction when importing `deg:main`, `deg:rational`, and
`deg:exception-certificate`.

The original rank-one spectral stencil extends to every rank rho by
`h=2r-rho-1`. The new family has exact pole orders rho-m+1 at m=1,...,rho,
with explicit leading Laurent coefficients and a Gamma product at m=1.
Import `hier:closure`, `hier:rank`, `hier:poles`, and `hier:Gamma-product`
as a structured extension. This does not classify all higher-rank harmonic
pencils or solve the general overlapping Gauss-ensemble resonances.

## Qualifications to preserve verbatim in meaning

1. A cutoff finite part specifies its coordinate. Natural-cutoff odd contacts
   vanish, but an arbitrary translation introduces odd-order contacts.
2. Formal rank and degree do not establish arithmetic independence or minimal
   polylogarithmic depth under functional equations.
3. Real rational weights may have conjugate nonreal poles; the real theorem
   allows them after a real/imaginary coordinate change. It does not extend by
   assertion to arbitrary complex rational weights.
4. Exact spectral pole orders are proved for a > 0. The leading-coefficient
   identity continues holomorphically to Re(a) > 0, where special complex
   parameters could make that coefficient vanish.
5. The Gamma quotient, alternating-Hurwitz recurrence, Euler specialization,
   and asymptotic expansion are classical inputs. The order-ten source
   determinant and real-variable threshold method are inherited inputs.

The project’s Gaussian S6 and revised S8 statements remain conjectural in
this contribution. No new error in the proved core manuscript is asserted.
