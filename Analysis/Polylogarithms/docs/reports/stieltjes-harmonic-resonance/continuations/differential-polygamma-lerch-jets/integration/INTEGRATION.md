# Proposed ProveIt integration

## Source baseline

Repository: VladimirReshetnikov/ProveIt  
Revision: **f7e35be357654198c1546fd40f363694c5bcc2cc**  
Commit time: **2026-10-11T03:35:18Z**

The source paths are the canonical manuscript in Analysis/Polylogarithms/docs/manuscript and the current docs/incoming reports. The accompanying source_provenance.json identifies exact archive and textual inputs. Integration is proposed here; no remote write was performed.

## Placement and dependencies

| Article material | Suggested location and dependency |
|---|---|
| Sections 2–5: differential-polynomial calculus, convergent words, IBP basis, primitives | The Gamma/polygamma and finite-part development of Volume III, near the existing integration and derivative-contact material. Retain the exact cutoff convention before the new statements. |
| Section 6: Gamma–Appell singular support and explicit sixth/seventh formulas | Immediately after the canonical fifth-moment and scalar Gamma normalization development. The new proofs use the scalar projection bridge and the strict-word conventions. |
| Section 7: odd-lattice Lerch jets and Gamma-weighted polylogarithms | After the continuous-depth report's centered reflection and convolution theorems. The normal Euler continuation should precede computational use of reflected derivatives. |
| Section 8: optimal adjacent-order prefix, fixed-gap reduction, ordinary identities | After the two-tail moment coordinates in the canonical fifth-moment report. Copy the omission convention in the binomial matrix. |
| Section 9 | Update the research-question and status ledger. Preserve the explicit unresolved larger-gap and arithmetic statements. |

The canonical filename layout is evolving. These are mathematical dependency recommendations, not instructions to overwrite a particular chapter. The modular sections are supplied for selective integration.

## Exact source questions and new statements

| Source target | Article labels | Status |
|---|---|---|
| Higher Digamma Powers, further question “Differential polynomials in digamma and polygamma” | poly:ML, poly:filter, poly:bridge, poly:words | General polynomial calculus proved; convergent coordinate construction for every mixed monomial |
| Canonical Fifth Moment, Section 9, all-degree mixed-coordinate classification | poly:IBP, poly:endpointcor | Formal differential quotient solved; arithmetic residue-image classification remains separate |
| Higher Digamma Powers, common-shift question; Canonical Fifth Moment, shifted normalizations and primitives | poly:primitivethm, poly:primitivekernel | Normalized primitive and endpoint subtraction proved; full arithmetic multiple-Hurwitz reduction remains open |
| Higher Digamma Powers, scalar spectral support and explicit sixth/seventh moments | ac:main, ac:sixth, ac:seventh, ac:rawclosed | Highest singular coordinate isolated at every degree; sixth/seventh formulas complete in a named convergent derivative family |
| Continuous Depth Lerch, Q8, “Spectral derivatives on the odd evaluation lattice” | lj:thm:oddjets, lj:thm:Euler, lj:thm:polylog | Resolved in the requested Gamma–Stieltjes–reflected-jet form, with an independent convergent evaluator |
| Canonical Fifth Moment, Conjecture conj:firstq | ar:main, ar:det, ar:complete | Proved for every adjacent even pair p=q−2; arbitrary larger gaps remain conjectural |
| Same conjecture at a fixed even gap | ar:gap-det, ar:gap-factor | Exact reduction to a matrix of size equal to half the gap; nonvanishing is not proved in general |
| Ordinary consequence of the adjacent-order reconstruction | ar:all-rational, ar:46ordinary, ar:46telescoping | Infinite family of rational ordinary series and a separately telescoping (4,6) example |

The exact equation labels for the final example can also be read from the TeX; the claims ledger contains the definitive labels used by this package.

## Statements to retain without promoting their status

- The source scalar Mittag–Leffler theorem, Gamma height-one bridge, centered Lerch reflection, and two-tail coordinate formulas are antecedents. Their necessary normalization inputs are repeated with proofs or source references.
- Lower normalized moments through degree five, ordinary weight-five/six multiple-zeta reductions, Euler's transformation, and the Stieltjes parameter-derivative tower are recovered classical or prior-report inputs.
- The Gamma–Appell theorem removes lower **singular** Laurent coordinates. It does not prove elimination or independence of all convergent mixed derivatives.
- The canonical monomial count and harmonic-tail rank are formal statements. They do not establish arithmetic independence of the evaluated constants.
- The common-shift expansion is a normalization theorem. It does not by itself provide a finite Barnes or multiple-Hurwitz evaluation at arbitrary arguments.
- The Gaussian S6 and revised S8 candidates remain open. The rejected older S8 vector remains distinct. The Gamma–Appell symbols in this article do not refer to those Gaussian ladders.

## Corrections and editorial changes

No new false theorem was found in the portions of the incoming reports that were inspected. The following are updates and precautions for integration, not allegations that the source reports made these errors.

1. Amend conj:firstq to add the proved adjacent-order family and determinant. Leave the larger-gap statement open.
2. Preserve the omitted lower-index-zero binomial summand in the matrix definition; adding it changes the operator and determinant.
3. Retain every finite endpoint constant in integration by parts. The concrete test is \(I(u_1^2+u_0u_2)=-\zeta(3)\), rather than zero.
4. Keep the highest-singular-coordinate statement distinct from complete arithmetic closure.
5. Derive Lerch order derivatives from the holomorphic local germ, not by differentiating a discrete odd-value polynomial. Retain derivatives of the factor \(2^{1-s}\).
6. Do not differentiate an integer-index multiple-zeta duality identity. The directional simplifications here use identities valid on open order domains.

## Notation and reuse

The article uses \(Z(s_1,\ldots,s_d)\) with the largest summation index first. A spectral partial derivative inserts the negative logarithm of that index. The Stieltjes expansion has coefficients \((-1)^j\gamma_j(a)/j!\).

Finite parts use the original coordinate \(x\), cutoff \(x=\varepsilon\), and upper endpoint one. Primitive logarithms use the slit plane \(\mathbb C\setminus(-\infty,0]\). The Lerch depth domain is \(\Re\rho>0\).

There are 168 labeled objects in the final article. No exact label collision was found against canonical manuscript TeX at the pinned revision. Reconcile generic bibliography keys and any later report labels on integration.

The auxiliary verification scripts use no incoming-code imports for the differential and adjacent-tail checks. The Appell suite records its own compiler, independent rational certificate replay, and explicit source-free directional checks. The numerical comparisons use analytically different representations. All such independence is computational and structural; it is not a claim of independent human peer review.
