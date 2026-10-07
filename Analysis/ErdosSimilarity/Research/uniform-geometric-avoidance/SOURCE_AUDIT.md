# Source and proof audit

Audit date: 7 October 2026. This file records the sources actually inspected,
their immutable identifiers where available, and the principal proof checks.
It is an internal mathematical audit, not external peer review or a formal
verification certificate. The new theorems are proved in the article; source
catalogue claims are not treated as axioms.

## Repository revisions

| Repository | Revision used for the source records below |
|---|---|
| [openai/math](https://github.com/openai/math) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` |
| [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt) | `39beb65f2322d6190300fcd23f009f04420b4cb3` |

Initial repository discovery also used default-branch search. The substantive
source records in the tables below were subsequently checked at the displayed
commit identifiers. A search-index revision is not used as a substitute for a
pinned source revision.

## The inherited mathematical construction

The immediate source is OpenAI, *The geometric case of the Erdős similarity
conjecture*, dated 5 October 2026, family 084.

Pinned source directory:

[preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build)

The following paths are relative to that `build` directory. Git blob
identifiers were returned by the repository connector and independently
matched to the inspected source text, allowing for the extra terminal newline
in the local reading copies.

| Source file | Git blob | What was checked |
|---|---|---|
| `main.tex` | `1c63c67a52892a2c8efec1df9b245664b90a9c5b` | Abstract quantifiers; section inputs; theorem numbering. |
| `sections/01-introduction.tex` | `f5b867df4e87772187b0639de90b6a41626331d7` | Theorem 1.1 permits the avoiding set to depend on the fixed ratio. |
| `sections/01-history.tex` | `731d0d8542983eb1d77f467e3301517211eee7aa` | Source manuscript's background and comparison with earlier covering, random-cell, and additive-pattern methods; these historical statements are not hypotheses of the new proof. |
| `sections/02-periodic.tex` | `71ce8995f3ae4704e63c98c2a99081658909e95b` | Normalized periodic hitting target; signed dilation assembly and measure calculation. |
| `sections/03-windows.tex` | `d409f3f9d8d8ace0318b47af74f1ea94e52060e4` | Nested dyadic grids, preorder windows, local span, stability, separation. |
| `sections/04-routing.tex` | `f2b5233fa155e02eff559aadb238c6e881b69041` | Mean density, center exposure, first-default routing, distinct terminal addresses, conditional failure. |
| `sections/05-scales.tex` | `b9697d933e9798792eace89e3ef0f34d52c7e213` | Parameter representative count, order of parameter choices, closed residual centers, open repair. |

The catalogue's `README.md` and `overview.tex` were also inspected. The
catalogue reports 722 manuscripts in 372 families and explicitly distinguishes
verification stages. That report is a description of the source collection,
not a verification of all its results.

The new article reproduces the inherited probability argument, changes the
test-point selection to common scales, and proves the additional uniform
parameter count. Its assembled Section 6 also includes the signed
exponential-polynomial theorem and the positive-root recurrence corollary
described below. No unproved flagship result elsewhere in the catalogue is
needed by these arguments.

## ProveIt material reviewed

Paths are relative to the pinned ProveIt repository root. Formalization and
inventory counts in this table are repository-reported statuses. No ProveIt
Lean or Rocq build was rerun as part of this article.

| Source path | Git blob | Review purpose |
|---|---|---|
| `README.md` | `f5b2c21bf13c14106c2b188e6fee9eb4be60351d` | Repository organization and the distinction between formal results, executable certificates, and exploratory research. |
| `Combinatorics/Ramsey/FORMALIZATION_STATUS.txt` | `3019e17a3e41be96d1adccebf84a9e766a3ad24b` | Reported status of 113 exact companions and seven open items among 120. |
| `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md` | `02f1eb26decc04804b38d00bee586568701ff88e` | Existing local refinement coverage and explicit formalization distinctions; this pinned README lists 59 manuscripts. |
| `SetTheory/Cardinals/docs/reports/README.md` | `89c19b6deee461efd6f36a806d267eb8b6ea6786` | Research-report inventory and status; it describes 247 independent packages as AI-assisted drafts. |
| `SetTheory/Cardinals/docs/reports/log-concavity-and-unimodality/matching-rank-normalization/article.tex` | `c494f89722246638ea39d0bbdaa5adfae5c06b21` | Definitions and selected existing arguments for weighted matching-support polynomials; considered as an alternate research direction and not used in the present proofs. |

The review was selective, with close reading of the sources relevant to the
chosen theorem. It was not an audit of every result in either repository.

## External mathematical sources

| Source | Exact locus used | Role |
|---|---|---|
| Burgin–Goldberg–Keleti–MacMahon–Wang, [arXiv:2210.09284v1](https://arxiv.org/abs/2210.09284v1) | Question 1, first PDF page; Theorem 1.1, second PDF page. | Verifies the published question's simultaneous translation, dilation, and ratio quantifiers, and distinguishes the earlier prescribed-center construction. |
| Basu–Pollack–Roy, [arXiv:math/0603256v3](https://arxiv.org/abs/math/0603256v3) | Section 3.2, equation (3.3), PDF page 5. | A finite bound for components of all realized ternary sign conditions, including zero signs. |
| Perrucci–Roy, [arXiv:1609.02879v2](https://arxiv.org/abs/1609.02879v2) | Effective quantifier elimination over real closed fields. | The decision procedure used in the effectivity section. |
| Jung–Lai–Mooroogen, [arXiv:2412.11062v2](https://arxiv.org/abs/2412.11062v2) | Historical survey. | Context only; no theorem in the article depends on a novelty claim from the survey. |

For the sign-condition input, the finite expression is

\[
\sum_{j=0}^{v}\binom Sj4^j\Delta(2\Delta-1)^{v-1}.
\]

It bounds the number of realized sign vectors by bounding their total number
of connected components. The article uses the weaker consequence
`(8 Δ (S+1))^v`. The degree `Δ` is allowed to grow with the finite prefix:
the fixed-degree asymptotic in the paper's abstract is not used.

## Proof checks in the new article

The following checks were made directly against `sections/01_context.tex`
through `sections/08_limits_and_questions.tex`.

| Proof component | Check and result |
|---|---|
| Common-scale selection | The first level-crossing index gives the strict lower envelope `α Q^j < a_j ≤ Q^j`, has index at most `Tj`, and strictly increases. |
| Periodic keys | Half-open cell conventions, integer wraparound, refinement, and center/test separation are compatible. |
| Preorder windows | The edge/subtree span is at most `2r_h`; the global endpoint is affine in the base length after other parameters are fixed. |
| Center exposure | Only the deterministic center entry in each selector table is exposed; all active entries avoid those addresses. |
| Conditional probability | Further conditioning on all selectors leaves pairwise distinct independent terminal entries. Averaging gives exactly `(1-p/2)^((M-1)r)`. |
| Parameter representatives | The geometric arrangement counts all face dimensions and all singleton ratio strata. Representatives depend only on fixed geometry and the center atom. |
| Constants | The displayed `C(B+1)^4 Q^(-4r)` bound follows from the explicit arrangement count; its dependence on the fixed parameters is recorded. |
| Choice order | Branching, height, gap, and then base length avoid circular dependence. Polynomial growth in the global endpoint is dominated by exponential failure decay. |
| Residual centers | The residual set uses the complete continuous original prefix, not the discontinuous selected terms. Compact projection therefore proves closedness. |
| Global assembly | Only dyadic contractions are used. Each contracted periodic component retains its unit-interval density; summable budgets account for both signs. |
| Infinite omissions | Normalized geometric and positive-mixture tails stay in their respective families; tails reduce the affine scale as needed. |
| Polynomial-family count | Selection polynomials and every relevant grid-boundary polynomial determine all discrete choices, including equalities. There are polynomially many factors in the global prefix and exponential growth only in the local window length. |
| Positive polynomial factors | Tail normalization produces simplex weights, polynomial parameter degree at most `n+1`, and uniform ratio bounds after a sufficiently large tail. |
| Signed exponential polynomials | After equal bases are combined and the leading coefficient of the largest-base polynomial is absorbed into the dilation, the dominant polynomial is monic. On each compact coefficient/base-separation box, the displayed error bound `Rj/n + (m-1)R(k+1)n^k r_*^n` tends uniformly to zero and yields effective positive contraction ratios after an index `N`. |
| Every normalized signed tail | The assembled proof enumerates **all integers `h ≥ N` for every compact box**. For each such `h`, adjoining `u A_h = 1` gives a compact rational semialgebraic family with `f_n = u A_(h+n)`, `f_0 = 1`, and parameter degree at most `h+n+2`. This permits arbitrarily late indices and the scale reduction required by contraction-only periodic assembly. |
| Positive-root recurrences | The corollary concerns real homogeneous linear recurrences with constant coefficients and every characteristic root in `(0,1)`, allowing multiplicities. The article proves the standard solution representation using the shift operator, independence of the sequences `n^k q_i^n`, and the dimension of the solution space; the signed exponential-polynomial theorem then supplies simultaneous avoidance. |
| Effective normalized search | Apply existence with half the requested probability budget; compactness then supplies a finite rational subcover with strict density slack. Quantifier elimination can decide every candidate certificate. |
| Computable measure | Rectangular truncation in the family/contraction indices omits density at most `ε 2^(-N)`, an effective geometric-series tail. |
| Robust certificates | The parameter domain is compact and excludes zero dilation; normalized mixture weights remain in the closed simplex. Finite open covers supply a uniform positive margin, found by quantified rational interval tests. |
| Necessity of parameter control | The density-point annulus construction gives a sequence with consecutive ratios strictly between `1/8` and `1/2`, so ratio bounds alone cannot yield simultaneous avoidance of every such sequence. |

## Included extensions and the novelty boundary

The final Section 6 contains `thm:signed-exp-poly` and `cor:recurrences`;
they are proved results in this package, not reserved research questions.
The signed theorem provides one closed symmetric periodic avoiding set for
all nonzero finite real exponential polynomials with bases in `(0,1)`.
Its countable exhaustion includes coefficient bounds, base intervals,
separation bounds, degrees, component counts, and every sufficiently late
normalization index. The finite-mixture and positive-polynomial-factor
results are included as simpler subclasses. The recurrence consequence
uses precisely the homogeneous constant-coefficient setting described
in the audit table.

The dominant-term estimate and the representation of linear recurrence
solutions are classical elementary ingredients. The new assertion here is
their application to the common uniform avoiding set, together with the
effective countable construction. Novelty is assessed relative to the
inspected fixed-ratio source and the targeted literature review; this audit
does not certify absolute priority. The article correctly distinguishes
the published simultaneous-ratio question from prescribed-center and
almost-everywhere avoidance results. Its revised question on signed
coefficients asks for sharp quantitative behavior near cancellation and
root collision, rather than reopening the existence result proved in
Section 6. Nonreal characteristic roots and unrestricted infinite mixtures
remain outside the proved results.

No material proof gap was found in these audited sections. The accompanying
exact computations test selected finite identities and geometric invariants;
they do not establish the continuum-parameter theorems independently. The
article's claims remain subject to external mathematical review and, if
undertaken, formalization.
