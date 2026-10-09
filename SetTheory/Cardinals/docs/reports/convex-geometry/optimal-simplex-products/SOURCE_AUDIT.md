# Source, novelty, and verification audit

Audit date: 8 October 2026 UTC.

This file records the source snapshots used for the two manuscripts, the
boundary between inherited results and the present contributions, and what
the accompanying verification programs establish. It is an internal research
audit. Neither an external peer review nor a proof-assistant certification is
represented as having occurred.

The papers are independent. The recurrence-avoidance article does not use the
simplex-product article, and the simplex-product article does not use the
recurrence-avoidance article.

## 1. Repository snapshots

| Repository | Snapshot used for this delivery | Retrieval |
|---|---|---|
| [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a) | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` | Inspected on 8 October 2026; the recorded repository commit is dated 6 October 2026. |
| [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/58175ca45563d9ee29875374dd77942f069268a9) | `58175ca45563d9ee29875374dd77942f069268a9` | Snapshot fetched on 8 October 2026 at approximately 03:30 UTC. |

The predecessor report's own `SOURCE_AUDIT.md`, dated 7 October 2026,
records ProveIt revision `39beb65f2322d6190300fcd23f009f04420b4cb3`.
That older revision belongs to the predecessor's audit history. It is not the
ProveIt snapshot used for the current delivery. The predecessor was read at
the current `58175ca...` snapshot listed above.

Repository and catalogue descriptions were used to locate relevant work and
understand integration conventions. They are not mathematical axioms, and
this review does not validate the entire collection in either repository.
Initial discovery included default-branch browsing; substantive comparisons
refer to the recorded revisions and inspected source content below.

## 2. Immediate sources for recurrence avoidance

### 2.1. OpenAI geometric manuscript

The inherited fixed-ratio construction is OpenAI, **The geometric case of the
Erdős similarity conjecture**, dated 5 October 2026, family 084.

Pinned source directory:

[preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build)

The current review directly consulted the routing and scale arguments as well
as the predecessor's fuller source comparison. Paths in this table are
relative to the displayed `build` directory.

| Directly inspected source | Git blob | Role |
|---|---|---|
| `sections/04-routing.tex` | `f2b5233fa155e02eff559aadb238c6e881b69041` | Selector exposure, first-default routing, distinct terminal keys, and the conditional failure calculation. |
| `sections/05-scales.tex` | `b9697d933e9798792eace89e3ef0f34d52c7e213` | Parameter representatives, noncircular choice of constants, compact residual centers, and open repair. |

The source theorem allows the avoiding set to depend on a fixed geometric
ratio. The present article does not claim that theorem as new. Its relevant
finite routing ingredients are restated and proved in the recurrence article,
with the signed boundary conventions needed for oscillatory scalar terms.

### 2.2. ProveIt predecessor

The immediate predecessor is **Uniform avoidance of geometric progressions
and exponential-polynomial patterns**, dated 7 October 2026. Its title page
says that it was prepared for Vladimir Reshetnikov, with mathematical
development and exposition with ChatGPT. It is cited as a repository research
manuscript, without assuming conventional sole authorship or external
publication status.

Pinned report directory:

[Analysis/ErdosSimilarity/Research/uniform-geometric-avoidance](https://github.com/VladimirReshetnikov/ProveIt/tree/58175ca45563d9ee29875374dd77942f069268a9/Analysis/ErdosSimilarity/Research/uniform-geometric-avoidance)

Paths below are relative to this report directory. The main source filename
is `uniform_geometric_avoidance.tex`.

| Inspected source | Git blob | Role in the comparison |
|---|---|---|
| `uniform_geometric_avoidance.tex` | `2abf6db8b813920c911424adac278c7aa7603ced` | Title, scope, assembled inputs, and bibliographic attribution. |
| `SOURCE_AUDIT.md` | `9f9701b8b84c39d4f728d412bd5cdab46913c015` | Earlier source records, inherited proof checks, and the explicit previous novelty boundary. |
| `sections/02_synchronization.tex` | `21ed867f1bf9a94797f1c7d5752204bae3609636` | Common-scale first-passage selection for contracting positive scalar terms. |
| `sections/03_routing.tex` | `e236813e3db249415da856b23baa8fcb55d5eb9b` | Finite windows and ordered routing. |
| `sections/04_uniformity.tex` | `653b1057ae05141ceabc5edd4986bba434cbd110` | Uniform address complexity, representatives, and residual repair. |
| `sections/05_global.tex` | `6c69130a8fd2e96dae8f83209ea1d87fcb3d4e4d` | Countable assembly, dyadic contraction, measure budgets, and tail arguments. |
| `sections/06_algebraic_families.tex` | `ba16f7690bb25bbf6dd1d4636699982d52b4d350` | Already proved signed exponential polynomials with positive bases and positive-root recurrence consequences. |
| `sections/07_effectivity.tex` | `ea510a05d3f2a5eee9c128c16b5761224ab80994` | Rational finite blockers, positive margins, and computable measure. |
| `sections/08_limits_and_questions.tex` | `260b4566c59edde321d66d801cfade46b9db7e65` | Restrictions of the earlier result and proposed extensions. |

The predecessor already covers signed finite exponential polynomials whose
bases lie in `(0,1)`, and the corresponding positive-root recurrences. Those
results are not reclassified here as new. In particular, merely allowing
negative coefficients in such positive-base sums would not supply the
extension claimed by the present paper.

The new mechanism selects a first passage of a quadratic norm of a block of
consecutive recurrence states, then selects an actual original scalar term
from that block. It permits negative and nonreal roots, repeated roots,
spectral collisions, cancellation, and infinitely many zero terms. Compact
families use rational semialgebraic constraints on the state transition and
Lyapunov metric. This replaces the positive scalar-ratio hypothesis that
restricted the predecessor.

## 3. Immediate source for simplex products

The geometric source is OpenAI, **A product counterexample to the simplex
maximum for projection-body volume**, dated 24 September 2026.

Pinned source:

[preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex)

The inspected source has Git blob
`c32187535cddb5c38f28d332997dc0578cbad586`. The original retrieval record is
preserved in
`simplex_products/verification/source_provenance.json`; its discovery URL
uses `main`, while the immutable repository snapshot is supplied above.

The source establishes the normalized projection-body volume of a simplex,
the product identity, a dimension-20 product counterexample, and an
exponential improvement obtained by repeating fixed factors. The companion
re-proves the needed geometric identities with attribution. It does not claim
the first disproof of the unrestricted simplex-maximum conjecture: the source
itself cites the earlier counterexamples of Feng, Hu, Liu, and Xu.

The companion's contribution is the exact optimization within the class of
affine images of products of simplices: the unique rate-maximizing block
dimension 13, the two-candidate formula in every dimension, the eventual
residue rule with minimal threshold 100, the sharp uniform gap between the
optimal dimension multiset and every other multiset, and the exact periodic
asymptotic correction. It also gives the fixed-factor-count and facet-count
optimization.

The uniqueness and gap concern factor-dimension multisets, equivalently the
corresponding affine product classes. All nondegenerate simplices in the same
dimension are affinely equivalent. The article supplies no uniqueness claim
among arbitrary convex bodies and no geometric stability theorem for
perturbations that leave the product class.

## 4. External mathematical references

The articles contain their own bibliographies. The table records the role of
the primary references and separates mathematical dependencies from context.

| Reference | Locus or identifier | Role |
|---|---|---|
| S. Basu, R. Pollack, and M.-F. Roy, *An asymptotically tight bound on the number of semi-algebraically connected components of realizable sign conditions* | [arXiv:math/0603256v3](https://arxiv.org/abs/math/0603256v3), Section 3.2, equation (3.3) | External input bounding all realized polynomial sign conditions, including zeros. The finite expression, with degree allowed to grow with prefix length, is used rather than a fixed-degree asymptotic. |
| D. Perrucci and M.-F. Roy, *Elementary recursive quantifier elimination based on Thom encoding and sign determination* | [arXiv:1609.02879v2](https://arxiv.org/abs/1609.02879v2), 2017 | Effective real quantifier elimination used to decide a proposed finite rational blocker certificate. |
| A. Burgin, S. Goldberg, T. Keleti, C. MacMahon, and X. Wang, *Large sets avoiding infinite arithmetic / geometric progressions* | [arXiv:2210.09284](https://arxiv.org/abs/2210.09284); [DOI 10.14321/realanalexch.48.2.1668676378](https://doi.org/10.14321/realanalexch.48.2.1668676378) | Context for the simultaneous geometric-ratio question and the difference between prescribed-center and full affine quantifiers. |
| M. N. Kolountzakis and E. Papageorgiou, *Large sets containing no copies of a given infinite sequence* | [arXiv:2208.02637](https://arxiv.org/abs/2208.02637); *Analysis & PDE* 18 (2025), 93–108 | Related avoidance work on discrete unbounded sequences; it is not used as a theorem about all contracting recurrences. |
| Y. Jung, C.-K. Lai, and Y. Mooroogen, *Fifty years of the Erdős similarity conjecture* | [arXiv:2412.11062v2](https://arxiv.org/abs/2412.11062v2), 2025 | Historical survey and context; not a proof dependency. |
| N. Mora Cuellar, A. Iosevich, N. Kulkarni, I. Rojas Aravena, and A. Yavicoli, *The Erdős Similarity Conjecture for Two-Fold Sumsets with a Geometric Summand* | [arXiv:2607.03584v2](https://arxiv.org/abs/2607.03584v2), 2026 | Contextual related work; not a dependency of the recurrence theorem. |
| Feng, Hu, Liu, and Xu, *On the Reverse Projection Inequality* | [Zenodo record 22037130](https://zenodo.org/records/22037130); [DOI 10.5281/zenodo.22037130](https://doi.org/10.5281/zenodo.22037130), 21 August 2026 | Earlier counterexamples to the unrestricted simplex-maximum conjecture, acknowledged in the inspected product source. |
| N. S. Brannen, *Volumes of projection bodies* | *Mathematika* 43 (1996), no. 2, 255–264; [DOI 10.1112/S002557930001175X](https://doi.org/10.1112/S002557930001175X) | Historical conjecture and context. Bibliographic details follow the inspected source; the companion does not depend on accepting that conjecture. |
| NIST Digital Library of Mathematical Functions | [Section 5.11](https://dlmf.nist.gov/5.11) | Classical Stirling expansion and remainder control used in the companion's asymptotic formula. |

The stable-tail representation, Lyapunov estimates, simplex facet calculation,
and discrete concavity arguments are proved in the manuscripts. Their
elementary ingredients are not presented as new general linear algebra or
convex geometry.

## 5. Novelty assessment and scope

### Recurrence article

The main new extension relative to the inspected sources is a **single**
closed symmetric one-periodic set, of arbitrarily high unit-interval measure,
that omits infinitely many points from every nontrivial affine copy of every
convergent, non-eventually-constant real C-finite sequence. The same set covers
rational observations of finitely many such convergent sequences when the
limiting denominator is nonzero. The basic theorem is stated for a decaying
C-finite numerator that is not eventually zero and a C-finite denominator
with nonzero limit.

The order of the quantifiers matters: the set is chosen before the sequence,
its recurrence coefficients, the translation, and the nonzero dilation.
No countability restriction is placed on those real coefficients. The proof
uses a countable exhaustion by compact families, each of which contains a
continuum of parameters.

Effectivity for rational density loss is a proved existence-and-termination
statement: enumerate rational finite open-arc candidates and decide their
uniform hitting property and positive margin by quantifier elimination.
It is **not** an implemented algorithm in this delivery. Neither the full
search nor the random routing tree has been executed, and no practical
complexity bound is claimed.

The result does not assert simultaneous avoidance for all infinite
subsets of the line, all variable-coefficient recurrences, all analytic
observations, or quotients with arbitrary vanishing limiting denominators.
It is not a solution of the full Erdős similarity conjecture. The
positive-measure obstruction for the unrestricted class of perturbations
`q^n + o(q^n)` is an elementary limitation proved in the article, not a
priority claim for that density-point argument.

### Simplex-product article

The exact optimization results sharpen the inspected product counterexample.
They concern a specific geometrically natural product class. The value
`s_13^(1/13)` is the optimal rate for simplex factors, not an asserted optimum
over all convex bodies or over arbitrary factor families.

### Limits of the literature review

Targeted searches of primary research sources and inspection of the immediate
repository predecessors did not locate the stated full recurrence extension
or the specific dimension-13 optimization classification. This supports
describing them as proposed new results relative to the inspected literature.
It cannot certify absolute priority, rule out equivalent formulations under
different terminology, or replace expert mathematical review. No claim of a
globally established breakthrough is made by this audit.

## 6. Proof review and executable evidence

The mathematical arguments were reviewed separately from their initial
construction during preparation of this package. This was an internal review,
including a separately written exact dynamic program for the companion; it
was not an external peer-review process. The reviewed written proofs had no
identified material gap at delivery. That status is a report of the review,
not a substitute for the proofs or a guarantee that further review cannot
find an error.

For the recurrence article, the review explicitly checked the following
interfaces: stable reduction after nilpotent transients; common denominator
and numerator contraction constraints; selection of an original scalar term
at the shifted index; increasing selected indices; negative displacements at
old grid boundaries; zero signs and ties; exposure of center entries before
choosing representatives; distinct terminal keys in the conditional
probability calculation; compact residual projection from the original
continuous prefix; tail closure; and the final two-sign measure budget.
The effective finite-cover and quantifier-elimination argument was reviewed
as a mathematical proof.

For the companion, the review checked affine covariance and the product
identity, the simplex value, the equality `q_1=q_2=3` before strict decrease of
the consecutive ratios, the unique rate peak, all-dimensional balancing,
deficit comparisons, the residue threshold, the sharp isolation gap, and the
Stirling coefficients and remainder. Dimension 99 supplies the obstruction
showing that the uniform eventual threshold 100 cannot be lowered.

The executable evidence has the following finite scope.

| Program | What is checked | Recorded extent |
|---|---|---|
| `recurrence_avoidance/verification/verify_recurrence.py` | Exact quadratic inequalities, explicit scalar formulas, denominator normalization, original-term selection, sign clearing including zeros, first-passage equalities, ties, prefix bounds, and signed annular separation. | Three explicit oscillatory or repeated-root examples; 3,380 exact assertions, including 16 actual threshold-equality witnesses. |
| `simplex_products/verification/verify.py` | Factorial values, seven strict rational interval certificates with positive integer cross-multiplication margins, printed prime-power identities, eight initial comparisons, and an exact unrestricted dimension-partition dynamic program. | All dimensions 1 through 300; agreement with the two-candidate formula and every attainable eventual residue formula; sharp-gap examples. |
| `simplex_products/verification/independent_audit.py` | A separate construction of the simplex values from consecutive ratios, retaining the two highest distinct exact values and all associated multisets. | All dimensions through 260; exact optimum and uniqueness, the isolation bound from 100, and equality at dimensions `112 + 13j` within that range. |

All decisions in these programs use integer or rational arithmetic. Decimal
displays and floating-point figure rendering have no role in the certificate
inequalities. The assertion counts and finite dimension ranges describe
what was run; they do not establish unbounded or continuum-parameter
statements by extrapolation.

The recurrence proof depends on the finite sign-condition theorem,
conditional probability, compactness, and countable measure estimates. Its
verifier does not implement those continuum arguments. The companion's
all-dimensional proof depends on concavity and deficit bounds, while its
finite exact inequalities are certified by the integer margins. The dynamic
programs provide independent cross-checks of the formulas and implementation
on their stated finite ranges.

The package contains ordinary mathematical proofs and executable arithmetic,
not a Lean, Rocq, Isabelle, or other proof-assistant development. No existing
ProveIt formalization build was rerun or altered as part of these manuscripts.

## 7. Reproduction and integration status

The top-level [README.md](README.md) gives the exact build and verification
commands. [Makefile](Makefile) builds both PDFs and reproduces the exact
records in a separate output directory before comparing them with the
delivered evidence. Its `clean` target removes only generated TeX auxiliary
files for the two article job names.

The manuscripts include their complete sources, referenced figures and
figure-generation code where applicable, verifiers, and recorded outputs.
The external source manuscripts themselves are cited and content-pinned;
the delivery does not depend on bundling copies of those third-party works.
Reproducing the included finite checks requires no network access.

Repository destinations in the README are proposals for intake. No repository
push, merge, catalogue update, or replacement of the predecessor has been
performed by this delivery. A maintainer should apply the repository's
current intake conventions, preserve attribution and the source comparison,
and maintain the shared preamble dependency when placing the papers.
