# Research audit

Manuscript date: 22 September 2026. Builds may have a 23 September UTC timestamp.

## Repository version and actual scope

Repository: VladimirReshetnikov/Surreal.
Pinned commit: `465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`.

The repository tree, root README, documentation catalogue, docs/new directory,
and the research audit of docs/surreal/transcendence-over-bounded-support were
retrieved through the GitHub connector. The documentation catalogue describes
44 reports. This was not a line-by-line audit of all reports, old versions,
code, or Lean declarations. The linked docs/new listing at that revision was
not treated as evidence of an additional unseen collection of articles.

The closest bounded-support report explicitly works with supports bounded in
exponent order and their fraction field. This manuscript uses all supports
of cardinality less than kappa, an already-real-closed or algebraically closed
field. It does not claim a new version of that report's independence theorem.
The foundations and Hahn-vector-space topics were compared at their stated
catalogue/overview scope, not advertised as independently verified proofs.

An indexed search for “spherical” returned no matches, despite related
catalogue topics. That negative result was not treated as exhaustive evidence
of absence. The novelty comparison relies on actual retrieved descriptions.

No repository content was modified. No Lean build was performed.

## Literature inspected and background cited

1. S. Kuhlmann and S. Shelah, kappa-bounded Exponential-Logarithmic Power Series
   Fields, arXiv:math/0512220v1. Relevant HTML definitions/background were read.
   The paper fixes a regular uncountable cardinal. The bounded-field construction
   is credited, not claimed as new.

2. A. Berarducci, S. Kuhlmann, V. Mantova, and M. Matusinski, Exponential fields
   and Conway's omega-map, arXiv:1810.03029v2; Proc. AMS 151 (2023), 2655–2669,
   DOI 10.1090/proc/14577. Relevant bounded-field context and metadata were checked.

3. F.-V. Kuhlmann, Approximation types describing extensions of valuations to
   rational function fields, arXiv:2111.10529v1. The abstract, valuation/ball
   framework, and Section 4.2 were inspected. PDF pages 1, 35, and 36 were viewed.
   Proposition 4.4 already expresses approximation types using ball formulas.
   Neither those formulas nor the general approximation-type framework are new
   claims of this manuscript. The precise cardinal-prefix and arbitrary-formula
   omission calculations are proved here in the specific bounded-support setting.

4. B. Poonen, Maximally complete fields, L'Enseignement Mathématique 39 (1993),
   87–106. Lemma 4 and Corollary 4 were inspected, including PDF images of printed
   pages 95 and 96. Full-Hahn ball gluing, completeness, and algebraic closedness
   are credited as classical. The cardinal bound on the glued support is the
   additional calculation used here.

5. Y. Yin, Quantifier elimination and minimality conditions in algebraically
   closed valued fields, arXiv:1006.1393v1. The introduction and bibliography
   were inspected, including PDF images. Robinson's classical one-sorted
   divisibility-language quantifier elimination is distinguished from Yin's
   richer-language results. Robinson's Complete Theories (1956) is cited as
   historical background, not represented as a freshly audited complete book.

6. A. Tarski, A Decision Method for Elementary Algebra and Geometry, RAND R-109
   (1951). The publisher's landing page was checked. RCF quantifier elimination
   is a standard mathematical input; this task did not reread the entire report.

7. H. Gonshor, An Introduction to the Theory of Surreal Numbers (1986), is the
   classical normal-form reference. The entire book was not freshly audited.

Article references provide the source URLs. No third-party papers or font
files are redistributed in this archive.

## Novelty assessment

The priority search was targeted, not exhaustive. Several broad web queries
returned irrelevant results; those do not support an absence claim. No full
MathSciNet/zbMATH search, citation-network audit, or review of every unpublished
manuscript was performed.

The warranted status is: a theorem package with supplied written proofs,
proposed as a contribution not identified in the reviewed material. Expert
review may identify prior equivalents or a simpler general formulation.
The manuscript does not claim to solve a named longstanding conjecture.

## Proof-risk review

- Kappa is uncountable; the finite-support case is expressly excluded.
- Algebraic closedness at singular kappa is proved using one small rational
  exponent span for finitely many coefficients, not an invalid unbounded union.
- The type invariant is the entire first-kappa coefficient prefix, not merely
  the cofinality or cut of the support.
- The lower omission bound applies to arbitrary formulas via eventual agreement
  and quantifier elimination. It is not merely a bound for chosen ball formulas.
- Real inequalities recover coefficients below a threshold; a later cofinal
  threshold is used to recover the coefficient at a fixed support position.
- Only types realized in the fixed full Hahn extension are classified; no claim
  of full saturation or of automorphism homogeneity of that field is made.
- Ball gluing verifies well-ordering of the support as well as its cardinality.
- Cauchy and pseudo-Cauchy families are not conflated. Completion uses all
  valuation scales in the given group.
- The completion adds only cofinal supports of order type exactly kappa.
  Bounded supports of cardinality kappa are not added.
- The group Gamma_kappa has all bounded intervals of cardinality less than kappa;
  therefore its support-restricted field has the full Hahn field as completion.
  A separate group Gamma_kappa plus a dominating rational coordinate supplies
  the strict intermediate-completion example.
- Retraction continuity is shown equivalent to a uniform group-valued loss bound
  by an explicit monomial scaling argument; no real-valued norm is presumed.
- The zero continuous dual is an assertion over an incomplete base, in the
  specified inherited valuation topology, not a contradiction of finite-dimensional
  real/complex functional analysis.
- The Conway realization has the sign t^gamma -> omega^(-j(gamma)).
- No proper-class field is used as a first-order parameter structure.

## Computational and layout evidence

The delivered exact-rational Python run passed 9,622 assertions. These test
finite first-disagreement, product, tail-invariance, ball-agreement, and
retraction-trichotomy mechanisms. They do not verify the transfinite theorems,
quantifier elimination, novelty, or any Lean implementation.

The final PDF was built with pdfLaTeX, shell escape disabled, with repeated
passes to resolve references. Pages were rendered for visual inspection, and
text bounding boxes and the final LaTeX log were checked separately. The final
page count and log/layout results are recorded in build_audit.json.
