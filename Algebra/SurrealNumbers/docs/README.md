# The surreal and surcomplex reports

This collection has **69 research reports in five families**. Start with the
reading routes below, use the [notation guide](NOTATION.md) when moving between
reports, and consult the [typeset catalogue](manifest.pdf)
([source](manifest.tex)) for longer descriptions. The
[formalization ledger](FORMALIZATION.md) lists the main sources and maps exact
claims to checked Lean declarations. The [exposition review record](REVIEW.md)
identifies corrected portions and the scope still to review.

These are AI-assisted research drafts. A report's mathematical argument,
finite verification programs, and Lean coverage are separate forms of evidence.
Some statements and prerequisites now have checked Lean proofs; no complete
formal verification of the collection is claimed. Each report records its
hypotheses, limitations and provenance.

## Newest reports

Batches 96 and 97 (4 and 5 October 2026) add no report and extend two.
[Polish models of omnific arithmetic](foundations-and-computation/polish-models-of-omnific-arithmetic/)
grew from twenty to twenty-four manuscripts: Parts XVIII–XXI from batch 96
(placed in `54ece48ab`, written in `20262718e`: a divisibility threshold
for Borel conjugacy of derivations, with explicit normal forms and analytic
flows; the exact Borel level and Wadge degrees of well-ordered supports and
strong summation; a local-finiteness criterion for Borel flows and their
failure of Lie closure in infinite rational rank; simultaneous normal forms
of two derivations and finite-dimensional Lie algebras). Each Part is
followed by a merge section; one of them classifies the Borel actions of
connected Lie groups, and one shows a remark of the flow manuscript false
as stated in finite rational rank. [Surreal well-orders](foundations-and-computation/surreal-well-orders/)
grew from twenty-three to twenty-eight manuscripts: Part XVI from batch 96
(`111c38012`, `62b16914e`: four independent answers on definable class
well-orders beyond `Ord`, merged with the choice-free one as base; strong
comparability, canonical histories and a fixed-point principle equivalent
over GB without choice, the hereditary term order, and definability
ceilings at `V_κ`) and Part XVII from batch 97 (`6571ee1af`, `a21a42d8c`:
a fifth answer that arrived after that merge, printed whole: finite-support
arithmetic, a choice-free transfer theorem and definability horizons over
transitive models). Reciprocal notes are in `90b2d40e6` (in
`birthday-cutoffs-and-hereditary-sets`, `surcomplex-field-automorphisms`,
`omnific-preserving-automorphisms`, `hahn-evaluation-at-omega` and
`foundations`, and in the README of `Algebra/BakerCampbellHausdorff`) and
`c04452509` (`foundations`). The Hilbert's-tenth research tree reviewed all
nine archives before or at placement and the three publications within
stated scopes (`9280aa6d4`, `ec4b972db`, `65969409c`), correcting editorial,
metadata and guide statements and adding empty-domain hypotheses in Part
XVI while retaining the earlier text; the Part XVII write also repaired
four statements of Part XVI after an independent check. Batch 96's hat,
atom-action and commuting-injection manuscripts went to the research-report
collection (`measurable-box-games`, `naming-elementary-embeddings`), and
batch 97's other six to that collection (`a279619-level-seven-gamma-constant`,
`a189281-path-forest-expansions`) and to the Fabius drafts tree. None of
the new material is formalized or indexed in the formalization ledger;
Part XXI's affine BCH identity is, in matrix form, a Lean theorem of the
BCH project, which reaches its action only through an unformalized
homomorphism.

Batches 91 to 95 (4 October 2026) add no report and extend three.
[Polish models of omnific arithmetic](foundations-and-computation/polish-models-of-omnific-arithmetic/)
grew from fifteen to twenty manuscripts: Parts XIII–XV from batch 92
(placed in `e24ce2ce0`, written in `4af6f191d`: Borel Presburger orders in
one real dimension, with a classification of every uncountable locally
compact Polish Presburger model with continuous partial subtraction; the
exponent-group threshold; rational rank and self-embeddings of Levi-Civita
fields, with a counterexample showing Lemma 4.2.4 of a Kuhlmann–Serra
preprint false as stated) and Parts XVI–XVII from batch 93 (`5e4d8eed8`,
`9a8894d0a`, Lean-scope correction `b8bc36acc`: Borel orders on separable
Hilbert spaces, and Borel summability and derivations of left-finite
series fields). [Definable surreals and omnific integers](foundations-and-computation/definable-surreals-and-omnific-integers/)
gained Parts II–III from batch 93 (`47a77daba`, `c7d65e30b`: real
parameters, countable assembly, independent of ZFC, and the strong
`R`-and-`Ord` fixed field, merged from two independent manuscripts;
definable operations, absoluteness without a same-reals hypothesis and a
parameter-free interpretation of set theory in `(No, +, ·, <, Oz, Ω)`).
[Birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)
gained Part IX from batch 95 (`350b9a954`, `abba38172`: surreal-only and
omnific foundations bi-interpretable with ZFC, and the boundary at NBG,
merged from two independent manuscripts). Reciprocal notes are in
`9bffd43d5`, `c70ced0dd` and `ddb36da6c`. The Hilbert's-tenth research tree reviewed the
publications (`c3da7b57a`, `0bb0baf45`, `341c9f187`) and the reciprocal
notes of batch 92 (`fa3ead76f`), correcting guide wording and restoring
omitted hypotheses while retaining the earlier text. Batch 91 brought
nothing here; batch 92's box and hat manuscripts and batch 93's
commuting-action manuscript went to the research-report collection
(`measurable-box-games`, `naming-elementary-embeddings`), and batch 94 and
two of batch 95's archives to `Analysis/Transseries`. Apart from two
statements that coincide with theorems the Lean library already proves
(the fraction-field fact of the birthday-cutoff report's Part IX, and the
`Γ = Z` image clause of a corollary of the Polish report's Part XVII, over
fields of characteristic zero), none of the new material is formalized or
indexed in the formalization ledger yet.

Batches 87 to 90 (3 and 4 October 2026) add one report and extend four.
Batch 90 (placed in `12076b2e8`, written in `6f5f9954c`) adds
[a Cantor space of surreal subfields](foundations-and-computation/cantor-families-of-surreal-subfields/),
from one manuscript: the countable real closed subfields generated by
explicit monomials over the real algebraic numbers form a closed Cantor
family inside one countable surreal field, with unique finite supports,
Borel-complete isomorphism, an analytic-complete fixed-source embedding
locus and complete analytic embeddability (the unrestricted theorem for
countable real closed fields is Calderoni–Marker–Motto Ros–Shani's), an
openness threshold at finite transcendence degree and two generic regimes.
[Polish models of omnific arithmetic](foundations-and-computation/polish-models-of-omnific-arithmetic/)
grew from seven to fifteen manuscripts: Parts VI–IX from batch 87 (placed
in `d151b39ca`, written in `83926d574`: Baire-category rigidity of
discretely ordered rings, nonsplit Polish Presburger models, a **claimed,
not independently reviewed** ATR₀ answer to Glazer's Question 1, and
locally compact cones), Part X from batch 89 (`23adb85f9`, `c9bc70d8f`:
elementary embeddings and Polish submodels of lexicographic models) and
Parts XI–XII from batch 90 (`12076b2e8`, `dd26f917c`: local geometric
codes, and a criterion for Polish group completions that answers the
report's group-completion question, with Glazer's question on class
manifolds). [Birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)
gained Parts VI–VII from batch 89 (`e3e58a882`: Replacement-free cuts and
Collection spectra of urelement kernel models; choiceless universality)
and Part VIII from batch 90 (`1404038df`: named group actions on atoms and
Replacement); its Collection spectrum and part of Part VIII are proved
independently in the research-report collection's
[naming elementary embeddings](../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/),
a batch-89 report on urelement set theory without surreal content.
[Surreal well-orders](foundations-and-computation/surreal-well-orders/)
gained Part XV from batch 89 (`193e2e942`: countable global choice over
Zermelo set theory, nonconservative conditionally on an unreviewed
interface to Glazer's countermodels, and exact rank-model spectra at every
limit height), and
[discrete initial subgroups and omnific normalization](surreal/discrete-initial-subgroups-and-omnific-normalization/)
a fourth source from batch 90 (`5c32fda02`: the canonical residue images of
nonstandard models of PA, which answers its residue-image question for PA,
and perfect transcendence gaps). Reciprocal notes are in `8d7d03c3e`,
`fc1ad4275` and `e50dde15b`. Batch 87's other manuscript, on Glazer's box
game, and batch 90's hat-guessing manuscript went to the research-report
collection's `measurable-box-games`; batch 88 brought nothing here. None
of the new material is formalized or indexed in the formalization ledger
yet, and its proof review is pending.

Batches 81 to 86 (3 October 2026) add two reports and extend three.
Batch 84 (placed in `e1395c66c`, written in `a11efab09`, with reciprocal
notes in `883e0b3b2`) adds
[self-embeddings of the surreal numbers](surreal/surreal-self-embeddings/),
merged from six manuscripts written independently on one prompt (a seventh
archive is an earlier edition of one of them and is not printed): order
embeddings with simplicity-initial image are onto, Hahn lifts and the
weighted monomial classification, a proper cofinal field embedding and a
nonidentity automorphism fixing any set together with all reals and
ordinals, continuity equivalent to cofinality, and exponential rigidity with
cofinality in place of surjectivity; conditional elementary, large-cardinal
and omega-series results are marked. About half of each manuscript
re-proves results of five existing reports, printed once with their labels
credited. One manuscript showed a sentence of
[omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/)
false as stated; it was corrected in `f06e67d10` before the placement.
Batch 86 (placed in `3d2177df4` and `0bd0e5527`, written in `ae7b9ab74`
and `c3661c2ee`) adds [Polish models of omnific arithmetic](foundations-and-computation/polish-models-of-omnific-arithmetic/),
merged from seven manuscripts in five Parts: an affirmative answer to
Glazer's Question 2 as printed (the cone of `ℝ ×→ ℤ` is an uncountable
Polish model of Presburger arithmetic with continuous addition, embedded
additively in `Oz`); Borel presentations of Hahn fields with the support
barrier on the omnific side; continuous Presburger arithmetic (Polish
exactly for Borel cones, `2^ℵ₀` models on Baire space, a Polish semiring
cone of `ℤ + tℝ[t]` failing open induction, `0` isolated in every Polish
`PA⁻` cone); local compactness forcing discreteness of discretely ordered
rings; and which Hahn, Puiseux and Levi-Civita fields carry Polish
topologies. Its manuscript 10 became Sections 19–22 of
[discrete initial subgroups and omnific normalization](surreal/discrete-initial-subgroups-and-omnific-normalization/)
(written in `4eed8c460`): a bounded dyadic definition of `ℕ`, and no
nonstandard model of `IΔ0` has an initially realizable additive group, which
partly answers that report's question on arithmetic fragments.
[Surreal well-orders](foundations-and-computation/surreal-well-orders/)
grew from four to twenty-two manuscripts: six batch-81 continuations
(placed in `f0cd7032d` and `c4720e1b2`) became Parts VI–IX and twelve of
batch 83 (placed in `2e06337d5`, written in `07ee2b30c`) Parts X–XIV, with
reciprocal notes in `d68b65ea0` and `da289d902`. None of the new material
is formalized or indexed in the formalization ledger yet, and its proof
review is pending.

Batch 80 (placed in `ccc046989`, written in `d51fafea8` and `0be9b9134`,
with reciprocal notes in `a13efdd51`) adds one report,
[surreal well-orders](foundations-and-computation/surreal-well-orders/),
merged from four manuscripts written independently on one day; two pairs of
the archives share a name, but none is an edition of another. It compares
the well-orders of `No` lexicographically. For sets of surreals the order
behaves as over every infinite linear alphabet, which is the theorem layer
of the research-report collection's
[lexicographic well-orderings of the reals](../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/),
printed as pointers with second routes, except at birthday cutoffs: the
minimal slice of `No_{<κ}` has binary coding length `κ·κ` exactly at
singular strong limits, which answers that report's question on other ground
orders in part. Over GB without set choice, a class well-order of `No`
exists exactly when global choice holds; all class well-orders are compared
directly, with exact adjacency; set-like global well-orders carry a
bounded-support core isomorphic to `No` that interpolates every uniformly
set-indexed cut; and inaccessible and Kelley–Morse models separate the
set-like from the unrestricted order. The core that the manuscripts prove up
to four times is printed once, with the other proofs as routes or notes.
Reciprocal notes went to the reals report,
[the surreals as a real vector space](surreal/real-vector-space-structure/),
[birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/)
and [foundations](foundations-and-computation/foundations/). The new report
is not yet indexed in the formalization ledger; nothing in it is
formalized, four inputs it uses are proved in Lean on the sign carrier, and
its independent proof review is pending (the Hilbert's-tenth research tree
reviewed the four delivered archives and the merged text, outside this
collection's review record).

Batch 73 (placed in `26abf259b`, written in `9265235fd`, with reciprocal
notes in `5cbcc029f`) adds one report,
[the surreals as a real vector space](surreal/real-vector-space-structure/),
merged from three manuscripts written independently on one day in answer to
one question: what is the natural basis of `No` over `ℝ`? The monomials
`ω^γ` are its canonical Hahn basis and the basis of every layer of the
associated graded algebra, but a Hamel basis only of the finite-support
subspace; no set spans `No`, and in NBG with global choice a class Hamel
basis exists but must contain a proper class of infinite-support vectors.
The report also describes the canonical linear structure (support
projections, strong linear maps and the strong real dual) and, in Part IV,
the Euler quotient. The shared theorems are printed once, with the other
manuscripts' proofs as second and third routes, and results that re-prove
[three duals of Hahn vector spaces](surcomplex/three-duals-of-hahn-vector-spaces/)
and [exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/)
are pointers. Reciprocal notes went to those two reports, to
[omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/)
and [omnific Diophantine geometry](surreal/omnific-diophantine-geometry/),
and to the notation guide. The new report is not yet indexed in the
formalization ledger; nothing in it is formalized, and its independent
proof review is pending.

Batches 58 and 59 (placed in `b30441a` and `f2cb203`, written in `4e12835`
and `da05b41`) add one report,
[polytopes at surreal scales](surreal/polytopes-at-surreal-scales/), merged
from twelve manuscripts into ten Parts on finite polytopes over a set-sized
real closed field `K ⊇ ℝ` inside `No`: lifting compression to at most
`n−d−1` real layers with exact germ degrees, coordinate-truncation
histories, affine residues and mixed-volume scales, real traces and lattice
counts, extension complexity invisible to all-order jets, mixed-volume
tomography and realization, exponential contact depth of moving vertices,
omnific integer hulls with a rational-normal dichotomy, and set-sized
presentations. Batch 59 also adds a reciprocal note to
[omnific groups and lattices](surreal/omnific-groups-and-lattices/)
(`526c255`). The new report is not yet indexed in the formalization ledger;
nothing in it is formalized, and its independent proof review is pending.

Batches 24–29 (placed in `be06fc8`, `cf350b1`, `f4c9504`, `a4dcb91`,
`c6359e4` and `66d7e55`, each followed by its write commits) add nine reports
and extend three earlier ones; most of the new reports also grew by later
additions within the period. Five of the new reports concern Conway's omnific
integers `Oz`:

- [Omnific Diophantine geometry](surreal/omnific-diophantine-geometry/),
  from thirteen manuscripts: constant-term transfer, Pell and norm-form
  rigidity, single quartic equations defining `ℤ` in `Oz`, a Diophantine
  constant term, fractions, and only constant points on smooth affine curves
  other than the affine line, on abelian varieties and on suitable
  logarithmic complements.
- [Set-sized quotients](surreal/set-sized-quotients-of-omnific-integers/),
  from eighteen: every ring map from `Oz` to a set-sized ring factors through
  the constant term; exact cardinal thresholds, homological dimensions, and
  the proper-class Boolean branching of the integral closure.
- [Omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/)
  (five manuscripts), [omnific groups and lattices](surreal/omnific-groups-and-lattices/)
  (four) and [discrete initial subgroups](surreal/discrete-initial-subgroups-and-omnific-normalization/)
  (two), the last with a proposed affirmative answer to a question of Ehrlich
  and Kaplan.

The others are [definable surreals and omnific integers](foundations-and-computation/definable-surreals-and-omnific-integers/),
[omnific notations](foundations-and-computation/omnific-notations/),
[Hahn–Hilbert geometry](surcomplex/hahn-hilbert-geometry/) and a second
physics report, [quantum and gauge scale reductions](physics/quantum-and-gauge-scale-reductions/).
[Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/)
gains theta descent, which makes the order-unit boundary of differential
rigidity exact (Theorem H); [entire functions](surcomplex/entire-functions-at-arbitrary-rank/)
gains rectification by entire automorphisms; and
[Euclidean three-space](surreal/euclidean-three-space/) gains Part V on
compact groups over `No`.

Proof review of this material is recorded in the [review record](REVIEW.md).
The Diophantine report's review covers its original material and Sections
11–15 and 19, plus the Gaussian-fiber and étale-norm additions in Section 6.
Those proofs now include support arguments and boundary examples. Source
07's quartic and the elementary ring/Euler subsections 16.2–16.3 are also
reviewed, with the trivial-exponent-group exception and the meaning of
image inclusions made explicit. Later passes cover the rest of Section 16
and Sections 17.1–17.4: differential rigidity, smooth curves, exact arithmetic
fibers, separated-model descent and projective coordinate ideals. The review now
also covers Section 17.5 and the singular-curve criterion through Section 17.6.5:
conductor certificates, the discrete boundary place and structural consequences.
Later passes review the repeated-root applications and groups and coefficient
algebras and logarithmic applications through Section 18.6. Remaining curve
pointers and neighbouring-report comparisons still await review; Section 20
and Sections 21.1–21.6 now have a scope check, with the exact boundary in its
[reconciliation](surreal/omnific-diophantine-geometry/RECONCILIATION.md); its
remaining geometric arguments and the other new reports and additions await
review. Lean covers the omnific ring and constant-term package, degree
laws, units and finite elements, the exact omnific floor and ordinary
polynomial-root rigidity of the Diophantine report. Its other unmapped
Diophantine results remain pending.

Placement `21375f8` (batch 30) adds two report bases,
[critical-point defects](foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)
and [dilation rigidity](surcomplex/autonomous-dilation-relations/), and
companions to the holonomic, nonabelian-support and omnific-preserving
reports. The first four writes through `1ab41af` integrate those companions
and the dilation report; `de45cee` completes the three-manuscript
critical-point-defects assembly. Its initial 76 standard results were indexed;
independent proof review and Lean formalization remain pending.
That automorphism assembly had nine manuscripts and states automatic
strongness for `Oz` automorphisms; these new claims await proof review.

Placement `9d28e28` adds [independent surreal copies](surreal/independent-surreal-copies/),
a proposed construction of copies sharing a prescribed set-sized Hahn core,
written as a single-source report in `781b19e`. Its eight companions are now
integrated, including theta hierarchies (`1d3f503`) and polynomial
composition (`8bc7994`). The nine manuscripts
placed in `7d04483` are also written through `c315ac9`, expanding eight
existing reports. They add Galois rank, arithmetic sampling, finite symmetry
descent, support-bounded fields, cyclic ramification, measurable first
failures, Chevalley groups and arbitrary-rank coefficient recovery.
Their new proofs remain outside the independent review scopes recorded here.

Placement `aa9c891` retires the next nine archives and adds two main texts:
[omnific continued fractions](surreal/omnific-continued-fractions/) and
[exponential relations over omnific integers](foundations-and-computation/exponential-relations-over-omnific-integers/).
Their 60 standard results are indexed and PDFs supplied; their collection
editions are written in `68db1b5` and `fa54502`. The two dilation companions
are integrated in `1ef6bba`, adding 33 standard results on support rank and
algebraic independence of dilation orbits. The coefficient-observables and
Noetherian-compression companion is now integrated in `76dd876`, adding 11
standard results to the 222-result holonomic report. The discriminant and
étale-unit companion is integrated in `fdedce0`, adding 27 standard results
in Section 19.4 of the Diophantine report. The final three batch-33 companions
are integrated in `19d0b0e`, adding 89 standard results to the 274-result
omnific-automorphism report: formal orbit fields, left-orderable symmetry
groups and formal integration of derivations. All 185 earlier standard
statements in that report are unchanged. Independent proof review remains pending;
assembly alone does not extend any Lean mapping.
A further universal-symmetries and difference-equations archive arrived in
`bbe23a3`, and eight more archives arrived in `a4611ad`. All nine are now
placed in `a7a435f` as additions to six reports, with audits and verification
code supplied. All nine companions are now integrated through `ef3d112`:
rotation-equivariant dynamics, Gaussian omnific real forms, beyond-composita
obstructions, infinite simultaneous unitary straightening, universal
symmetries and difference equations, class residue fields, semialgebraic
preservers, polyhedral-cone cores and henselian branching. Their 204 new
standard results brought the index to 4,602 across 63 reports. Independent
review and Lean formalization of these new claims remain pending.
The Hahn-joins archive from `267b910`, placed in `dec8d56`, is now integrated
in `32bb723` as the third independent-copies manuscript. Its 24 new standard
results bring the current index to 4,626 across 63 reports. Independent
proof review and Lean formalization remain pending.
The singular-curve addition
gives a normalization criterion beyond the smooth case; its proof, structural
consequences, repeated-root test and arithmetic applications now have a
manuscript review. The review also covers the closing singular-curve scope
notes and Sections 18.1–18.6 on groups, coefficient algebras, boundary
examples and logarithmic applications. The workspace and question-status
review covers Sections 20–21.6. A subsequent pass checks geometric
pointers and the cited statement scopes in Section 21.7, correcting the
real arithmetic boundary and stale group-report comparison. The independent-copies report and its
class-foundation assumptions remain pending proof review and Lean formalization.

Batch 23 (placed in `e4f8848`, written in `7af7056`) adds
[Gamma and zeta](surcomplex/gamma-and-zeta-functions/), merged from six
manuscripts on the same questions after a claim-by-claim comparison; its
proof review and formalization remain pending.

Batch 22 (placed in `7b5f934`, written in `68e2960`) adds two reports,
[first-kappa coefficients](surcomplex/first-kappa-coefficients/) and
[single-dilation Hahn support](surcomplex/single-dilation-hahn-support/), and new
sections to the measures, holonomic-rigidity, Euclidean three-space,
entire-functions and trigonometry reports. Their proof review and
formalization remain pending.

Two reports placed in `d4e71b7` and written in `3a2d35d` are catalogued in the
tables below: [surreal fields across universes](foundations-and-computation/surreal-fields-across-universes/)
and [birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/),
both set theory about the surreal field. Their proof review and formalization
remain pending.

Four reports placed in `5fe7f8d` and written in `fb182ea` are catalogued in the
tables below:
[vector and tensor fields](surreal/vector-and-tensor-fields/),
[Euclidean three-space](surreal/euclidean-three-space/),
[finite surreal probability](surreal/finite-surreal-probability/) and
[surcomplex field automorphisms](surcomplex/surcomplex-field-automorphisms/).
The finite-probability main-text review now covers Sections 2–17; remaining
imports and source reconciliation remain pending. The field-automorphism
main-text review covers Sections 1–15 and Appendix B; its remaining imports
and source reconciliation, and review of the other two reports, are pending. Lean coverage is tracked
separately in the ledger. The same batch added
source material to the measures and trigonometry reports; those additions do
not extend their earlier proof-review scope.

## Reading routes

- **For foundations or formalization:** read
  [foundations](foundations-and-computation/foundations/), especially its
  size restrictions and verification boundary, then the current
  [formalization ledger](FORMALIZATION.md). The proposed architecture in the
  article is a plan; the ledger records implementation status.
- **For surcomplex analysis:** read [analysis](surcomplex/analysis/), then the
  four-ring comparison in [analytic geometry](surcomplex/analytic-geometry/).
  Continue to finite deformations, contours, or global divisors as needed.
- **For computation:** read [computer algebra](foundations-and-computation/computer-algebra/)
  for capability levels and prototypes, and
  [computable surreals](foundations-and-computation/computable-surreals/)
  for representations and uniform algorithms.
- **For measures and probability:** read
  [Hahn-valued measures and probability](surreal/hahn-valued-measures-and-probability/)
  first. Its distinction between *strong* and *coefficientwise* countable
  additivity is a prerequisite for
  [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/), whose
  measures require coefficientwise additivity, with strong additivity optional. "Moment" means power moments there,
  Fourier moments in the Herglotz report, and finite Prony input in
  [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/).
- **For a particular theorem:** use the report tables below. Read its local
  conventions before importing a definition from a companion report.

## Surreal numbers: twenty-six reports

| Report | Question or main subject |
|---|---|
| [Hahn evaluation at omega](surreal/hahn-evaluation-at-omega/) | Why increasing-support evaluation `x^a ↦ ω^a` fails, and which exponent maps permit field homomorphisms |
| [Broadcast sums](surreal/broadcast-sum-of-surreal-sequences/) | The sign-truncation game and Lipparini's broadcast-sum question |
| [Product birthdays](surreal/gonshor-product-birthdays/) | Gonshor's bound `b(xy) ≤ b(x) ⊗ b(y)` for specified ordinal-support normal forms |
| [Laurent birthdays](surreal/gonshor-laurent-birthdays/) | The same bound and sharper formulas over `ℝ((ω⁻¹))` |
| [Canonical forms and option graphs](surreal/canonical-forms-need-not-be-subgraphs/) | Why a canonical representative need not occur as a subgraph of a given form |
| [Genetic gaps and primitives](surreal/genetic-gaps-and-primitives/) | A nonconstant genetic indicator with derivative zero |
| [Exponential automorphism rigidity](surreal/exponential-automorphism-rigidity/) | Finite displacement identities, faithful action on the value group and a negative answer to Kaplan–Krapp–Serra Question 5.4 (arXiv v3); "rigidity" here means faithfulness, not triviality |
| [Gamma functions](surreal/gamma-functions/) | Convexity of a family of surreal Gamma extensions and failure of uniqueness |
| [Tail-spans and differential transcendence](surreal/tail-spans-and-differential-transcendence/) | Cofinite spans classify relations among Hahn sums with independent square-root coefficients; continuum many differentially independent surreals and analytic functions; its derivation formula is cited from the surcomplex differential-equations report |
| [Hahn-valued measures and probability](surreal/hahn-valued-measures-and-probability/) | Strong and coefficientwise Hahn-valued measures: atomicity, extension and moment criteria, hidden negative mass; the `ω+1` threshold and the finitely supported standard part hold only in the strong class; a countable-scale density criterion, Hahn-valued integration and conditional expectation; the exact Bernoulli product criterion at interior baselines without uniform separation |
| [Markov generators at every scale](surreal/markov-generators-at-every-scale/) | All-scale resolvent hierarchies of finite positive Hahn rate matrices and their converse realization; divisible value group, no path measures or infinite state spaces |
| [Transcendence over bounded support](surreal/transcendence-over-bounded-support/) | `2^cf(G)` algebraically independent Hahn series over the fraction field of bounded-support series, and linear-disjointness descent; transcendence from the support, not the coefficients |
| [Matrix scaling at surreal scales](surreal/matrix-scaling-at-surreal-scales/) | Fixed-margin diagonal scaling of positive Hahn matrices; the spanning-tree deletion gap is the exact gain; no Sinkhorn convergence claim |
| [Polytopes at surreal scales](surreal/polytopes-at-surreal-scales/) | Finite polytopes over set-sized real closed `K ⊇ ℝ`: all-scale lifting compression to at most `n−d−1` real layers with exact germ degrees, coordinate-truncation histories, affine residues and mixed-volume scales, lattice counts with non-quasipolynomial Ehrhart functions, extension complexity invisible to all-order jets, mixed-volume tomography and realization (a Fano obstruction), exponential contact depth of moving vertices, omnific integer hulls with a rational-normal dichotomy, and set-sized presentations; twelve manuscripts; no Lean verification |
| [The surreals as a real vector space](surreal/real-vector-space-structure/) | `No` over `ℝ`: the monomials as canonical Hahn basis and layer basis of `gr No ≅ ℝ[No]`, but a Hamel basis only of the finite-support subspace; no set spans `No`, and class Hamel bases (NBG with global choice) need a proper class of infinite-support vectors; window dimensions, strong linear maps and the strong real dual, the vanishing order-bounded dual, and the Euler quotient as a continuum-dimensional `ℝ(X)`-space; three manuscripts; no Lean verification |
| [Vector and tensor fields](surreal/vector-and-tensor-fields/) | Layered tensor calculus with surreal coefficients in every dimension: Hahn-supported smooth fields, Taylor prolongation, Hodge and Stokes; 3D calculus and Minkowski fields as parts; not a physics claim |
| [Euclidean three-space](surreal/euclidean-three-space/) | Coordinate and spherical geometry of `No³` with finite angles, and the rotation group `SO(3,No)` as a split extension with a perfect infinitesimal kernel; normal subgroups by valuation cuts and the universal set-sized quotient of `SO(3,No)`; Part V: compact groups over `No`, whose universal set-sized quotient exists exactly in the semisimple case |
| [Finite surreal probability](surreal/finite-surreal-probability/) | Surreal-valued probability on finite algebras: conditioning on infinitesimal events, log-odds, entropy, scoring rules; compare the measures report for countable additivity |
| [Omnific Diophantine geometry](surreal/omnific-diophantine-geometry/) | Diophantine equations over the omnific integers `Oz`: constant-term transfer, Pell and norm-form rigidity, quartic definitions of `ℤ`, a Diophantine constant term, fractions, and rigidity of smooth curves, abelian varieties and logarithmic complements; fifteen integrated manuscripts; Section 19.4 and its later question/status notes reviewed, including descent, critical-point and normal-matrix applications and an affine-conjugacy criterion; full source reconciliation awaits review; exact scope in its reconciliation |
| [Set-sized quotients of omnific integers](surreal/set-sized-quotients-of-omnific-integers/) | Every ring map from `Oz` to a set-sized ring factors through the constant term; exact cardinal thresholds, homological dimensions, integer-valued polynomials, and the proper-class Boolean branching of the integral closure; twenty-four manuscripts; support thresholds, initial fixed-group bounds, all five set-sized models, their organizing theorem, the flat-ideal/Ext package, and finite-support cores through the lattice/dimension comparisons, tensor normal forms through common-scale matrices, and set-presentation obstructions through exact model relation counts, flat dimensions, coefficient-Tor ranks, rank-two moduli, endomorphism orders, tail-annihilated modules and face telescopes through nonvanishing and exact projective dimensions, and derived algebra through framed reconstruction and the constant-term shadow reviewed; all 30 standard polyhedral results and their ten question/status notes reviewed; with fixed coefficients and rational space, every strict enlargement of full-dimensional pointed rational polyhedral cones is nonflat, even when old ray-pair tests pass; the simplicial projective formula requires a proper face; the universal module assertion retains its lower-universe size bound; noncoherence and the stronger global-dimension bounds require a coefficient-field restriction; the coefficient-field rank-one core has weak global dimension one; a large quotient may still have small images; internal-field proofs reviewed through compression and transfer to residue fraction fields, including the proper field image with its exact support description and agreement on overlaps; binomial kernels and dyadic algebras reviewed, with an explicit idempotent outside every dyadic stage; class-residue foundations reviewed through maximal extensions and coefficient comparison, with the global-choice equivalence already for class domains of characteristic two; monomial cutoff, tail reduction and scale/branch families reviewed, with continuum many maximal extensions of each fixed dyadic branch; separation, field realization and support-prime classification pending |
| [Omnific-preserving automorphisms](surreal/omnific-preserving-automorphisms/) | Which strong automorphisms of a Hahn field preserve its omnific integers: the convex-support criterion, stabilizers, nondefinable monomials, and polynomial coefficient rigidity; fifteen integrated manuscripts; later parts claim automatic strongness, coefficient recovery, formal orbit fields, left-orderable symmetry groups and integration of derivations, pending independent review; a false reason in Section 27.2 corrected in `f06e67d10` |
| [Omnific groups and lattices](surreal/omnific-groups-and-lattices/) | Algebraic groups with no new omnific points; `SL_n(ℤ)` as the universal set-sized quotient of `E_n(Oz)` for `n ≥ 3`, but none in rank two; shortest vectors and missing infima in omnific lattices; five manuscripts |
| [Omnific continued fractions](surreal/omnific-continued-fractions/) | Exact digit fibers as translates of a valuation ideal, full Hahn realizations and periodic algebraic fibers; ordinary finite indices only; proof review pending |
| [Discrete initial subgroups and omnific normalization](surreal/discrete-initial-subgroups-and-omnific-normalization/) | A proposed affirmative answer to Ehrlich–Kaplan's question (JSL Question 9.1): every discrete initial subgroup of `No` is isomorphic to an initial subgroup of `Oz`; convex subquotients of initial groups are initially realizable; four manuscripts; source 03 (batch 86): a bounded dyadic definition of `ℕ`, and nonstandard models of `IΔ0` have no initially realizable additive group (open induction does not suffice); source 04 (batch 90): the canonical profinite residue image of a nonstandard model of PA is exactly `Ẑ(SSy M)`, answering the residue-image question for PA (open for `IΔ0`), and perfect transcendence gaps over analytic fields |
| [Independent surreal copies](surreal/independent-surreal-copies/) | Prescribed common Hahn cores, surreal self-embeddings, transcendence gaps and maximal transcendence of Hahn joins; three manuscripts; class assumptions and proof review pending |
| [Self-embeddings of the surreal numbers](surreal/surreal-self-embeddings/) | Order, simplicity, field, valuation and exponential self-embeddings of `No`: simplicity-initial images are onto, Hahn lifts and weighted monomial classification, a proper cofinal embedding and a nonidentity automorphism fixing any set with all reals and ordinals, continuity iff cofinality, exponential rigidity under cofinality; conditional elementary, large-cardinal and omega-series results marked; six manuscripts; proof review pending |

The two birthday reports have different domains. The first allows its specified
ordinal supports but excludes positive powers of `ω`; the Laurent report allows
those powers but uses the integer exponent lattice. Their common part includes
`ℝ[[ω⁻¹]]`. Neither domain theorem subsumes the other. Here `⊗` denotes
**natural ordinal multiplication**, as distinguished in the notation guide.

## Surcomplex numbers: twenty-eight reports

| Report | Main subject and useful prerequisite |
|---|---|
| [Analysis](surcomplex/analysis/) | Hahn-supported calculus, function classes, zero clusters and all-scale rigidity; start here |
| [Analytic geometry](surcomplex/analytic-geometry/) | Coefficient rings, preparation, finite zero geometry and fixed-domain obstructions |
| [Finite deformations](surcomplex/finite-deformations/) | Support-controlled division, multiplicity and residue duality |
| [Contours and Stokes](surcomplex/contours-and-stokes/) | Standard-part Jordan separation, coefficientwise integration and contours representing residue series |
| [Global divisors](surcomplex/global-divisors/) | Plane support obstructions; compact Picard classification, cohomology and Abel criteria |
| [Polynomial algebra](surcomplex/polynomial-algebra/) | Finite-degree factorization and root geometry in modulus and valuation balls |
| [Trigonometry](surcomplex/trigonometry/) | Finite-angle polar representation and geometry at arbitrary surreal scale; the rotation group `SO(2,No)`; period arithmetic of global phases and a partial answer to an Ehrlich–Kaplan question |
| [Differential equations](surcomplex/differential-equations/) | Berarducci–Mantova differential algebra and finite primitives; matrix, regular-singular and autonomous equations; transfinite second-order critical potentials; coherent coordinate equations; its Section 5 on "phase" is a prerequisite |
| [Rank-one Berkovich geometry](surcomplex/rank-one-berkovich/) | Tate algebras, disks and annuli in the fixed field `ℂ((t^ℝ))` |
| [Spectral theory](surcomplex/spectral-theory/) | Finite matrices over real closed fields, singular values and valuation scales; exact matrix-root fields and Hankel splitting fields of squarefree real-rooted polynomials over a nondivisible `Γ` |
| [Dynamics and normal forms](surcomplex/dynamics-and-normal-forms/) | Linearization, periods and quasi-periodic equations; exact scalar and drifting multipliers answer the common-domain question oppositely, and an angular-rank bound covers every exact diagonal multiplier; its convention and threshold tables are prerequisites |
| [Nonabelian support](surcomplex/nonabelian-support/) | Matrix Cousin problems, inverse monodromy, and essential-singularity bundles that stay nontrivial over `Mer((t^Γ))`; its two support criteria test different objects; compare the scalar global-divisor report |
| [Entire functions at arbitrary rank](surcomplex/entire-functions-at-arbitrary-rank/) | Cofinality, factorization, the exact jet image, ideals above canonical products and scalar extension of entire series over one fixed Hahn field; in several variables only the scalar-extension clause is answered; prime ideals above one-simple-node products and their splitting under cofinal extension; with countable cofinality, radially finite sets in `K^d` are line-rectifiable by entire automorphisms iff `Γ` has an order unit, and fat-point ideals on rectifiable configurations |
| [Holonomic rigidity](surcomplex/holonomic-rigidity-for-entire-hahn-functions/) | Entire D-finite series are polynomials. Without an order unit, nonpolynomial entire series are differentially transcendental in all orders; with one, a theta series has minimal differential order three. Later chapters exclude order two for every value group, exclude order three through total jet degree three, and classify existence of mixed linear differential–dilation equations by relative valuation scales, assuming no quotient of distinct multipliers is a root of unity. These later chapters await independent proof review |
| [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/) | Tate elliptic curves at arbitrary rank: exact Hahn domain `U_q` and `U_q/q^ℤ ≅ E_q(K)`, plus multiscale theta series; the bounded-period quotient itself has a Molcho–Wise precedent |
| [Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/) | Two inequivalent spectra: ordinary normal operators extended to `H((t^Γ))`, and exact diagonalization of row- and column-finite Hahn matrices; Section 3 reconciles their apparently conflicting accumulation statements; Parts III and IV add Drazin halos for any unital algebra and noncommuting compact perturbations |
| [Expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/) | Exact itinerary fibers of expanding polynomials over Hahn fields, and the order-unit dichotomy; valuation-expanding is not repelling, and no Julia/Fatou theory is built |
| [Hahn–Herglotz positivity](surcomplex/hahn-herglotz-positivity/) | Matrix Herglotz normalization on halos, a null-ideal positivity criterion, and Toeplitz-positive Fourier moments with no positive measure; it assumes coefficientwise additivity, with strong additivity optional |
| [Prony reconstruction](surcomplex/prony-reconstruction-at-surreal-scales/) | Sharp valuation threshold for recovering `n` weighted nodes from `2n` power moments (no measures); compare polynomial algebra's coefficient threshold |
| [Wick summability certificates](surcomplex/wick-summability-certificates/) | Finite strict valuation inequalities decide strong summability of polynomial Wick diagram families over `ℂ((t^Γ))`, `Γ` divisible; diagramwise only, and a Hahn value is not an integral |
| [Three duals of Hahn vector spaces](surcomplex/three-duals-of-hahn-vector-spaces/) | Algebraic extension, completion and strong closure of `V((t^Γ))`; strong operators; comparison of represented, strong and continuous duals of a Hahn–Hilbert space |
| [Hidden negative Hermitian directions](surcomplex/hidden-negative-hermitian-directions/) | Hermitian forms positive over the finite-lattice-supported subfield yet indefinite over `ℂ((t^Γ))`; a two-scale matrix null-ideal criterion |
| [Hahn–Hilbert geometry](surcomplex/hahn-hilbert-geometry/) | Orthogonally split subspaces of `H((t^Γ))` are infinitesimal unitary rotations of ordinary ones; amplified graphs without nearest points, a projection poset that is a lattice only in finite dimension, metric rigidity, Fredholm least squares |
| [Surcomplex field automorphisms](surcomplex/surcomplex-field-automorphisms/) | Plain, valued, value-fixing and 1-automorphisms of `No(i)`; the real-axis stabilizer `Aut(No)×C₂` and phase twists that move `No`; exponential results are the rigidity report's |
| [First-κ coefficients](surcomplex/first-kappa-coefficients/) | Hahn series with fewer than `κ` terms: omitted types classified by the first `κ` coefficients, completion iff `cf(Γ) ≠ cf(κ)`, never spherically complete |
| [Single-dilation Hahn support](surcomplex/single-dilation-hahn-support/) | One monomial dilation defines coefficients, monomials and the valuation ring; its centralizer among all field automorphisms; undecidability |
| [Gamma and zeta](surcomplex/gamma-and-zeta-functions/) | Finite lifts and RH, strongly summable Dirichlet series at infinity, Stirling and Hurwitz, Gamma and zeta on the horizontal tube for any phase, reflection obstructions at infinite height; six manuscripts reconciled |
| [Dilation rigidity](surcomplex/autonomous-dilation-relations/) | Autonomous relations between exponent dilates; three manuscripts, including support-rank bounds and exact finite-support order; proof review pending |

Three distinctions recur throughout these reports.

**Specify the topology and the size of the index set.** In the full surreal
fine topology, every set-sized subset is closed and discrete, and a convergent
set-indexed net is eventually constant. In a universe-relative formulation,
these assertions require smaller-universe subsets and index types. Intrinsic
valuation topology on a fixed Hahn workspace behaves differently: `t^n → 0`
in `ℂ((t^ℚ))`. Even there, a strongly summable family need not converge
through its finite subsums; the foundations report gives the example
`Σ t^(n/(n+1))`. Formal support conditions and topological convergence are
separate requirements.

**Name the coefficient ring.** These four constructions impose different
conditions; the table is not a chain of interchangeable rings.

| Construction | Requirement |
|---|---|
| `ℂ{z}((t^Γ))` | Each coefficient is a convergent germ; no common radius is required |
| `O(D)((t^Γ))` | Every coefficient is holomorphic on the specified ordinary domain `D` |
| Common-domain Hahn germ ring `𝓡ₙ` | One neighborhood represents all coefficients, with shrinking allowed |
| `ℂ[[z]]((t^Γ))` | Each coefficient is formal |

A fifth construction, `Mer(D)((t^Γ))`, is not in the table: every coefficient
is meromorphic on the specified domain. It appears in global divisors, in
analysis, and in Part III of nonabelian support, which constructs bundles that
stay nontrivial over it.

For `η > 0`, the family `Σ_{r≥1} t^(rη)/(1−rz)` lies in the radius-free germ
ring but not in the common-domain germ ring: its coefficient poles `1/r`
approach zero. This witnesses that particular strict inclusion. Analytic
geometry gives separate obstructions for fixed domains and explains why
shrinking changes the applicable theorems.

**Keep different operations distinct.** Formal differentiation in `z`, a fine
derivative, and the Berarducci–Mantova scalar derivation act on different data.
A finite angle `θ` for `cis θ` is not an arbitrary primitive of an imaginary
coefficient. Likewise, nonabelian gluing uses supports of normalized **polar
factors**, while monodromy realization uses the **raw** monodromy matrices.
The [notation guide](NOTATION.md) records these distinctions and their local
symbols.

## Surquaternions: one report

[Surquaternions](surquaternions/surquaternions/) develops Hamilton's algebra
over surreal coefficients, its Hahn workspaces, and its exponential and
differential structures. Its convention table distinguishes three
exponentials and four derivative notions. Noncommutative identities need
their own hypotheses: the radial exponential obeys the usual product law on
a common commutative slice, but not on arbitrary pairs of quaternions.

## Physics: two reports

[Surreal scalars and spacetime](physics/surreal-scalars-and-spacetime/)
separates exact symbolic identities, conditional mathematics, physical
assessments and imported results. Replacing scalars can encode asymptotic
scales without regularizing a singular metric. For example, with nonzero
Schwarzschild mass `m`, the substitution `r = s^q w(s)`, with integer `q ≥ 1`,
`w ∈ ℝ[[s]]` and `w(0) ≠ 0`,
in `48m²/r⁶` gives a pole of order `6q` and leading coefficient
`48m² w(0)^(−6)`. The recorded special case `w(s) = 1+s` preserves `48m²`;
general substitutions need the factor `w(0)^(−6)`.

[Quantum and gauge scale reductions](physics/quantum-and-gauge-scale-reductions/),
merged from four manuscripts, applies the same claim-tier firewall to finite
quantum operations and gauge models: leading-Gram shadows of rare branches, a
sharp postselection cost, exact elimination of separated virtual sectors,
soft-mode Schur defects, optimal identification of an infinitesimal holonomy,
and Hahn deformations of gauge fields. It claims no departure from ordinary
quantum theory and no measurable infinitesimal.

## Foundations and computation: twelve reports

| Report | Main subject |
|---|---|
| [Foundations](foundations-and-computation/foundations/) | Classes and universes, workspace localization, support recursion, topology and a formalization proposal |
| [Computer algebra](foundations-and-computation/computer-algebra/) | Exact denotation, coefficient access, equality and approximation; three distinct Wolfram prototypes |
| [Computable surreals](foundations-and-computation/computable-surreals/) | Structural names, effective left-finite Hahn names and bounded-denominator Puiseux names |
| [Surreal fields across universes](foundations-and-computation/surreal-fields-across-universes/) | External saturation of an inner model's `No^M` in a same-ordinal outer universe: new ordinal sequences, fresh-sign gaps, first new birthday, nonconjugate surcomplex real forms; exact gap spectra under Cohen, Easton, Prikry and Namba forcing, real traces, and equal-spectrum fields that are not isomorphic (Part VIII, batch 37) |
| [Definable surreals and omnific integers](foundations-and-computation/definable-surreals-and-omnific-integers/) | The definable surreals form a real closed subfield, elementary in `No` and closed under `exp`, `log` and the omnific floor; `No ∩ HOD = No^HOD`, and `V = HOD` iff every omnific integer in `(0, ω)` is ordinal definable; the maximal initial core; Part II (batch 93): real parameters, countable assembly (independent of ZFC, from Con(ZFC)) and the common fixed field of the strong automorphisms fixing `R ∪ Ord`; Part III (batch 93): definable operations, absoluteness of normal forms without a same-reals hypothesis, and a parameter-free interpretation of `(V, ∈)` in `(No, +, ·, <, Oz, Ω)`; five manuscripts |
| [Omnific notations](foundations-and-computation/omnific-notations/) | Holonomic towers, hereditary forms and rational `ω`-terms with decidable equality and floor; raw `d`-block equality is `Π⁰₁`-complete and support validity `Π¹₁`-complete |
| [Birthday cutoffs and hereditary sets](foundations-and-computation/birthday-cutoffs-and-hereditary-sets/) | Surreals born below an epsilon number, with birthday, interpret `H_κ`: bi-interpretation, elementary inclusions, axiom spectra, outer models, orientation; Parts VI–VII (batch 89): Replacement-free cuts, definable-family schemes equivalent to ordinal bounding, Collection spectra of urelement kernel models, and choiceless universality (`X ↪ No` iff `X ↪ P(α)`, `KWP_1`, permutation models); Part VIII (batch 90): named group actions on atoms and Replacement, an exact orbit criterion and a strict kernel hierarchy; Part IX (batch 95): surreal-only and omnific foundations bi-interpretable with ZFC, round-trip axiomatizations, no theory uniformly interpretable in ZFC interprets NBG, and class lifts bi-interpretable with GBC and KM; ten manuscripts |
| [Critical-point defects](foundations-and-computation/large-cardinal-embeddings-and-normal-forms/) | Four manuscripts on the claimed exact support threshold for two transports, defect coefficients, and descent to the target model; proof review pending |
| [Exponential relations over omnific integers](foundations-and-computation/exponential-relations-over-omnific-integers/) | Toric relations and a decidable additive language with algebraic exponential predicates; elementary cores and computability boundaries; proof review pending |
| [Surreal well-orders](foundations-and-computation/surreal-well-orders/) | Lexicographic orders of the well-orders of `No`: set cutoffs with the singular `κ·κ` transition, set-length words, choiceless GB ⇔ global choice, direct comparison and adjacency of all class well-orders, a bounded-support core ≅ `No` interpolating set-indexed cuts, diagonal non-coding, inaccessible and KM models; twenty-eight manuscripts (Parts VI–XIV from batches 81 and 83: strata, gap spectra and topology, termination types, cuts of the core, block decompositions and condensation histories; Part XV from batch 89: countable global choice over Zermelo set theory, conditionally nonconservative, and exact rank-model spectra at every limit height; Part XVI from batch 96: definable class well-orders beyond `Ord`, strong comparability ⇔ canonical histories over GB without choice, the hereditary term order and definability ceilings; Part XVII from batch 97: finite-support arithmetic and definability horizons); the set-sized layer re-proves the reals report; proof review pending |
| [Polish models of omnific arithmetic](foundations-and-computation/polish-models-of-omnific-arithmetic/) | Glazer's Question 2 answered affirmatively as printed: the cone of `ℝ ×→ ℤ` is an uncountable locally compact Polish model of Presburger arithmetic with continuous addition, embedded additively in `Oz`; Borel presentations of Hahn fields exist exactly for scattered supports, and no Polish recoding of the finite principal-part ring makes addition continuous; continuous Presburger arithmetic and a Polish semiring cone failing open induction (Part III), local compactness forcing countability (Part IV), Polish Hahn, Puiseux and Levi-Civita fields (Part V); Baire-category rigidity of discretely ordered rings (Part VI), nonsplit models and exact continuity (Part VII), a **claimed, unreviewed** ATR₀ answer to Glazer's Question 1 (Part VIII), locally compact cones (Part IX), elementary embeddings and Polish submodels of lexicographic models (Part X), local geometric codes (Part XI), Polish group completions and class manifolds (Part XII); Borel Presburger orders in one real dimension (Part XIII), the exponent-group threshold (Part XIV), rational rank and self-embeddings of Levi-Civita fields, with a counterexample to a Kuhlmann–Serra lemma (Part XV), Borel orders on separable Hilbert spaces (Part XVI), Borel summability and derivations of left-finite series fields (Part XVII); Borel conjugacy of derivations (Part XVIII), exact support complexity and strong summation (Part XIX), Borel flows (Part XX), pairs of derivations and finite-dimensional Lie algebras (Part XXI); twenty-four manuscripts; proof review pending |
| [A Cantor space of surreal subfields](foundations-and-computation/cantor-families-of-surreal-subfields/) | Countable real closed subfields of one explicit countable surreal field as a closed Cantor family with unique finite supports; Borel-complete isomorphism, an analytic-complete fixed-source embedding locus, complete analytic embeddability inside one field (the unrestricted theorem is Calderoni–Marker–Motto Ros–Shani's), the finite-transcendence openness threshold and two generic regimes; one manuscript; proof review pending |

A mathematical closure theorem need not supply a uniform algorithm on the
chosen names. In particular, numerical coefficient access does not supply a
decidable exact support or a leading exponent. The computability report states
which operations need that additional information. The computer-algebra
report separately records each prototype's coefficient field, exponent
lattice, supported operations and known implementation defects.

## Files, provenance and building

Each report has a LaTeX source, a typeset PDF and a local README. Most
also retain verification programs under `code/` and recorded outputs under
`data/`. Those finite checks do not establish infinite theorems. The former
`sources/` archives were retired in `e5791a8`; their tracked originals remain
available in Git history. For example, run
`git ls-tree -r --name-only 608dd23 -- docs` to locate an old manuscript and
`git show 608dd23:<path>` to read it. The computable-surreals originals were
never tracked here; its provenance manifest records their archive identities
and hashes. Reconciliation of every source claim remains a separate audit
obligation.

Build from the report's own directory with a TeX distribution containing its
listed packages:

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
```

If `latexmk` is unavailable, run `pdflatex -halt-on-error
-interaction=nonstopmode article.tex` repeatedly until references and the
contents stabilize. Use `surreal_product_birthdays.tex` in the product-birthday
directory, `surreal_graphs.tex` in the option-graph directory, and `manifest.tex`
for the catalogue. The broadcast-sum report uses its checked-in `article.bbl`.
Inspect the final log for unresolved references and inspect affected PDF pages;
a successful typesetting run is not a proof check.
