# combinatorial-coefficient-calculus

Canonical consolidation of six combinatorial coefficient-calculus and inversion
manuscripts received on 2026-09-01. Each arrival supplied one flat LaTeX/PDF
pair. ZIP CRCs, member paths, and member types were checked before extraction;
at intake the filed source and PDF bytes were identical to their ZIP members.

The archival consolidation is complete: `Combinatorial_Coefficient_Calculus/`
is the single surviving package, and the five donor directories were retired
after all source, topic, and claim disposition rows were completed. The
mathematical formalization campaign remains open. Its canonical source evolves
as proofs are repaired, strengthened, and matched with Lean declarations.

| Record | Purpose |
| --- | --- |
| [Canonical TeX](Combinatorial_Coefficient_Calculus/Combinatorial_Coefficient_Calculus.tex) and [PDF](Combinatorial_Coefficient_Calculus/Combinatorial_Coefficient_Calculus.pdf) | Mathematical exposition and the single in-document Lean claim register. |
| [Campaign status](Combinatorial_Coefficient_Calculus/FORMALIZATION_STATUS.md) | Current compilation, review, rendering, and remaining-work receipts. |
| [Provenance](Combinatorial_Coefficient_Calculus/PROVENANCE.md) | Consolidation boundary and immutable recovery procedures. |
| [Source inventory](Combinatorial_Coefficient_Calculus/SOURCE_INVENTORY.csv) | Six original sources and their immutable Git recovery locators. |
| [Source dispositions](Combinatorial_Coefficient_Calculus/SOURCE_DISPOSITION.csv) | Editorial decisions for source, topic, and claim records. |
| [Canonical validator](Combinatorial_Coefficient_Calculus/validate_canonical.py) | Structural and provenance checks; this package is expected to pass `--final`. |

The current campaign rebuilds the canonical TeX/PDF pair after source
integration. Rendering is pending at this checkpoint; the final page count
and parity receipt will be recorded in the campaign status. Earlier notes that
PDF building was skipped at the user's request refer to other source-only
sessions. They do not waive this campaign's render requirement. Historical
arrival and checkpoint PDFs remain recoverable through Git.

Standalone checksum ledgers are retired. Provenance is preserved in Git and the
source inventory, and the validator does not maintain or require live-file
digests. Its checks cover structure, labels, references, citations, proof pairing,
source coverage, Git object availability, dispositions, and publication layout.
They do not compile Lean or establish mathematical correctness.

## Consolidation history

The consolidation used a label- and formula-level inventory of all six inputs.
The inventory found 394 labels occurring in more than one source. Closely
related material was grouped, common statements retained once, and alternate
proofs preserved where they explain a different mechanism. The manuscript's
concordance chapter contains the mathematical contribution map.

The historical consolidation also repaired fatal TeX superscript errors left
by the notation migration, expanded the Bell upper-bound proof and its finite
verification, supplied missing analytic prerequisites for the polygamma
discussion, integrated thirteen donor-only results, and normalized notation.
These editorial and human-proof changes do not by themselves constitute Lean
formalization.

## Current coefficient-calculus campaign

The six new leaves contain **25 public theorems: five compiled and twenty
pending compilation**. `NewtonReciprocal` has passed focused compilation.
`StirlingSymmetricFunctions`, `LagrangeInversionUniqueness`, and
`StirlingSecondReverseRowIdentity` have independent source/API reviews.
`ExponentialRiordanInverse` and `LagrangeExistence` are in the current review
queue. All five remaining leaves await successful compilation.

The first Lagrange uniqueness compilation attempt reached the default heartbeat
limit while inferring an inverse witness. The correction supplies explicit
proof data and awaits retry; the statement and heartbeat limit are unchanged.
Separately, thirteen existing helper/existence theorems in `LagrangeInversion`
now have weaker coefficient-ring assumptions and have passed direct compilation.
They are not counted among the twenty-five new theorems.

The manuscript currently contains 209 theorem-like entries: **64 `Lean`,
36 `partial`, and 109 `none`**. The latest claim audit corrected overclaims in
the Abel and Fréchet crosswalks and confirmed the second-kind Stirling
set-partition counting interpretation through
`BellSetPartitions.card_setPartitions`. That correspondence uses upstream
validation evidence; this campaign has not freshly compiled the counting
module. The in-document register remains authoritative, and a compiled source
module does not automatically certify every assertion in a broader theorem.

The campaign repairs the Laplace theorem's analytic assumptions and remainder
proof, removes contradictory duplicate crosswalks, and corrects boundary and
coefficient-ring assumptions. Detailed statements, proofs, and declaration
names belong in the TeX exposition. The status file tracks the still-open
analytic and combinatorial interpretation work without maintaining a second
claim register.

## Inherited focused-validation receipts

These are receipts from their named source checkpoints, not a fresh aggregate
build of the current merged corpus. The campaign status preserves the pinned
merge and validation history.

| Source surface | Recorded receipt and scope |
| --- | --- |
| `AppellSequence` | Eleven public lemmas passed direct sequential compilation; the caller refactor in `FinitePrefixThueMorseCollapse` also passed its own direct check. |
| `StirlingCompleteHomogeneous` | Eight public theorems passed focused compilation. The campaign's duplicate second-kind evaluation formulas were removed in favor of this shared API. |
| `ExponentialRescaling` | Four public lemmas passed focused compilation; existing `NorlundDiagonal` helper names were retained through the shared API. |
| `AbelPolynomialSeries` | A focused source build passed. Coverage of the entire canonical Abel statement remains subject to its current claim audit. |
| `GridEvaluationCertificate`, `IntegerCRTCertificate` | Nine public theorems compiled with the standard project axiom set; their human statements and proofs are grouped in the manuscript's two certificate theorems. |
| `BernoulliFormalLog`, `NorlundGeneralized` extensions | Source/API reviews were recorded; their compilation and affected-dependent closure remain separate outstanding work. |

The moment-cumulant crosswalk retains its normalization and degree boundaries.
The second-kind Stirling set-partition cardinality bridge is established;
weighted per-profile interpretations, surjections, cycles, and descents retain
their separate formalization obligations.
The Nörlund and Bernoulli discussions distinguish formal coefficient algebra,
coefficient-ring transport, multiplicity interpretations, and analytic
convergence. The certificate discussion distinguishes deterministic
certificates from probabilistic testing. These boundaries are maintained in
the exposition and must be preserved through later coverage upgrades.
