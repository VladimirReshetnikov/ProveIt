# Source and provenance record

## Observation date and scope

Research and source observations: 12 October 2026.
Observed ProveIt `main` commit:
`6207c3d40047fd8d1400a4d509fee71c9a3a8132`.
Commit timestamp: `2026-10-12T13:47:03Z`.
Commit message: `New research reports`.

Initial directory/index reads were on `main`. The later critical-Hahn TeX
read was pinned to this observed commit. This is **not** an atomic full-tree
checkout or an exhaustive source audit. Blob identifiers below record source
provenance, not a demand to rewrite delivery checksum ledgers.

## Repository sources inspected

| Path | Read scope | Returned blob identifier |
| --- | --- | --- |
| `Analysis/Polylogarithms/README.md` | Source lines 1–190 | `5b4902718f97704a762739516c0abbd8bc18926b` |
| `Analysis/Transseries/README.md` | README response | `fc60650928928cfef3203df5dd06e94a519fa68e` |
| `Analysis/Transseries/docs/series-and-transseries/README.md` | Source lines 1–220 | `b0f627c03c6f9e6aee9670d90cfa3a34c30710ad` |
| `docs/incoming/README.md` | Source lines 1–145 | `9956ad83c5ddfa3c75e5f2946481a83082bc81e8` |
| `Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/README.md` | Full returned README, including editorial updates | `7d138677987dd1cc6dbfdf5df1aa564bfd08d5dd` |
| `Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex` | Source lines 1–150, pinned to the observed commit | `c64869335a671096cb23bf9c6044b9e24aa66bdf` |

The three requested directories and the incoming commit metadata were also
read. Five archive names were observed:

- `ProveIt_Resonant_Polylog_Transseries.zip`
- `ProveIt_Resonant_Polylogarithm_Inversion_2026-10-11.zip`
- `Resonant_Polylogarithm_Transseries.zip`
- `polylogarithm_resonance_and_inverse_transseries.zip`
- `polylogarithm_transseries_research.zip`

Their complete binary contents were **not** all decoded and compared.

## The precise predecessor used

Title: *Resonant Polylogarithm Transseries: Gamma Borel Kernels, Cyclotomic
Order Jets, and Sharp Dilogarithm Reversion*.
Date: 11 October 2026.
Inspected Library TeX filename: `article(20261012-044824).tex`.
Source ranges read: 1–1000 and 1030–1487.

Relevant statements:

- Theorem 9.1 proves the interior-fold quadratic-feedback result.
- Section 12, Question 1 explicitly leaves the strict and critical boundary
  regimes open, proposing the constant now proved in Theorem 5.1 here.
- Earlier sections contain the positive finite coefficient formula and the
  sharp dilogarithm reversion theorem. Neither is claimed new here.

The Library copy was not byte-compared with an archived member of
`docs/incoming/Resonant_Polylogarithm_Transseries.zip`. The exact title and
mathematical statement identify the target, but byte-level archive provenance
is not asserted. Library searches for related quadratic boundary material
primarily returned this same question; they do not establish the absence of
all overlapping material.

## External primary/reference sources

- NIST DLMF, §25.12, especially 25.12.12:
  https://dlmf.nist.gov/25.12 . Successful text read of the expansion and its
  conditions. Source of the classical polylogarithm continuation identity.
- NIST DLMF, §4.13: https://dlmf.nist.gov/4.13 . Lambert branch definitions
  and asymptotic information. A successful earlier text read was followed
  by intermittent failed reopens; the branch used in the paper is defined
  independently by the large solution of its implicit equation.
- NIST DLMF, Chapter 5: https://dlmf.nist.gov/5 . Bibliographic reference for
  classical Gamma recurrence/duplication and polygamma identities; no claim
  of a chapter-wide read. The needed half-integer identities are also
  derived from recurrence in the proof and exact checks.
- Flajolet and Odlyzko, *Singularity analysis of generating functions*,
  SIAM J. Discrete Math. 3 (1990), 216–240, DOI 10.1137/0403019.
  The publication was identified in searches; direct full-text retrieval
  failed. The manuscript explains the finite local transfer calculation and
  does not represent this reference as fully re-audited.
- Flajolet and Sedgewick, *Analytic Combinatorics* (2009), Chapters VI–VII.
  Classical background citation, not a newly executed full-book audit.
- Janson, *Simply generated trees, conditioned Galton–Watson trees, random
  allocations and condensation*, Probability Surveys 9 (2012), 103–252:
  https://arxiv.org/abs/1112.0510 . Publication record and abstract inspected
  to identify the established probabilistic setting. No probability limit
  theorem from the survey is used without the separate analytic arguments
  supplied in this article.

Targeted searches did not establish worldwide priority for the explicit
quadratic constants, charts, or coefficient refinements. The title-page
research-status statement preserves this limit.

## Corrections and boundaries

No new mathematical error was established in accepted inspected claims.
The predecessor's boundary status changes from a proposed fixed-parameter
law to a law proved in this new manuscript, subject to independent review.
The existing interior theorem is not invalidated. Uniform joint limits,
full incoming-corpus overlap, interval certification, and proof-assistant
formalization are not claimed.
