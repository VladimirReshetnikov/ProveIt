# Bounded source and priority audit

## Repository observation

Repository: https://github.com/VladimirReshetnikov/ProveIt

Last observed `main` commit:
`cbfbc3163e0d038a381808c6db8d39ea12dc0db7`.
Its returned timestamp was `2026-10-12T04:06:59Z`, corresponding to 11 October
2026 in the user's Pacific time zone. The article date is the local research
date. Repository reads used the connected GitHub tools; no remote writes were
performed. Some initial reads were made on `main` before the final commit
observation. This is **not an atomic checkout or an exhaustive full-tree audit**.
Search indexes also surfaced older snapshots, notably prefixes `4722893a2320`
and `25f0d079100e`.

## Inspected material and scope

| Source path | Actual reading scope | Recorded Git blob / ref |
|---|---|---|
| `Analysis/Transseries/README.md` | Project overview | `fc60650928928cfef3203df5dd06e94a519fa68e`, initial `main` read |
| `Analysis/Polylogarithms/README.md` | Substantial initial portion, including the accepted/evidence/pending distinction; large response truncated | Blob not retained; initial `main` read |
| `Analysis/Transseries/docs/series-and-transseries/README.md` | Selected initial index text and source lines 300–590, not every package entry | Initial `main` reads |
| `Analysis/Polylogarithms/docs/articles/polylog-polygamma-bridge.tex` | Source lines 1–220 requested; initial article/DFT discussion read, response end truncated | Initial `main` read; blob not retained |
| `Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex` | Source 180–370 (contour proof, certificate, countable family, actions, flows), then 1–110 (title, abstract, context) | `1e8b24325554d1f1c94c29f21b794ba62feff755`; latter read pinned to the observed commit and returned the same blob |
| `Analysis/Transseries/docs/series-and-transseries/Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/README.md` | Full returned README including editorial continuations | `7d138677987dd1cc6dbfdf5df1aa564bfd08d5dd`, pinned to the observed commit |

The original PolyLog bridge article is historical material. Its original
rhetorical novelty/independence wording is not used to override the current
project's claim-status ledger. In particular, a numerical failure to find a
relation is not treated as proof of arithmetic independence.

Search queries included `polylogarithm transseries resonance`, `Sommerfeld`, and
`Stokes_Transport` within the repository. Results guided the scoped reads above;
a search hit alone was not treated as a complete theorem. The full canonical
transseries volumes, every polylogarithm manuscript volume, and the complete
incoming archive collection were not audited.

## Overlap and attribution

The nonlinear Stokes-transport package already supplies the generic inverse
coefficient formula, contour proof, analytic certificate, and countable-family
qualification. Its title/abstract also explicitly identifies the nonlinear
real-averaging defect. The present general inverse certificate and averaging
calculation are specializations or explanatory restatements, not new general
engines. The actual proposed reversion contribution is the dilogarithm-specific
positive Laurent formula, exact radius, unique dominant singularity, full
coefficient constant, and necessary-and-sufficient physical threshold.

The critical-Hahn README concerns linear-core polylogarithmic feedback and
records many later boundary/endpoint developments. The present quadratic-core
interior-fold theorem is a related model, not a claim to have originated that
research direction or settled its complete boundary classification.

## External primary sources

1. NIST DLMF §25.12: https://dlmf.nist.gov/25.12
   Integral representation and classical polylogarithm/dilogarithm identities.
   HTML equations and surrounding conditions inspected.
2. NIST DLMF §5.5: https://dlmf.nist.gov/5.5
   Gamma reflection; HTML inspected.
3. NIST DLMF §5.11: https://dlmf.nist.gov/5.11
   Stirling, digamma asymptotics, and Gamma ratios; HTML inspected.
4. Gil, Segura, Temme, arXiv:2108.11210v2:
   https://arxiv.org/html/2108.11210v2
   Section 3/Lemma 3.1 and reference context inspected. The classical complete
   Fermi–Dirac expansion is prior work, not a new theorem of this contribution.
5. Garoni, Frankel, Glasser (2001), DOI 10.1063/1.1350634:
   https://doi.org/10.1063/1.1350634
   Institutional publication metadata/abstract inspected, not the full paper.
6. Flajolet, Odlyzko (1990), DOI 10.1137/0403019:
   https://epubs.siam.org/doi/10.1137/0403019
   Primary publisher metadata and abstract inspected. The paper's standard
   singularity-transfer method is used, after the present proof establishes
   the required model-specific continuation and unique dominant singularity.

Additional search queries included `"inverse dilogarithm" series convergence`,
`"Fermi-Dirac" "inverse" "convergent"`, and a threshold-specific dilogarithm
query. Results included numerical inverse-Fermi–Dirac work; no claim is made
that those searches excluded every earlier equivalent theorem. Irrelevant
search results were not used as technical sources.

## Priority boundary

No matching statement of the complete sharp dilogarithm reversion package was
identified in the sources actually inspected. This is a bounded negative search,
not a proof of novelty. Independent literature review should precede any formal
priority claim. The complete Sommerfeld expansion, Gamma/cosecant generator,
DFT, Lagrange inversion, square-root transfer, and general averaging obstruction
are all credited as established input.
