# Source audit and limitations

Reference revision: `74de08949619863b002b5fcf01813a2faddde212` (GitHub commit read
on 12 October 2026; recorded commit timestamp 22:48:08Z).

The GitHub connector was used to inspect the main unknot README, its synthesis
introduction, the report catalogue through report 105, report 96's README and
article entry point, and the complete report 96 fixture module. Initial reads
used the moving main branch; a later article-entry-point read used the exact
revision. This is not represented as a full checkout or complete repository audit.

Inspected blob identifiers:

| Path relative to `Topology/UnknotRecognition` | Returned Git blob |
| --- | --- |
| `README.md` | `4fb929b5689d0bc20327e241cb775789660c8013` |
| `synthesis/report.tex` | `059e1b99e17f2e9896413e4527350f6f68425a60` |
| `reports/README.md` | `73dd14219d13e2aed58c0c12b026c0c9406eb1d5` |
| `reports/96/README.md` | `62f03dd7e3f1f2aa34fcbbaff6f89c9509d64272` |
| `reports/96/article/article.tex` | `bd7b2c006fc5e71deda79b0c102d25d119d94c88` |
| `reports/96/scalar_separators/fixtures.py` | `246c74562195b51559ac9258e85e68af82c3ab84` |

The source fixture definitions and their face-arc/Euler conventions are adapted
with attribution from the last file. The package has no dependency on upstream
runtime modules. Reciprocal face pairings are checked; all manifold links and
knot-diagram ancestry were not independently checked by this delivery.

The incoming directory showed four ZIPs:
`ProveIt_Exceptional_Rows_2026-10-12.zip`,
`ProveIt_Matroidal_Dual_Forests_2026-10-12.zip`,
`ProveIt_Nonlinear_Activation_Forests_2026-10-12.zip`, and
`ProveIt_Ordered_Interface_Kernels_2026-10-12.zip`.
Their metadata and intake documentation were read. Available binary fetch routes
did not provide the ZIP contents, and container network retrieval failed. No
assertion of complete overlap review of those archives is made. Filenames alone
were not used as evidence for their mathematical content.

Primary literature checked online included Lackenby's 2021 slides and July 2026
preprint, Burton--Paixão--Spreer's normal-surface complexity paper, the
Adler--Monteiro parametric-LP publication page, and Karp's original chapter page.
Section 9 of the 2026 Lackenby paper was visually inspected. These external
sources are cited in the article; no copyrighted upstream PDF or font file is
redistributed.

No native ProveIt suite, Regina run, full knot-diagram benchmark, formal Lean
proof, repository write, patch application, or background task was performed.
The tests, oracle comparisons and timings in `evidence/` concern the delivered
standalone code and explicitly described source fixtures.
