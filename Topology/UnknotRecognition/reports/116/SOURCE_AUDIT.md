# Source audit and research provenance

Targeted maintained source pin:

```text
d9456c5bdb94820bfa9e480e9ed73c10a769e59a
```

The GitHub commit response identifies this as the placement of ordered pivot interfaces, report 110, at 2026-10-12T23:21:50Z. Its placement message expressly separates intake from test execution and soundness review. The repository was changing during this task; the pin, not “latest main”, is the reproducible reference for the interface review.

## Inspected content

- `Topology/UnknotRecognition/README.md`: general exact recognizer status and compressed-geometry checkpoint. Contextual main-branch read.
- `Topology/UnknotRecognition/synthesis/cut_cells.tex`, first 250 lines: faithful source-chart raw cuts, encoded bit bounds, and remaining geometric obligations. Contextual main-branch read.
- `Topology/UnknotRecognition/fast/fastunknot/core_handlebody.py`, first 240 lines at the pin: source graph, cycle flags, saturated occurrences, private queue, and deferred full forest routines.
- `Topology/UnknotRecognition/reports/105/README.md` at the pin: full deferred primal forests, exceptional interfaces, native-data scope and integration contract.
- `Topology/UnknotRecognition/reports/108/CLAIMS.md` at the pin: exceptional activation/forest methods, read to avoid conflating that parameter with block rank.
- `Topology/UnknotRecognition/reports/109/README.md` at the pin: weighted ordered incidence interfaces and two-support specialization.
- Report 110's `CLAIMS.md` and `INTEGRATION.md` text exposed in the placement commit diff: existing weighted matching, prepeeling, contextual tables and repeat-safe powers.
- `docs/incoming/README.md`: intake, source pin, delivery preservation, and separation of placement from promotion.

These were targeted GitHub connector text reads. No full repository clone was available in the execution environment. No claim is made to have read every incoming archive body or all 110 reports. The implementation was written and tested as an independent standard-library packet, not as a native patch.

## Primary public sources checked

1. Marc Lackenby, *Unknot recognition in quasi-polynomial time*, March 2021 Oxford slides. Title page and main-theorem slide were visually checked. The displayed bound is `2^O((log n)^3)`, not `n^O(log n)`.
2. Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*, arXiv:2607.23350v1, July 25, 2026, 54 pages. Abstract, contents and Section 9 checked; printed page 34 visually inspected. The iteration analysis must not be represented as a full operation-cost bound.
3. Juhi Chaudhary, Ignasi Sau, Meirav Zehavi, *A Parameterized Perspective on Uniquely Restricted Matchings*, arXiv:2508.12004v1, 2025. Read the matching/triangularity discussion, classical cactus attribution, and treewidth statement.
4. Golumbic–Hirst–Lewenstein, *Uniquely restricted matchings*, Algorithmica 31 (2001), 139–154, DOI 10.1007/s00453-001-0004-z. Bibliographic/abstract information checked through authors' institutional publication records. Classical cactus tractability is explicitly attributed.

The targeted search did not establish absolute novelty of all algorithmic components. This article's contribution is stated as a self-contained cycle-block/path refinement of the inspected ProveIt continuation, with additional precise composition and output contracts.

## Review limitations

The source core shape adapter is tested on abstract dictionaries only. Its parity success is not geometric source authentication. Any native promotion must re-read current code and schemas, reconstruct real source data, run geometric replay, and measure all preparation/verification/downstream work. Prior reports' native counts are not presented as newly executed in this packet.
