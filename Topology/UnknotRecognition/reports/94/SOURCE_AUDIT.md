# Source review and provenance

Date: 12 October 2026.
Reference revision returned by the connected GitHub branch read:
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`.

This package is new work in a local working directory. No commits, pull requests,
production patches or other writes were made to ProveIt.

## Repository reads

The connected GitHub tool was used to inspect:

- `Topology/UnknotRecognition/README.md` from moving `main` before the reference
  branch read. Its earlier missing-parallelity wording is superseded by the newer
  parallelity article; we do not treat that earlier summary as the final status.
- `Topology/UnknotRecognition/synthesis/cut_cells.tex` from moving `main`: full raw
  CW source charts, binary interval incidence, retained self-identifications,
  homology/ball distinction and the declared interface names.
- `Topology/UnknotRecognition/synthesis/boundary_shellings.tex` from moving `main`:
  existing homeomorphism-preserving embedded boundary shellings and source replay.
- `Topology/UnknotRecognition/synthesis/parallelity.tex` at the reference revision:
  all-dimensional source parallelity, the 30T inherited-core bound and the explicit
  admissibility distinction.
- `Topology/UnknotRecognition/reports/README.md` at the reference revision: a
  substantial retrieved prefix of the report catalogue, not every archived report.
- Directory listings for the synthesis and incoming directories, and a retrieved
  prefix of `docs/incoming/README.md` containing intake and placement instructions.

Earlier moving-branch source reads were not subsequently claimed to be byte-for-byte
checked against the reference revision. This is a targeted source review, not a
complete checkout or audit of native implementation code.

The four visible incoming archive names were:
`ProveIt_Disconnected_Tile_Kernels_2026-10-12.zip`,
`ProveIt_Moment_Coded_First_Returns_2026-10-12.zip`,
`ProveIt_Unknot_Hierarchy_Kernels_2026-10-12.zip`, and
`ProveIt_Unknot_Sparse_Cut_Grammars_2026-10-12.zip`.
These binary archives were not extracted in this session. A prior PDF of the
moment-coded first-return report was retrieved through the user's Library. Its
abstract, interface discussion and claim ledger were inspected; no claim of a
complete archive review is made.

## External primary sources

- Oxford Mathematical Institute's 2021 announcement:
  https://www.maths.ox.ac.uk/node/38304
- Marc Lackenby, arXiv:2607.23350v1, especially Sections 9, 10 and 14:
  https://arxiv.org/html/2607.23350v1
- Robin Forman, A User's Guide to Discrete Morse Theory:
  https://www.mat.univie.ac.at/~slc/wpapers/s48forman.pdf
- Adiprasito, Benedetti and Lutz, arXiv:1404.4239, including the explicit statement
  of Whitehead's PL collapsible-manifold implication:
  https://arxiv.org/pdf/1404.4239
- Lackenby's 2021 lecture slides were consulted but are not redistributed.

These sources establish the historical objective and classical topological
background. They do not supply the modular certificate compiler or the claimed
fixed-coordinate lower bound. The report does not assert exhaustive priority.

## Execution scope

Only this package's code and tests were run. There was no production checkout,
native recognizer execution, Regina comparison, native AHT benchmark or upstream
suite rerun. The stored source-specific prism JSON was replayed with synthesis,
offset solving and expansion disabled. Large binary tests disable expansion.

The first annulus test incorrectly expected an optimal critical vector (1,1,0,0).
The actual deterministic free-face base producer leaves a three-edge cycle, giving
(3,3,0,0). The test expectation and manuscript were corrected; the acyclicity and
non-point-collapse conclusions were unchanged. The final retained run is clean.

A benchmark rerun interrupted by the execution time limit was replaced by a fully
completed rerun; only the latter supplies `benchmark.json` and the article tables.
All seven measured rounds for each retained case are present.
