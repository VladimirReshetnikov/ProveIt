# reports

The six original archives and their extracted contents. Each ZIP had a single
wrapper directory, which was removed; the numbering follows the archives'
modification times.

| Dir | Archive | Package | Complete recognizer | Hierarchy components | Tests |
|---|---|---|---|---|---|
| `01/` | `unknot_recognition_implementation.zip` | `unknot` | grid diagrams, Dynnikov moves, replayable certificates | ball-pattern test, rational H^1, cocycle-dual normal coordinates, potential | 40 |
| `02/` | `unknot_recognition_partial_implementation.zip` | `unknotlab` | descending test, determinant, reduced Khovanov cube over F2 | face-pairing triangulations, normal coordinates, ball-pattern test, potential | 64 |
| `03/` | `unknot_workbench.zip` | `unknot_lab` | determinant, Khovanov cube with default ceilings | bond-enumeration pattern test, conditional bound arithmetic | 49 |
| `04/` | `unknot_recognition_partial.zip` | `unknot` | Khovanov cube, Knot Atlas fixtures | dual-4-connectivity pattern test, potential | 62 |
| `05/` | `unknot_recognition_partial_implementation (1).zip` | `unknot_recognition` | Reidemeister I/II traces, determinant, Khovanov cube | bond-enumeration pattern test, simplicial normal coordinates, pattern complexity | 58 |
| `06/` | `unknot-recognition-implementation.zip` | `unknot` | Khovanov cube, 11-crossing fixtures, report verifier | bond-enumeration pattern test | 45 |

Every archive contains a README, a LaTeX report with PDF under `docs/`,
examples, recorded results, and a standard-library-only Python package. All
six test suites pass on CPython 3.14 (`python -m unittest discover -s tests`
from the archive directory). All six reports state that the requested
`n^O(log n)` implementation was not achieved and explain why; the synthesized
review of them is `../synthesis/report.pdf`.

Cross-validation of the archives against each other (five Khovanov
implementations, six pattern testers, the grid search of `01/` against the
Khovanov homology of `04/`) is in `../synthesis/data/`.
