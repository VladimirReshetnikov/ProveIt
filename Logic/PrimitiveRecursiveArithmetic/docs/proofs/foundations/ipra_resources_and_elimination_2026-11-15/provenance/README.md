# Source and reuse record

## Snapshot and review scope

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit: `b0f6f535ffc16324683fef2c263260a88ae03755`

The source inventory records the exact files consulted for the framework comparison, selected obstruction reports, API inspection, and reused dependencies. Each entry includes a pinned URL, Git blob identifier, byte count, and SHA-256. It is a provenance record, not a certification of all statements in an inspected source. The packet inventory records the 60 immediate research-packet directories; inclusion in that inventory does not imply a substantive proof audit.

## Reused mathematical and software ingredients

- Bounded Booleanization, finite observations/contracts, demand scheduling, finite root scans, conditional arithmetic operations, and height/list distinctions already occur in the repository frameworks. They are credited in the report.
- `lean/BackwardDemand.lean` is an unchanged copy of the earlier finite-demand packet's semantic development.
- `lean/ObjectKernel.lean` reuses the coherent-methods packet's standalone concatenation of the repository's `Syntax.lean`, `Deduction.lean`, and `PR.lean`. Only its surrounding provenance comment was changed. The source sections agree with the pinned upstream files after import lines and boundary whitespace are removed; see `lean/validation/source_audit.json`.
- The TeX build script adapts the earlier `ipra_framework/paper/build.sh` fallback for the available TeX installation.
- The newly written compiler modules, fixed-dimensional fuel syntax, concrete plane-elimination definitions, human proof extensions, and Python references are identified in `CLAIMS.json` and `lean/README.md`.

## External mathematical background

The report gives its own elementary proofs of the required length bound, total-degree resultant bound, fibre multiplicity, and enumeration theorems. It cites the following for broader context, not as substituted proofs of these exact arithmetic claims:

- Sylvain Schmitz, *Complexity Bounds for Ordinal-Based Termination* (2014), <https://arxiv.org/abs/1407.5896>.
- Bernd Sturmfels, *Solving Systems of Polynomial Equations* (2002), Chapter 4, <https://math.berkeley.edu/~bernd/cbms.pdf>.

## Review and verification limits

The mathematical chapters and their claim calibration received separate cross-reviews. The actual Lean build, source comparison, and axiom audit are logged. The executable arithmetic checks validate selected finite examples only. There is no complete verification of all research packets, no claim of a general semantic-to-iPRA reflection theorem, and no completed object proof of the plane-intersection or lexicographic termination theorems.
