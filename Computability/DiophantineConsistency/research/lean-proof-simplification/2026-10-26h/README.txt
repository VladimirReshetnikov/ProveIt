LEAN PROOF SIMPLIFICATION REVIEW
Prepared for Vladimir Reshetnikov, 26 October 2026

Read lean-proof-simplification-review.pdf for the complete analysis.
The matching .tex file is self-contained and builds with XeLaTeX.

SOURCE SNAPSHOT
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 60e9c5d620c6c387d932876cfa2d9376f64ea56c
Lean: leanprover/lean4:v4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997
Requested subtree: Computability/DiophantineConsistency

WHAT TO INTEGRATE FIRST
1. patches/list-lookup.patch: seven direct uses of existing Lean list lemmas;
   61 -> 21 lines across the changed declarations. Full replay of ProofChecker;
   exact polymorphic replacement propositions checked for all seven sites.
2. patches/decoder-options.patch: two independent decoder proofs, 55 -> 43
   lines; full-file replay, exactly matching original per-theorem axiom lists.
3. patches/assignment-transport.patch: 260 -> 242 lines including two shared
   helpers; full replacement file checked and expression fields checked by rfl.
4. patches/finite-residuals.patch: 33 net physical lines saved including a new
   36-line support module; all eight replacements and 15 overlay commands pass.
5. patches/pell-residue-casts.patch: 248 -> 241 lines; complete original and
   replacement files checked, matching selected theorem/endpoint axioms.

The patches above affect distinct files and can be reviewed independently.
They preserve executable definitions and public theorem statements, apart
from adding the shared helper declarations needed by their proofs. No change
has been pushed to the upstream repository.

OPTIONAL, CHECKED TRADEOFFS
- patches/optional/coefficient-bounds-compact.patch: 679 -> 122 lines, with
  unchanged public statements and coefficient data. Full original/new files
  compile. The combined proof needs a local 4,000,000-heartbeat budget and was
  substantially slower in the recorded single-run comparison. See the report
  and evidence/arithmetic for exact diagnostic timings. It is not a speedup.
- patches/optional/decoder-fusion.patch: an alternative to decoder-options,
  NOT an additional patch. The fused proof compiles and is shorter, but its
  depth projection inherits Classical.choice. The independent Option-based
  patch preserves the original axiom separation and is the default choice.

CHECKED PROTOTYPES, WITH CLIENT MIGRATIONS STILL TO DO
lean/ScanIteration.lean and lean/ValidatedHistory.lean prove shared scanner
and history laws, including explicit bridges from concrete recursive shapes.
lean/RunInvariant.lean checks a common topological evaluation invariant and
both nonnegativity/degree applications. lean/SmallArithmetic.lean and
lean/BasicNat.lean check exact small arithmetic examples. AssignmentTransport
and FiniteResiduals expose reusable proof interfaces and paired audits.

Generated power tables, weighted-degree/cost consolidation, cyclic-word
interfaces, and Object completeness/sealing are architectural proposals.
They are explained in the report and are not presented as completed migrations.
No failed experimental proof is included as an accepted candidate.

REPLAY
Use a checkout at the exact commit, with its pinned Lean toolchain on PATH.
If needed, prepare its dependency cache in the usual way (lake exe cache get).
The verifier does not change source files or apply patches.

  python3 scripts/verify.py /absolute/path/to/ProveIt --level core
  python3 scripts/verify.py /absolute/path/to/ProveIt --level prototypes
  python3 scripts/verify.py /absolute/path/to/ProveIt --level full --build-prerequisites

Add --include-optional to replay the compact coefficient and fused decoder
experiments too. The default level is full; optional experiments are excluded
unless explicitly requested. Logs go to replay-logs in the caller's working
directory, or to the path supplied by --logs.

The full level also runs scripts/verify_shared_patch.py through lake env.
It creates a temporary Lean overlay, checks the four patched residual modules,
recompiles eight unchanged dependencies against them, and runs three original
audit files. It never writes through symlinks to the checkout's build outputs.
This is a targeted integration replay, not a build of every dependent module.

For independent source inventory reproduction:
  python3 scripts/inventory.py /absolute/path/to/ProveIt /path/to/inventory-output

For the report:
  xelatex -interaction=nonstopmode -halt-on-error lean-proof-simplification-review.tex
  xelatex -interaction=nonstopmode -halt-on-error lean-proof-simplification-review.tex
The fonts are Latin Modern Roman, DejaVu Sans, and DejaVu Sans Mono. Standard
LaTeX packages used include fontspec, fvextra, xurl, hyperref, and booktabs.

EVIDENCE AND LIMITS
- evidence/source-inventory.* records exact filenames, byte/line counts, and
  hashes for the 546 files in the maintained Lean tree.
- evidence/verification-plan.json lists reproducible checks and checksum pins.
- evidence/{syntax,structural,arithmetic}/ contains topic receipts and logs.
- evidence/validation-summary.json is the consolidated status record.
- SHA256SUMS.txt records package integrity hashes.

All reported source reductions are local and explicitly scoped. They are not
repository-wide savings, proof-term measurements, or smaller Diophantine
constructions. The source survey is textual, not a Lean parser or axiom audit.
Compiler exit status must be zero before axiom output is accepted: a failed
proof can still produce misleading subsequent diagnostic output.

The main source checkout was not edited. Full replacement checks generally
use original compiled imports; the residual overlay provides the additional
integration replay described above. The entire 546-file maintained tree and
all dependents of the combined patch have not been rebuilt. Follow that gate
when integrating into the live repository.

The original source license is reproduced in LICENSE.txt.
