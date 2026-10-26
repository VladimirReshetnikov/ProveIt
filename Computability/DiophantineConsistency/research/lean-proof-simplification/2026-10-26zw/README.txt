THREE FURTHER LEAN PROOF SIMPLIFICATIONS FOR PROVEIT
26 October 2026

Read report.pdf, or rebuild it from report.tex and metrics.tex.

RESULTS

1. NativePellBootstrap.source_window_bound:
   A sharp integer upper bound R <= q^4 - q^3 - q - 1 follows from
   an explicit nonnegative deficit. The proof-only patch removes 14 lines.
   Sharpness concerns the reduced arithmetic constraints, not solutions
   of the entire Diophantine source system.

2. QuadraticBoolean.zero_certificate_sound and ObjectZeroTest.certificate_sound:
   Annihilation and balance already determine the zero-test selector.
   Both direct proofs explicitly clear the Boolean/idempotence conjunct.
   The two proof-only edits remove 13 lines. All literal rows stay in place.

3. CurrentControllerSubsets2011.block_base_isUnit:
   The actual base is a power of two modulo an odd number; exact order
   is unnecessary for this endpoint. The proof-only patch removes 3 lines.

Total: 30 physical lines removed across four current modules. No production
helper, import, public theorem statement, executable definition, witness count,
or polynomial row is added or changed. One explanatory comment is updated.
The general kernels are explanatory/checking artifacts, not production imports.

SOURCE AND NOVELTY CUTOFF

Repository: https://github.com/VladimirReshetnikov/ProveIt
Initial maintained source:
  3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114
Substantive exclusion review (43 prior packets, through zp and zq):
  60fcb2a69b7f1fdd4c3592ea5f164223cad50abe
Last checked main:
  09eaa57ae5b80130ddb0aa5344f71e638ebb3e97

The last comparison leaves all four patch targets and the 43 proposal packets
unchanged. Other maintained modules have advanced. The one later ADOPTION note
records already excluded list-lookup and predecessor-power simplifications.

All earlier proposals are treated as already applied for novelty, regardless
of their adoption/compilation status. The numerical line savings are measured
against actual pinned source, not a hypothetical merge of every alternative
historical patch. Evidence identifies the closest prior ideas and why these
three residual proposals differ.

WHAT WAS CHECKED

- Six standalone Lean files passed Lean 4.32.0 with mathlib commit
  81a5d257c8e410db227a6665ed08f64fea08e997, matching the repository manifest.
- Checked results include the deficit identity, bound, strict window,
  reduced-box sharpness, two-premise selector, direct certificate proofs,
  internal-carrier typeclass bridge, and actual controller modulus shape.
- RankSourceFixture and ControllerBaseSourceFixture contain the exact
  proposed production proof bodies. Existing upstream facts are explicit
  theorem parameters, not axioms. They check consumption of these facts.
- Printed axiom reports contain only propext, Classical.choice and Quot.sound
  where applicable. No sorry, admit, or added axiom occurs in the six files.
- All three patches pass git apply --check together against the pinned source.
- The unchanged declarations and all other code in the four proposed modules
  were compared with the baseline; exact hashes and metrics are supplied.

WHAT WAS NOT CHECKED

The complete four production modules and their full transitive project import
graphs were not rebuilt here. Full production integration and downstream client
checks remain a local acceptance gate. No runtime improvement is claimed, and
the controller cleanup does not remove the file's other uses of order theory.
No changes were written to GitHub.

CONTENTS

report.tex, metrics.tex, report.pdf
  Article source, exact metric macros, and the rendered 8-page article.

lean/
  Six independently checkable Lean files. They import only mathlib.
  They are not imported by the proposed production modules.

patches/
  rank-upper.patch
  zero-test-two-rows.patch
  controller-base-unit.patch

baseline/, proposed/
  Complete original and proposed copies of the four target files, under
  their actual repository paths. These facilitate review and comparison.

evidence/
  Source hashes, patch accounting, novelty audit, independent mathematics
  review, exclusion inventory, source-binding checks, freshness comparison,
  final validation metadata, compiler logs and PDF quality receipt.
  Some audit notes retain original analysis/ provenance paths. Their delivered
  counterparts are under lean/, baseline/, proposed/ and evidence/.

scripts/
  verify_sources.py  Check the bundle's code-only edits and optional checkout.
  replay.py          Recheck the six Lean files in an existing Lake project.
  build_report.py    Run pdflatex twice and retain errors on failure.
  verify_bundle.py   Verify every file against MANIFEST.sha256.

REPLAY WITHOUT EDITING A CHECKOUT

From the extracted archive directory:

  python3 scripts/verify_bundle.py
  python3 scripts/verify_sources.py --project /absolute/path/to/ProveIt
  python3 scripts/replay.py --project /absolute/path/to/ProveIt

The replay script requires an existing matching Lean/mathlib installation.
It does not install packages, apply patches, or change repository source.
It writes fresh logs under replay-results/ beside this README.

PROPOSED PRODUCTION INTEGRATION

First use a clean worktree or otherwise preserve local changes. Resolve the
archive directory to an absolute path. From the ProveIt checkout, review and run:

  git apply --check /absolute/path/to/packet/patches/rank-upper.patch /absolute/path/to/packet/patches/zero-test-two-rows.patch /absolute/path/to/packet/patches/controller-base-unit.patch
  git apply /absolute/path/to/packet/patches/rank-upper.patch /absolute/path/to/packet/patches/zero-test-two-rows.patch /absolute/path/to/packet/patches/controller-base-unit.patch

Then build the actual targets in the project's normal environment:

  lake build DiophantineConsistency.QuadraticBoolean
  lake build DiophantineConsistency.ObjectZeroTest
  lake build DiophantineConsistency.NativePellBootstrap
  lake build DiophantineConsistency.CurrentControllerSubsets2011
  lake build DiophantineConsistency.CurrentControllerSubsets2011Checks

Also run the repository's appropriate compiler/object and direct-client checks
for the accepted changes. These production commands are instructions for the
integration gate; their success is not claimed by this packet.

The patches are independent and may be adopted separately. If a target file
has changed since the recorded revisions, review the intervening diff and
adapt the proof manually rather than forcing a patch through a conflict.

REPORT REBUILD

  python3 scripts/build_report.py

This uses a standard pdflatex installation. Font/layout packages are declared
in report.tex. Rebuilding the PDF changes its file hash; regenerate a manifest
for any modified packet rather than treating the original checksum as valid.
