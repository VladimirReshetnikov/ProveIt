K215 PROOF SIMPLIFICATION: SHARED IMPLICATION AND CANDIDATE SCHEDULING
==================================================================
Date: 2026-10-22
Repository: https://github.com/VladimirReshetnikov/ProveIt
Baseline: 57541fe0cfe3af62b4cb58747d8d1d7c16b338d5

START HERE
----------
Read report.pdf (or the standalone report.tex). This is a proposal with checked
component implementations and reviewable production patches. It changes proof
organization, not the 215-state machine or the target consistency statement.

The first recommendation is to share the implication derivation. The second
is to share the candidate-search induction where multiple enumerators can use
it. The paper distinguishes immediate source reduction from structural reuse,
and separates completed implementation from proposed decoder work.

The shared six-goal implication graph is existing ProveIt work from commits
3a7a61ee973a32777f2c5e07b8a304e6f4418b37 and
49e99c5b7cc6c2e164331961de28bad3904361fd. The retained sources at the baseline
still used the older proof pair. This packet reconciles that existing work
with the actual baseline and its producers. Earlier shared-proof-core,
checked-transport and further-interface proposals are credited in the paper.

CONTENTS
--------
report.tex, report.pdf          Complete mathematical and engineering proposal.
lean/                          Self-contained combined Lean sources and checker.
rocq/                          Self-contained combined Rocq sources and checker.
patches/                       Four ordered production patches.
integration/                   Portable patch/producer checker and its evidence.
components/lean_implication/    Focused shared-basis patch, overlays and evidence.
components/lean_scheduler/      Four enumerator overlays, kernel and source audit.
components/rocq_scheduler/      Constructive scheduler and current-source adapters.
  implication/                 Shared Rocq implication core, adapter and producer.
evidence/                      Baseline closure inventory, source review and QA.
scripts/build_report.py        Rebuild report.pdf in a temporary LaTeX directory.
MANIFEST.sha256                Exact delivered-file hashes (excluding itself).
LICENSE.ProveIt, LICENSES/,    Inherited license and source-scope notices.
THIRD_PARTY.upstream.md,
NOTICE.txt

No compiled Lean/Rocq objects, toolchain binaries, caches or failed development
experiments are included. Logs and receipts contain the actual execution paths
used for validation; the supported reproduction commands below use explicit
portable paths.

RESULTS WITH PRECISE SOURCE BOUNDARIES
------------------------------------
Lean implication proof pair:
  811 -> 401 lines; 42,454 -> 18,243 bytes (24,211 bytes saved).
All six changed production files for that integration, including producer,
renderer, plan and template:
  1,747 -> 1,343 lines; 80,277 -> 55,874 bytes (24,403 bytes saved).

Lean four scheduler clients plus the new core:
  2,666 -> 2,659 lines; 109,663 -> 109,339 bytes (324 bytes saved).
  Sixteen separately maintained inductive proofs become three shared proofs.
  K215 EnumPerm alone plus the new core grows by 95 lines / 3,411 bytes.

Rocq implication module replaced by generic core plus numeric adapter:
  1,169 -> 353 lines; 22,673 -> 17,449 bytes (5,224 bytes / 23.0% saved).
Rocq scheduler clients plus new core:
  410 -> 511 lines; 18,100 -> 21,625 bytes (3,525 bytes added).
Both Rocq refactors together, counting each proof module once:
  1,579 -> 864 lines; 40,773 -> 39,074 bytes (1,699 bytes / 4.2% saved).

Counts include comments and whitespace. Documentation, audit scripts, retained
historical evidence and duplicated template copies are outside proof-module
comparisons unless explicitly included. These are not full-repository sizes,
compiled proof-term sizes, timings, or reductions in machine states.

REPRODUCE THE COMBINED PROOF CHECKS WITHOUT A REPOSITORY CHECKOUT
-------------------------------------------------------------
Requirements: Python 3.10+ and the relevant complete proof-assistant install.
No network, Lake project, Mathlib, or downloaded project objects are needed.
Choose fresh output directories outside this packet.

Lean (validated with Lean 4.32.0):

  python3 lean/check.py --lean /path/to/lean-4.32.0/bin/lean \
      --out /tmp/k215-lean-check

Rocq/Coq (validated with Coq 8.18.0 / OCaml 4.14.1):

  python3 rocq/check.py --coqc /path/to/coqc --coqchk /path/to/coqchk \
      --out /tmp/k215-rocq-check

The Rocq checker retains the original production sources and makes an explicit
Stdlib -> Coq import-namespace substitution only in build copies for Coq 8.x.
Both original and compiled hashes are recorded. This is a compatibility check;
the production-designated Rocq 9.1.0 / rocq-stdlib 9.0.0 lane still needs its
own acceptance run at integration. See rocq/README.md for exact driver options.

Both drivers verify source hashes before compiling into isolated fresh object
trees. The accepted standalone Lean run covers 22 modules, 14 shared-basis
typed clients, 10 scheduler typed clients and the counterexample. The accepted
standalone Rocq run covers 12 modules plus Client, nine closed assumption
reports, and recursive coqchk. The generic implication core and counterexample
are axiom-free. Lean scheduler/concrete clients retain their documented standard
axiom profiles. Six existing TarskiComplete linter warnings are retained.

PRODUCTION PATCH REVIEW AND PRODUCER REPLAY
-----------------------------------------
Run the following against an unmodified checkout of the pinned baseline:

  python3 integration/check_patches.py --repo /path/to/ProveIt \
      --patches patches --out /tmp/k215-integration-check

This checks the baseline and patch hashes, creates a temporary minimal copy,
applies all four patches there, verifies 13 checked proof-source hashes, and
replays the relevant producers. It checks three Lean basis outputs, both Lean
enumerator variants and five Rocq calculus outputs byte-for-byte. It does not
modify the original checkout. Keep integration/check_patches.py,
integration/integration_manifest.json and integration/check_rocq_producer.py
together.

Apply production patches in this order after reviewing them:

  01_shared_implication_lean.patch
  02_scheduler_lean.patch
  03_scheduler_rocq.patch
  04_shared_implication_rocq.patch

For example, from a suitable ProveIt checkout, with PACKET set to this packet's
absolute directory:

  git apply "$PACKET/patches/01_shared_implication_lean.patch"
  git apply "$PACKET/patches/02_scheduler_lean.patch"
  git apply "$PACKET/patches/03_scheduler_rocq.patch"
  git apply "$PACKET/patches/04_shared_implication_rocq.patch"

The mechanisms are mathematically independent, but patch 04 intentionally
follows patch 03 because they share producer/manifest paths. Patch 04 also
depends on patch 01's exact six-goal parser and proof data. Applying only the
shorter generated sources without their producers is not a supported variant.
The patches affect 23 distinct production paths. Their application and producer
replay were checked together; see integration/evidence/receipt.json.

For inclusion as a proposal packet in ProveIt, a suitable destination is:

  Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/
  simplification/proposals/shared-mechanisms/

The packet has not been committed or pushed to the repository. No production
source was modified during the checks.

ACCEPTANCE BOUNDARY
-------------------
The complete physical-machine-to-ZFC endpoint was not rebuilt for this proposal.
Before adopting the production patches, run the repository's designated Lean
and Rocq acceptance gates for affected descendants and the endpoint clients,
and record new transitive source/object bindings. Existing checkpoint receipts
remain historical evidence for their exact old sources.

The exact retained endpoint is the external proof-assistant equivalence between
BlankHalts machine215 and BProv ZFCax_s [] Form.fBot, with the nonhalting theorem
obtained by negation. This packet does not supply a separately encoded proof
inside ZFC or PA, prove unconditional consistency/nonhalting, establish machine
minimality, or complete the proposed decoder route/clock factoring.

The scheduler's complete_at fixes one target before quantifying over reachable
boundary payloads. lean/src/QuantifierCounterexample.lean checks that the weaker
payload-wise cofinality condition can hold along a forever nonhalting search.
Generalized completeness works from arbitrary states; generalized equivalence
still requires the maintained soundness invariant.

DOCUMENT AND ARCHIVE CHECKS
---------------------------
Rebuild the standalone LaTeX report:

  python3 scripts/build_report.py --out /tmp/k215-report.pdf

This uses pdflatex twice in a temporary directory. The source includes its
bibliography and final measured values; no external metrics.tex is needed.
The delivered PDF was compiled and all pages were rendered for visual review.

Verify delivered file hashes from the packet root:

  sha256sum --check MANIFEST.sha256

Source and producer receipts are evidence about the specific scopes they name.
The renderers, generators and Python checks remain outside the trusted logical
kernel: their emitted theorem proofs are checked by Lean and Rocq/Coq.
