SHARED IMPLICATION BASIS: CURRENT-HEAD INTEGRATION PROPOSAL
========================================================

Baseline: 57541fe0cfe3af62b4cb58747d8d1d7c16b338d5
Existing proof/renderer origin: 49e99c5b7cc6c2e164331961de28bad3904361fd
Earlier shared-six-goal change: 3a7a61ee973a32777f2c5e07b8a304e6f4418b37

This packet reconciles existing prior mathematical work with the checked sources
retained at the baseline. It does not claim a new implication derivation. The new
contribution is a reviewable current-HEAD patch, a consistent maintained producer,
and fresh component-level verification. No repository source has been modified.

The shared core proves unrestricted rho8, composition, prefix lifting, K, Peirce
and S under the existing abstract Language/Restricted interface. The numerical
DomRho8 adapter remains byte-identical. The Lukasiewicz namespace uses the same
core with domination defined to be True; its named Tarski bridge is byte-identical
to the baseline. Neither interpretation assumes implication injectivity.

EXACT SOURCE REDUCTION

DominatedImplication.lean: 13,723 -> 14,146 bytes; 287 -> 300 lines.
Lukasiewicz.lean:          28,731 ->  4,097 bytes; 524 -> 101 lines.
Combined proof pair:      42,454 -> 18,243 bytes; 811 -> 401 lines.
Net proof-pair reduction:  24,211 bytes and 410 lines.

Including every changed production file, the patch changes 80,277 -> 55,874
bytes and 1,747 -> 1,343 lines: 24,403 bytes and 404 lines saved. These counts
include the renderer, proof data, replacement producer and new adapter template.
They exclude new audit/build scripts and preserved historical evidence. They are
source measurements, not proof-term, trusted-kernel or endpoint timing claims.

SIX CHANGED PRODUCTION PATHS

1. Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean
2. Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean
3. Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py
4. Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py
5. Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/derivation_core.txt
6. Computability/BusyBeaver/Research/ZFC/k225-formal/dominated_implication_templates/lukasiewicz.txt

Two unchanged inputs are also included in overlay/ for self-contained production:
DomRho8.lean and dominated_implication_templates/adapter.txt. The patch does not
change them. Every before/after hash and measurement is in integration_metrics.json.

WHY THE PRODUCER ALSO CHANGES

The baseline generate_dominated_implication_lean.py pins the three-goal derivation
and a historical raw core. Merely copying the shorter shared proof pair would
break regeneration. Its replacement preserves the --out/--check/no-argument CLI,
pins the inherited renderer and six-goal derivation, reproduces the core, and
copies the two exact adapter templates. It now checks all three maintained Lean
outputs. The renderer recomputes condensed-detachment instances; its output is
then checked by Lean. Its execution, hashes, and diagnostics are not trusted as
mathematical evidence.

The optional legacy rho8cd --luk mode still renders the older independent
unrestricted derivation. It is not the producer of the maintained shared adapter.
The four legacy renderer modes (--rocq, --lean, --rocq-cd, --luk) retain exactly
their baseline output bytes; see producer_verification.json. In particular the
two proposed Rocq renderings are unchanged by this patch.

FRESH VERIFICATION

Lean 4.32.0, compiler commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Fourteen project modules plus SharedBasisAudit were compiled freshly and serially
in an isolated source/object tree. No precompiled project object was reused.
All 15 modules succeeded. The unchanged TarskiComplete provider emitted six
linter warnings. The two changed proof sources and the audit emitted none.

The audit has fourteen explicit typed public clients: the three original abstract
exports; unrestricted K, Peirce, composition and S; the principal numerical row,
composition and lifting exports; the Tarski ex-falso/classical/completeness bridge;
and the current CDom/C222 equivalence. The six core theorems and the four
unrestricted basis results are axiom-free. The numerical clients use propext and
Quot.sound; Tarski completeness uses the usual propext, Classical.choice and
Quot.sound. There is no sorryAx and no new axiom declaration.

The 215-state machine endpoint was not rebuilt by this component experiment.
The patch leaves that theorem statement, the machine table and source program
untouched. A production adoption must run the affected endpoint descendants and
the project's current acceptance gate.

PORTABLE COMMANDS

Read-only review of the pinned baseline and regeneration:

  python3 check.py --repo /absolute/path/to/ProveIt

Fresh component compilation (OUT must not yet exist):

  python3 build.py --repo /absolute/path/to/ProveIt \
    --lean /absolute/path/to/lean-4.32.0/bin/lean --out /absolute/path/to/OUT

The compiler build reads the repository for unchanged dependencies. It does not
write into the repository and does not use Lake or require network access.

After repository review, the patch can be applied with:

  git -C /absolute/path/to/ProveIt apply /absolute/path/to/shared_basis.patch

From the patched k225-formal directory, the maintained producer check is:

  python3 generate_dominated_implication_lean.py --check

EVIDENCE

shared_basis.patch                    Exact six-file patch, applicability checked.
integration_metrics.json              Complete before/after pins and source counts.
source_comparison.json                Parent-origin comparison for the four inherited files.
producer_verification.json            Fresh byte reproduction and legacy renderer controls.
patch_check.json                      Successful git apply --check record.
evidence/lean_verification.json       Every fresh module's source/object/log hash and command.
evidence/logs/SharedBasisAudit.log    Exact typed-client assumption reports.
evidence/summary.json                 Fresh scope and warning census.

Historical verification commands retain their actual absolute execution paths.
The commands above and build.py/check.py accept explicit portable paths.
Inherited proofs, data, renderer and headers retain their existing attribution;
the shared basis is the repository's prior work identified above.
