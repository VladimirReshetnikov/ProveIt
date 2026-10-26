FURTHER LEAN PROOF SIMPLIFICATIONS AFTER THE PRIOR PROPOSALS
26 October 2026

Repository: https://github.com/VladimirReshetnikov/ProveIt
Proof-source commit: 29936089835c0c55cca81edc86b4fb0c70ce34d5
Final exclusion audit: 09d65a93c9df8684c1a226341d6a5120623d1cdb
Lean: 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35
mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

START HERE

Read report.pdf for the mathematical arguments, evidence boundaries, and
comparisons with earlier proposals. report.tex is the editable source.
Two primary patches contain two mechanisms improving three concrete proofs:

  01-coefficient-action.patch
    Compose the existing linear coefficient bound twice instead of expanding
    a square into a double sum. Preserve the old linear-bound theorem as an
    alias. The two complete modules decrease from 328 to 316 lines: 12 saved.

  02-power-thresholds.patch
    Replace two scalar exponential inductions by a common-power substitution
    and a threshold shift. Each exact proof body decreases from eight to five
    nonblank lines. The containing snapshots decrease from 424 to 418 lines:
    6 saved.

The four complete primary source snapshots therefore decrease from 752 to 734
physical lines, a net reduction of 18. This includes new helper statements,
documentation, and compatibility declarations. It does not count earlier
proposals as new savings, or measure a hypothetical tree with all earlier
packets integrated.

The separate optional-canonical-tile-index.patch replaces the choice-based
quotient tile index with the existing arithmetic decoder. Its accompanying
baseline comparison proves agreement with the legacy word. The patch increases
the complete module from 147 to 160 lines.
Its benefit is a computable data expression, not a source-size reduction. It
does not remove Classical.choice from all supporting proofs, and equality to
the old constructor is extensional rather than promised definitional equality.

NON-REPETITION AND FRESHNESS

The audit treats optional, deferred, unimplemented, and screened suggestions
as prior ideas, regardless of adoption status. The final frozen review at
09d65a93c9df8684c1a226341d6a5120623d1cdb covers 23 placed packets, a-w, plus
four incoming archives: 27 collections. Incoming archives were inspected as
inert data, including principal manuscripts, relevant notes, optional ideas,
patches and candidate-specific evidence. No archived script was executed.

The earlier a-v stage covered 22 packets and 55 principal TeX files totaling
896,675 bytes, with 129 overlapping exclusion records. These are historical
initial-stage counts, not totals for the enlarged final corpus and not counts
of independent mathematical ideas. The audit does not claim a semantic review
of every unchanged source snapshot or of every historical manuscript
transitively linked from the incoming index.

The final refresh found that packet w already proposes the RefinedPair
expansion-injectivity identity and finite-sign product cleanup. Both were
withdrawn. Their candidate code, patch, checks and eight-line saving are
excluded from this deliverable. Two developed machine proposals were also
excluded after earlier overlap was identified. The retained proposals each
have a specific comparison with the closest earlier work in the report.

The repository advanced during this review. The primary patches and whole-file
measurements refer to the proof-source commit above. The final audit is frozen
at the recorded 09d revision. NativeHalfBinomial.lean changed around the target
during the review; the exact scalar declaration was compared separately.
Apply the focused patch after earlier Pell changes. Do not replace a newer
whole file with an older overlay snapshot. The applicability checker reports
the local checkout commit and checks the actual current files without edits.

WHAT WAS CHECKED IN THIS RUN

  * Coefficients: both complete original modules and both complete candidate
    modules compiled. Six public endpoints have matching standard axiom sets
    in the baseline and candidate. CoefficientAction.lean separately checks
    the new helper and the exact square replacement.

  * Scalar thresholds: exact original and replacement declarations compiled,
    with unchanged theorem headers. Their complete NativePellPower and
    NativeHalfBinomial candidate modules were NOT rebuilt. The second isolated
    replacement uses propext and Quot.sound, while its original proof also
    used Classical.choice. This is a theorem-local comparison.

  * Optional quotient: the complete candidate module and its original,
    unmodified checks compiled. CanonicalTileIndex.lean was checked against
    the BASELINE module, where it defines the new constructor alongside the
    actual legacy constructor, proves their equality, and transfers MarkedWord.

Own-project dependencies used for these checks were rebuilt from pinned
sources. External package objects were reused at the pinned mathlib revision;
missing mathlib objects were built with its stated options. There is no full
repository build claim. No admitted proofs or newly declared axioms occur in
the delivered candidates. Detailed receipts and source hashes are in evidence/.
No upstream branch, commit, pull request, or incoming file was written.

CONTENTS

  report.tex, report.pdf   Report and editable LaTeX source.
  patches/                Two primary patches and one optional patch.
  overlay/                Complete primary candidate source snapshots.
  optional/               Complete optional quotient candidate.
  checks/                 Exact-declaration checks, coefficient axiom audit,
                          and baseline additive quotient comparison.
  evidence/               Successful checking receipts, hashes, measurements,
                          axiom comparisons, and freshness information.
  audit/                  Prior-proposal inventory and closing exclusion audit.
  scripts/check_patches.py Read-only applicability check; no apply or network.
  scripts/verify_manifest.py Verify all listed deliverable hashes without edits.
  scripts/build_report.sh Rebuild report.pdf with two XeLaTeX passes.
  MANIFEST.sha256          SHA-256 hashes of the distributed files.

To check the extracted archive's integrity, run:

  python3 scripts/verify_manifest.py

PORTABLE REPLAY IN A DISPOSABLE CHECKOUT

Use a separate checkout with the recorded Lean toolchain and dependency
manifest configured. The commands below distinguish the baseline phase from
the candidate phase. They are replay instructions, not a statement that every
listed command was executed during this review.

Set these two paths for your machine:

  review_bundle=/absolute/path/to/diophantine-lean-after-prior-proposals-2026-10-26
  review_checkout=/absolute/path/to/disposable/ProveIt

Prepare the disposable checkout at the exact proof-source commit. Obtain any
missing toolchain/package objects through your usual project setup before
running the Lean commands. The patch-checking script itself never fetches
anything.

  cd "$review_checkout"
  git checkout --detach 29936089835c0c55cca81edc86b4fb0c70ce34d5
  python3 "$review_bundle/scripts/check_patches.py" "$review_checkout"

BASELINE PHASE

  lake build DiophantineConsistency.SplitCoefficientBounds
  lake env lean "$review_bundle/checks/CoefficientAction.lean"
  lake env lean "$review_bundle/checks/CoefficientAxiomAudit.lean"
  lake env lean "$review_bundle/checks/PowerThresholdBefore.lean"
  lake env lean "$review_bundle/checks/PowerThreshold.lean"

If considering the optional quotient change, run its additive comparison
BEFORE applying optional-canonical-tile-index.patch. It must import the actual
baseline choice-based quotientWord to establish the advertised legacy
comparison:

  lake build DiophantineConsistency.WangTiles942HelicalQuotient
  lake env lean "$review_bundle/checks/CanonicalTileIndex.lean"

PRIMARY CANDIDATE PHASE

Choose the mechanisms you want. Apply the coefficient patch as a two-file unit.
For both primary changes:

  git apply "$review_bundle/patches/01-coefficient-action.patch" \
    "$review_bundle/patches/02-power-thresholds.patch"
  lake build DiophantineConsistency.SplitCoefficientBounds
  lake env lean "$review_bundle/checks/CoefficientAxiomAudit.lean"

REMAINING NATIVE FULL-MODULE INTEGRATION CHECKS

The following are recommended before adopting the scalar proof patches, but
were NOT executed on the complete native candidate modules in this run:

  lake build DiophantineConsistency.NativePellPower \
    DiophantineConsistency.NativeHalfBinomial

OPTIONAL CANDIDATE PHASE

The script's --include-optional option checks all three patches together and
is intended to run before any of them have been applied. If the primary
patches are already applied, check only the optional patch with git directly:

  git apply --check "$review_bundle/patches/optional-canonical-tile-index.patch"
  git apply "$review_bundle/patches/optional-canonical-tile-index.patch"
  lake build DiophantineConsistency.WangTiles942HelicalQuotient \
    DiophantineConsistency.WangTiles942HelicalQuotientChecks

Review clients that unfold quotientWord, since its implementation changes.
The candidate preserves its public type and proves its observable word equal
to the legacy construction; broader downstream builds remain a separate gate.

BUILD THE REPORT

  bash "$review_bundle/scripts/build_report.sh"

This requires XeLaTeX and the packages/fonts named in report.tex, including
Latin Modern Roman/Sans/Math and DejaVu Sans Mono. The script uses XeLaTeX
twice to resolve references. LuaLaTeX was not the working font configuration
in the preparation environment.
