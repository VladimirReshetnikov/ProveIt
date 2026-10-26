FOUR FURTHER LEAN PROOF SIMPLIFICATIONS — 26 OCTOBER 2026

Repository: https://github.com/VladimirReshetnikov/ProveIt
Primary source pin: e1c8914bc7064d9a8e7c06171a18069a949badd0
Final exclusion cutoff: ae736b383e59c32c3c3f81910ef1c1197cbfbd44
Lean: leanprover/lean4:v4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

START HERE

Read report.pdf, or compile report.tex with validation-summary.tex in the
same directory. The report gives four additional mechanisms after treating
all earlier proposals in the requested corpus as applied:

A. All-offset reflected-source normalization, with p <= 1005.
B. Fixed-reference coprimality transport through fixed prime support.
C. Translate any seed of the required cardinality to prescribe its sum.
D. Universal LTE divisibility, then multiplicative order by mutual divisibility.

The primary source inventory has 690 Lean files. The novelty audit initially
covered 23 placed packets and five incoming ZIPs, then expanded to 36 placed
packets at the final cutoff. The five initial incoming ZIPs became x–zb;
zc–zj were screened separately. No ZIP remains in docs/incoming at the cutoff.
The full coordinate/control-update direction was rejected because w and zd
already cover it. Terminal-band consolidation from zh is also excluded.

WHAT IS CHECKED

lean/ReflectionAllFields.lean
  Complete independent kernel using the actual constants 2011, 1005 and
  1004, sparse-support adapter, finite-sum lifting, compatibility wrappers,
  and boundary controls. Accepted by pinned Lean; standard axiom audit.

lean/ControllerPrimeSupport.lean
  Generic congruence/coprimality thickening and the guarded rank-factor
  congruence. Accepted by pinned Lean. This does not discharge the actual
  fixed controller certificate or compile the controller dependency closure.

lean/ControllerSubsetTranslation.lean
  General additive-group translation, the ZMod unit case, and arbitrary-seed
  existence. Accepted by pinned Lean. This does not establish safe mutation
  or replace exact startFor/targetInterval definitions.

validation/PrimePowerOrderReplay.lean
  Complete old source in a baseline namespace, complete replacement source,
  all original PrimePowerOrderChecks, two additional exponent controls, and
  axiom audits. Accepted by pinned Lean. The original six public statement
  texts and their axiom sets are preserved. The old pow_cast_eq_one_iff body
  is intentionally unchanged, excluding incidental cast cleanup.

proposed/PrimePowerOrder.lean and patches/PrimePowerOrder.patch
  The strict production replacement validated by the combined replay.
  Full file: 80 -> 77 physical lines; 3,415 -> 3,425 UTF-8 bytes.
  No whole-repository or downstream auxiliary-order build is claimed.

proposed/CurrentReflectedGeometry2011.lean and
patches/reflection-all-fields.patch
  SOURCE-REVIEWED, UNCOMPILED production integration proposal. It retains
  the old theorem header as a wrapper. Full file: 350 -> 351 physical lines.
  The independent reflection kernel is checked; this production module and
  its dependency/client closure were not rebuilt.

The four successful compiler runs have exit code 0. No sorryAx occurs in
their axiom output. Reflection examples have harmless linter warnings.
See validation/results.json for hashes, commands, exact scope and log paths.
No compilation-speed, memory, object-size, or whole-project claim is made.

The assumed-applied condition is used for non-repetition of mechanisms.
Numerical diffs compare the actual pinned files; they are not additive
savings after composing all earlier proposed patches.

VERIFY THE ARCHIVE

From the extracted packet directory:

    python3 verify_bundle.py

This checks every listed digest without modifying files. MANIFEST.sha256
lists all delivered files except itself.

REPLAY LEAN

Use an existing Lake project with the exact Lean/Mathlib versions above.
An ordinary ProveIt checkout at the primary pin is suitable after its
dependencies and Mathlib cache have been prepared. The replay script checks
the Lake manifest and Lean version before invoking Lean on the four files.

    python3 replay.py --project /absolute/path/to/ProveIt

If necessary select an explicit Lake executable:

    python3 replay.py --project /absolute/path/to/ProveIt --lake /path/to/lake

The script does not apply patches. It writes new logs and a receipt under
validation/replay/ in the extracted packet. It imports only Mathlib for
the checked files, so a ProveIt production-module build is not required.
The delivered validation/log files record the original runs; replay writes
separate files instead of overwriting those records.

For a fresh project, obtain the exact repository/dependencies using the
repository's normal setup. Do not run lake update to a different revision.
The archive intentionally does not include Lean or compiled Mathlib caches.

PATCH REVIEW

Both patches are relative to the ProveIt repository root. To check whether
one applies, without changing the repository, use:

    git -C /path/to/ProveIt apply --check /path/to/packet/patches/PrimePowerOrder.patch

The analogous reflection patch is an integration proposal, not a ready
validated migration. Review its complete imported module and downstream
checks before adoption. At the final audit head, both patch targets are
byte-identical to their primary-pin versions.

REBUILD THE PDF

From the extracted packet directory, with pdfLaTeX and standard TeX packages:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The PDF has clickable citations to immutable GitHub sources. Rebuilding
changes the PDF's metadata and therefore its checksum; use the delivered
manifest to verify the original archive before rebuilding.

EVIDENCE AND PROVENANCE

evidence/source-manifest.json: exact original Lean source inventory.
evidence/exclusion-ledger.md: original exclusion map, with late-update notice.
evidence/corpus-index.json: original 28 packet identities and archive inventory.
evidence/late-refresh.md: final eight-packet audit and candidate decisions.
evidence/late-corpus-manifest.json: complete late subtree inventories and
  hashes/URLs for 71 selected packet texts plus the two directory indexes.
evidence/incoming-refresh.diff: complete incoming-index difference.
evidence/late-source-comparison.json: byte comparison of eight targets and
  metadata for five newly inspected production modules.
evidence/reflection-review.md and controller-notes.txt: mathematical review.

Paths inside provenance inventories can identify the original research
workspace or the upstream repository; those inventories do not assert that
all old reports or source snapshots are repackaged here. The immutable
source URLs and Git/SHA-256 hashes support independent retrieval. Earlier
proposal archives are intentionally not duplicated in this packet.

SOURCE-LICENSE.txt retains the upstream MIT No Attribution license for
included source-derived material. New helper code and accompanying prose
may be reused under the same license.
