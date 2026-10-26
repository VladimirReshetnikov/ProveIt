FURTHER LEAN PROOF SIMPLIFICATIONS FOR DIOPHANTINECONSISTENCY
Prepared for Vladimir Reshetnikov — 26 October 2026

Start with report.pdf. The complete editable manuscript is report.tex, with
generated numerical constants in metrics.tex. This packet proposes four
directions beyond the prior simplification corpus. Two are supplied as
complete production-source patches; two are optional checked abstractions.

SOURCE SNAPSHOT

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 23f631ea07fff8632eb8cd92286f7621bbe051c0
Toolchain: leanprover/lean4:v4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997
All package revisions: evidence/lake-manifest.json

RESULTS

1. Compositional object-formula specifications: 133 fewer physical lines,
   20 proof bodies in eight complete modules; no helper overhead.
2. Common scale-parametric Pell bound and lower comparisons: 86 additional
   lines saved after the earlier alias cleanup (90 versus current sources).
3. Optional integer extraction from two error budgets: checked core and
   applications; no production migration or net line saving claimed.
4. Optional observed-set certificate closure: checked core and six concrete
   client theorems; no production migration or net line saving claimed.

The integrated patch changes 24 existing proofs in 11 existing production
files; the shared Pell helper lives in an existing lower-level module.
Raw reduction: 223 lines. Additional reduction after charging four lines of
previously proposed upper-estimate alias cleanup to the baseline: 219 lines.
This is a scoped counterfactual for the affected proof bodies, not a globally
merged implementation of all prior reports.

FINAL EXCLUSION REFRESH

Four additional incoming archives were found during the final refresh. Their
reports, prototypes and supplementary screening ideas were audited, bringing
the incoming total to nine. The source and deliverable were rebased to the
current pin above. Two entire candidate directions (finite-cut rank/rail
reuse and a small-square firstUnit proof) were withdrawn as superseded by
prior ideas. Two Sat targets were also dropped because a new prior proposal
removes those private stages: zeroSumStage_spec and zeroProductStage_spec.
No withdrawn patch or example is included as a proposal in this packet.
See evidence/late-audit-part1.txt through late-audit-part3.txt for exact prior
locations and decisions; the initial 53-family audit remains as provenance.

PACKET CONTENTS

report.tex, metrics.tex, report.pdf
    Editable LaTeX source and rendered report with exact source links.
patches/combined.patch
    Both integrated directions. The family patches permit separate adoption:
    specifications.patch and pell.patch.
candidates/
    Complete changed production modules at repository-relative paths.
    These snapshots make review exact. Do not copy them over a branch that
    has other changes without porting the patch deliberately.
examples/
    Checked independent demonstrations, optional cores, concrete adapters,
    and an integrated public-endpoint axiom audit.
evidence/
    Source metrics/hashes, 53-family novelty audit, prior-artifact inventories,
    full-module compilation records, and before/after axiom reports.
validation-plan.json
    Exact production and example/audit endpoints.
scripts/
    Reproduction tools described below. Python 3.11 or later is required.
SHA256SUMS
    SHA-256 hashes of all other delivered files.

CHECK THE PACKET WITHOUT BUILDING

From this packet directory:

    python3 scripts/verify_packet.py

To additionally check original source hashes and patch applicability, point
to an unmodified checkout at the source pin:

    python3 scripts/verify_packet.py --repo /path/to/ProveIt

REPRODUCE THE LEAN CHECKS

Prerequisites: the pinned checkout with its local source import closure,
Lean 4.32.0, and dependencies already built at the revisions in the manifest.
The scripts do not fetch packages, change the checkout, or write into package
caches. They use a separate output directory. No precompiled project object
files or Lean toolchain are included in this archive.

    python3 scripts/validate.py \
      --repo /path/to/ProveIt \
      --lean /path/to/lean-4.32.0/bin/lean \
      --packages /path/to/ProveIt/.lake/packages \
      --out /tmp/diophantine-simplification-check

Omit --packages when they are in the checkout's .lake/packages. Add --plan
to list the import closure without compiling it. validate.py checks the
repository commit, compiler version, and every package revision, recursively
compiles local imports, and writes records.json plus per-module logs.

Then check the examples and full-source private specification axioms:

    python3 scripts/check_examples.py \
      --repo /path/to/ProveIt \
      --lean /path/to/lean-4.32.0/bin/lean \
      --packages /path/to/ProveIt/.lake/packages \
      --validated /tmp/diophantine-simplification-check

The second command checks five example/audit modules and eight full-source
specification axiom audits. It writes example-checks.json and example-logs/.
Add --baseline /path/to/original-validation to additionally compare the eight
original full-source axiom audits; the supplied final run used this option,
for 21 successful example/audit compilations in total.

The supplied successful combined run checked an import closure of 71 local
repository modules, reusing an independently checked exact-pin baseline for
unchanged prerequisites. Its optional --baseline argument points
to a directory containing build/ and build_records.json (with an optional
extra_records.json).
Those compiled objects are intentionally not shipped. Reuse requires matching
source, local-dependency-object, and output hashes. Because Lean resolves a
namespace root from the first matching search directory, verified objects are
linked individually into the isolated output tree; candidate compilation
never follows those links to overwrite baseline objects. A normal recipient
can omit --baseline and build the local import closure from source instead.

VALIDATION LIMITS

This is a checked import closure and full changed-module review, not a build
of every target in the repository. No performance improvement is inferred
from elapsed times. Standard Lean foundational axioms are permitted; no
sorryAx or newly postulated project axiom was observed in the audited results.
The 20 specification theorem axiom sets match their before versions exactly:
propext, Classical.choice, Quot.sound.

Evidence records preserve the actual absolute paths used for reproducibility;
those paths are provenance, not instructions to recreate this environment.
Use the portable commands above with your own paths. A disk-space interruption
during the baseline build was repaired by regenerating affected object files.
Only successful final records were used for the combined overlay.

EXCLUSION POLICY

All proposed ideas, including pending and supplementary ones, in research
packets 2026-10-26a through f and the nine current incoming simplification ZIPs
were treated as available. See evidence/novelty-audit-initial.txt for the
initial 53 excluded families, and the three late-audit files for the refresh.
This does not claim to have semantically
read every older mathematical archive transitively linked by the incoming
index. Existing proposals are assumed applied for novelty and the stated
incremental accounting; alternative historical architectures were not merged
into an invented unified checkout.

REBUILD THE PDF

    python3 scripts/build_report.py

Requires pdflatex and the standard packages named in report.tex, including
Latin Modern, geometry, amsmath, booktabs, longtable, microtype, xurl,
hyperref, listings, fancyhdr, enumitem, and needspace. The delivered PDF was compiled,
rendered, and visually inspected. Rebuilding creates ordinary LaTeX auxiliary
files; these are not part of the distributed archive.

No change has been pushed to the repository. The patch and source overlays
are proposals for review and selective adoption.
