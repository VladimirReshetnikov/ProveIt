Lean proof simplification for positions, rank growth and rephasing
Sixth review, 26 October 2026

Read report/report.pdf first. Editable LaTeX and a PDF build script are included.

SOURCE AND NOVELTY BOUNDARIES
Candidate source: 9d9d1123b39927d30363f1dcd53c23f0575c30ee.
Final bounded comparison: 60fcb2a69b7f1fdd4c3592ea5f164223cad50abe.
Repository: https://github.com/VladimirReshetnikov/ProveIt
The final exclusion collection has 43 placed manuscripts and no incoming
ZIPs. All prior proposals, including notes-only alternatives, are assumed
available for novelty analysis, not asserted to compile together.

RECOMMENDED PROOF-ONLY SET
1. safety/patches/positions_combined.patch changes ONLY position_budget and
   position_injective. Unfolding the small fixed auxiliary coefficient makes
   their arithmetic linear; symbolic powers and all public guards remain.
   CurrentControllerPositions2011.lean: 178 -> 174 physical lines.
2. population/patches/rank_gt_twice_window.patch obtains the existing cubic
   rank comparison through 2u <= 3u < 2^(3u), retaining the exact packing and
   final cast bridge. CurrentPackingRank2011.lean: 138 -> 133 lines.
3. rephase/patches/rephase-exact-field-rewrite.patch rewrites the two record
   fields directly instead of constructing an intermediate function equality.
   CurrentWordRephase2011.lean: 122 -> 116 lines. Its separate scalar modular
   transport and quotient recomputation are unchanged.
Together: three complete production files, 438 -> 423 lines, 15 fewer.
No new helpers/imports, altered public statements or definition changes.

SECONDARY HOUSEKEEPING
population/patches/disjoint_add_lt.patch directly rewrites an existing
disjointness identity: NativePackingPopulation.lean, 57 -> 55 lines.
This is two additional lines, not a substantive new population theorem.
All four files: 495 -> 478 lines, 17 fewer physical/nonblank lines.

LATE WITHDRAWALS
The late zq supporting note proposes retiring the optional-support branch.
Under the assumed-applied rule, shorter proofs of optional_next_lt and
optional_stride_lt are therefore redundant; position_ne_three is also
conservatively excluded through its optional-path consumers. Those three
candidate edits and their nine provisional saved lines are withdrawn.
Their original unchanged proofs remain in frozen full-file snapshots, but
no replacement patch or credited saving for them is delivered.

PATCH SELECTION
Use positions_combined.patch alone for both retained position edits.
The two isolated position patches target the original baseline as selective
alternatives. Never apply the combined patch as well as its isolated pieces.
Body-edit permutation checks are not claims about arbitrary unified-patch
context sequencing. The integrated audit composes the combined positions
patch with the three other, disjoint-file patches in all 24 orders.

VALIDATION STATUS
Every new Lean candidate is UNCOMPILED. No Lean elaboration, kernel check,
axiom comparison or performance benchmark was run. The project source
already has one-dummy nonwrap under physical position guards, exact packing
population and same-data rephasing; those are not new results of this review.
Remaining-obligation descriptions are bounded to the documented comparison.
This packet establishes no new full polynomial/consistency equivalence.

OFFLINE READ-ONLY REPLAY
With Python 3, from any directory:
  python3 -X utf8 -B /path/to/packet/verify.py
  python3 -X utf8 -O -B /path/to/packet/verify.py
The top-level checker verifies the sealed file hashes and 702 maintained
Lean-source Git bindings, then runs four source/patch/finite stages:
  safety/verify_safety.py
  population/checks/audit_population.py
  rephase/verify.py
  audit/check_integrated.py
No Git, network, Lean or third-party Python package is needed. JSON goes
to stdout; no sealed files are changed. Exact textual patch/interface
checks and finite models do not prove Lean elaboration or universal claims.

LEAN ACCEPTANCE WORK STILL REQUIRED
Use an authorized complete checkout at the declared pin with its original
lean-toolchain and lake-manifest.json. Establish an unmodified baseline,
apply selected patches, then build main modules, their existing Checks
modules, affected clients and configured project checks. Inspect axiom
output before and after. Never weaken a public theorem to fit a tactic.
The repository warns that LAKE_JOBS=1 does not bound this Lake version.
Run one dependency-ready Lean process/module at a time, main before Checks;
do not run an umbrella over stale dependencies. Do not set LEAN_NUM_THREADS=0.

CONTENTS
report/       New LaTeX, PDF, build script and PDF QA record.
baseline/     Frozen maintained tree, selected metadata and two selected HTP
              dependency sources; not a full external build closure.
safety/       Two-edit candidate, combined/selective patches and checker.
population/   Rank and secondary disjoint-sum candidates, patches and checker.
rephase/      Exact-field candidate, patch and checker.
audit/        Independent source, patch composition and bounded-model audit.
catalog/      Exclusion/adoption ledgers, final comparison and provenance.
              Old full reports, incoming archives and raw extraction trees
              are omitted; documentary receipts may describe those inputs.
evidence/     Main-source hashes, Git bindings and source census.
MANIFEST.json SHA-256 seals for every other included file.

No upstream source edit, push or publication was made by this review.
