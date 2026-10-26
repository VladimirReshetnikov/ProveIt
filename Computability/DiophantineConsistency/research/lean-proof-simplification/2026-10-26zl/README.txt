Lean proof simplification for power coordinates and mask clients
Fifth review, 26 October 2026

Read report/report.pdf first; editable LaTeX and its build script are included.

SOURCE AND EXCLUSION BOUNDARIES
Candidate source: 9f35798db4a63c25e435fca14d75931144657d7e.
Final bounded comparison: 91dce223cda86c0755b8a9b2504f84be04443fce.
Repository: https://github.com/VladimirReshetnikov/ProveIt
The final exclusion corpus has 36 placed manuscripts and no incoming ZIPs.
It consists of 28 previously reviewed manuscripts, the previous delivered
review, and seven additional manuscripts. All prior proposals are assumed
available for novelty analysis, not asserted to coexist in a compiled tree.
The four retained target files are unchanged between the two pins.

RECOMMENDED PROOF-ONLY CANDIDATES
1. power/patches/guarded_power_cast_fusion.patch:
   rewrite a guarded cast/divisibility equivalence once instead of proving
   both directions separately. PrimePowerOrder.lean: 80 -> 73 lines.
   Preserve g >= 1, including modulus zero and exponent zero cases.
2. power/patches/exact_order_clients.patch:
   simplify the CRT image calculation, reuse zero-level exact-order results,
   and eliminate a private one-use modulus-transport helper.
   CurrentPowerCoordinates2011.lean: 105 -> 91 lines.
   Exact-order endpoint reuse introduces stronger theorem dependencies;
   keep lower-level proofs if that independence is important.
3. masks/patches/bit3_clear_of_residue.patch:
   directly transport the small-remainder bit bound through existing APIs.
   CurrentWordPadding2011.lean: 224 -> 221 lines.
   The arbitrary-natural domain is unchanged; x itself need not be small.
Together: three complete production files, 409 -> 385 physical lines,
24 fewer physical / 23 fewer nonblank lines, with no new helpers or imports.

OPTIONAL DEPENDENCY TRADEOFF
units/patches/gamma_pos_from_coprime.patch uses the already-proved
coprimality with 47 to prove Gamma is positive. CurrentControllerUnits2011
shrinks from 201 to 198 lines. Unlike the elementary old proof, positivity
then depends on the literal-kernel calibration chain. This is optional,
not a default recommendation, and not a claimed speedup or axiom reduction.
All four patches together: 610 -> 583 lines (27 fewer), including the
removed helper. They modify disjoint files; all 24 patch orders replay.

WITHDRAWN
The q_prefix predecessor-power cleanup repeats prior E41 and is absent from
the delivered candidates and savings. Generic order-certificate assembly,
coordinate equivalence, carry/mask interfaces, fourth-round marker tails
and other inherited mechanisms are not proposed again.

VALIDATION BOUNDARY
All new Lean candidates remain UNCOMPILED. No Lean elaboration, kernel,
axiom-output or performance validation was run. Repository reports of prior
checks are cited as upstream evidence, not rerun experiments. Literal K
residues and unconditional Hs results already exist at the source pin;
these are not new results of this review. Remaining-obligation statements
in the report are bounded to its documented comparison, not a live status.

OFFLINE READ-ONLY REPLAY
From any working directory with Python 3:
  python3 -X utf8 -B /path/to/packet/verify.py
  python3 -X utf8 -O -B /path/to/packet/verify.py
The top checker verifies all sealed hashes, 686 source-to-Git-blob bindings,
then runs four source/patch/finite stages in each mode:
  power/verify_power.py
  masks/verify_masks.py
  units/checks/check_units.py
  audit/check_integrated.py
These require no Git, network, Lean or third-party Python packages.
No sealed file is changed. JSON is printed to stdout. Finite cases and
lexical interface checks do not establish Lean acceptance.

COMPILATION STILL REQUIRED
Use an authorized complete checkout with the declared lean-toolchain and
lake-manifest.json. Establish the unmodified baseline first. Apply selected
patches, compile their modules and existing Checks modules, then affected
clients and normal project checks. For adoption at the comparison pin also
check the new CurrentControllerSubsets2011 client of block_order.
Inspect #print axioms for changed theorems, particularly the dependency
reuse variants. Keep B/K opacity protections and exact domain assumptions.
The repository warns that LAKE_JOBS=1 does not limit this Lake version.
Compile one process/module at a time only after its dependencies are ready;
do not launch an umbrella build over stale dependencies. Do not set
LEAN_NUM_THREADS=0. Source line counts imply no execution-time improvement.

CONTENTS
report/      New LaTeX, PDF, build script and PDF QA record.
baseline/    Frozen maintained Lean tree and selected repository metadata;
             not a complete external dependency/build closure.
power/       Full candidates, patches, API/source evidence and checker.
masks/       One retained full candidate/patch, rejection record and checker.
units/       Optional full candidate/patch and dependency-cost discussion.
audit/       Independent source, patch-composition and bounded arithmetic audit.
catalog/     Current/final exclusion decisions and provenance. Old reports,
             original incoming archives and raw extraction trees are omitted.
evidence/    Main-source hashes, Git bindings and source census.
MANIFEST.json SHA-256 seals for every other included file.

No upstream source edit, push or publication was made by this review.
