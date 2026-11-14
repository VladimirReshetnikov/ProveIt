U209: a 209-state candidate for the consistency of Peano arithmetic
=================================================================
Research prepared for Vladimir Reshetnikov, 29 October 2026.

RESULT
------
machine/u209.tm is a complete deterministic binary one-tape Turing machine:

  working states: 0 through 208; separate halt label: 209
  initial state: 0; initial head: 0; every tape cell initially zero
  tape coordinates: all integers; every transition moves L or R
  literal rows: 418; the entire blank initializer is included

Each row q b w D r means read b in state q, write w, move D, enter r.
Entering the halt label halts after that transition's write and move.
The first line '#! start 0' is a header, not a transition.

The ordinary mathematical proof composes the new exact machine/source
reduction with the retained proof-search and unary-theory calibration:

  PA proves: not Halt(U209, blank) <-> Con(U) <-> Con(PA).

Proof status: conventional PA-formalizable mathematics plus fresh executable
local/source and unary/list-inductive verification. This is not a newly
exported PA derivation or a newly kernel-checked Lean, Rocq, or MM0 endpoint.
It asserts neither PA's consistency nor unconditional nonhalting, and makes
no global minimality or priority claim.

WHAT IS NEW
-----------
The current Contextual, Research, and Rotated U211 proposals are three
pairwise nonisomorphic literal tables, with the same 3,909-primitive word
and resolved ordinal control graph. Each deletes a different native state
from a common U212 parent. Their patches do not compose directly.

Thirty closed source rotations arrange all three required entry invariants
at once. After an arithmetic entry repair at 171/read0, the final fold uses

  rho(180)=163; rho(181)=220; rho(218)=157; rho(q)=q otherwise
  163/read0 = 0 L 211
  220/read0 = 0 L 217

Redirect all targets through rho and delete both rows of 180,181,218.
The new helper 217 is essential: the earlier Research helper 129 and the
discovery U210 helper 215 are not correct substitutes in the final layout.

Native labels are names, not counts. In machine/u209.native.tm native 254
is halt and native 211 is a working helper. machine/state_map.json gives
the checked native/dense bijection.

The report also proves a separate obstruction: deleting the entire native
dominated propositional row produces a calculus whose target 1 underivability
is already PA-provable. 'Dominated' refers to a numerical parameter bound,
not logical redundancy. See report Section7 and research/.

VERIFICATION
------------
* Exact reconstruction of native/dense tables and source from pinned U212.
* All 30 closed rotations, all 3,909 primitives, all 5,083 guarded CFG arrows.
* All 3,908 final internal-prefix states commute with the simultaneous rho.
* Ten universal two-cell fold cases, with an arbitrary unread tape exterior.
* Two universal arithmetic-entry repair cases and 13 rejected damaged controls.
* All 5,084 arbitrary-natural primitive contracts freshly rederived.
* All 418 literal transitions covered; 1,250,049 symbolic inference applications.
* Four arbitrary-value block/list lemmas rederived from the exact table.
* Complete 48,140-transition blank prefix and 120 one-cell endpoint verified.
* Independent checker agrees under normal and optimized Python.
* All three original U211 quick audit commands rerun successfully.

Seventeen intermediate rotation stages have a seven-zero source address.
They are source/assembly stages, not accepted runtime-equivalent machines.
Only the final layout is used in the final runtime proof; its maximum zero
run is 6 and maximum depth 42. The code and report explicitly preserve this
distinction.

The local R212->U209 fold has an all-common-initial-tapes proof with positive
one-, three-, or five-step blocks. The full U212->U209 source transformation has the
proved blank/canonical-frame scope. The bound T_C <= 5 T_R applies only to the
fold after rotations, not to the original U212. No speedup is claimed.

OFFLINE REPRODUCTION
--------------------
Python 3.10+ and the standard library. No network, solver, optimizer, or proof
assistant is needed. Keep assertions enabled in the main driver/runtime:

  python3 -B reproduce.py

Default reproduction checks the manifest, compares all input packets,
rebuilds the machine and source, runs independent local/source/startup
checks and the no-go cross-check, and regenerates every universal runtime
case. Fresh per-case data must equal the retained compressed records.
The full replay takes a few minutes, depending on hardware.

  python3 -B reproduce.py --output /tmp/u209-reproduction
  python3 -B reproduce.py --quick

--output keeps receipts outside the sealed packet; otherwise they are
temporary. --quick explicitly skips the unbounded symbolic runtime and
reports that omission. It is not a substitute for the full default run.

Individual useful commands (default outputs are below build/):

  python3 checks/independent_check.py
  python3 -O checks/independent_check.py
  python3 checks/independent_source.py
  python3 checks/compare_inputs.py
  python3 checks/check_runtime.py
  python3 checks/build.py --output /tmp/u209-rebuild
  python3 checks/check_row_deletion.py

Do not run the main driver or the symbolic engine with -O or PYTHONOPTIMIZE.
The independent literal checker uses explicit exceptions and is tested in
both modes. Building outputs under build/ does not change any sealed file.

REPORT
------
report.pdf is the 17-page research report, with all 418 transitions and the
complete 30-rotation recipe. report.tex and paper/*.tex are editable source.
From a working copy with a TeX installation:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF metadata can differ by TeX version/time. Verify the supplied manifest
before editing or rebuilding sealed files.

CONTENTS
--------
machine/       U209 native/dense tables, rotated212, source, state map, patch.
inputs/        Pinned U212 table/source, 30 rotations, and immutable provenance.
checks/        Deterministic builder; independent source and literal checks;
               pinned inherited runtime induction engine; input comparison.
evidence/      Fresh local/source/runtime receipts, full compressed case data,
               original-packet quick logs, and final portable replay record.
reference/     All four original source archives, unchanged.
research/      Full proof and finite cross-check of the row-deletion obstruction.
licenses/      Original attribution, licenses and notices retained from lineage.
MANIFEST.json  SHA-256 and size of every sealed payload file except itself.

FULL MATHEMATICAL DEPENDENCY
---------------------------
The native numerical calculus is not the positive dyadic stream proposed in
the unary-theory packet. It uses truth 0, target 1, seven logical rows, a
dominated propositional row, and the U214 gated role-a cover/vacuity bundle.

The complete inherited mathematical dependency is included transitively in:

 reference/U211_ConPA_Contextual_2026-10-28.zip
   u211_contextual_2026-10-28/baseline/selected_U212.zip
     inputs/parent_U213_ConPA_2026-10-28_1.zip
       inputs/U214_ConPA_Reduction_2026-10-28.zip
         inputs/U218_ConPA_2026-10-28.zip
           inputs/U222_ConU_2026-10-28.zip

Each inner inputs/ path is relative to that archive's top-level package
directory. See U222 paper/report.tex and references/logic/, U214
proofs/role_emitter.tex, and U213 proofs/compiler.tex,
proofs/source_transport.tex, proofs/startup_suffix.tex.

The actual startup contains an opaque tail 4 whose safety depends on the
retained nine-head/two-debt proof, not on treating its raw numbers as
theorems. The report explains this proof boundary explicitly.

EXACT IDENTITIES
----------------
Dense U209:
65ccb606c8e970adec22c311486e747b440171363601b8f11b56bc729cf8decb

Native U209:
891455876f2684b2bd2a9118092715590028fbdb227aa7055030536714d8b7a4

Source:
cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164

Repository snapshot:
VladimirReshetnikov/ProveIt commit da4ab9dd68ccfc47ac852118601eaf1fdae53795

See NOTICE.txt for attribution and the distinction between new checking code,
inherited proof engines, and the unchanged reference packets.
