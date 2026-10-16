ZFC253 machine audit and constrained compression experiments
==========================================================

Date: 2026-10-16
Upstream proof/table: mira-emmy/busy-beaver
Pinned commit: 0d544f2a2e3c18f12278441a74b7879f31cbe856
Public PR: https://github.com/jeff87654/busy-beaver/pull/20
Status when inspected: open, unmerged; exact-head CI completed successfully.

OUTCOME

The smallest complete machine located in the inspected sources has 253 working
states, two symbols, a blank initial tape, start state0, and a separate terminal
state253. It is existing work, attributed upstream to mira-emmy's reduction of
Mira-Cult's254-state construction, with Jeff's accepted verification layers.
This package does not claim a new record or authorship of either machine.

The253 table SHA256 is
84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95

The254 table SHA256 is
d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb

New audit contributions in this package:

1. An exact obstruction to every noninjective transition-table quotient of the
   literal253 machine. The certificate supplies distinguishing free input words
   for all31878 pairs of working states; the longest has12 symbols. Its small
   independent replay checker does not use the generator's partition/BFS data.
   This proves injectivity of exact transition homomorphisms. It is not a lower
   bound on machines with the same blank-tape halting behavior.

2. A radius6 local-window check of253, extending the existing ProveIt audit
   implementation to this table:335369 abstract configurations;63756 ordered
   state pairs; at most256 positive local steps per side; no certified merge.
   This is a negative result for the bounded checker, not general inequivalence.

3. An actual arbitrary-register instruction audit followed by106400 bounded
   fold specifications. All8391 baseline instruction/branch cases pass at
   header gap>=40. The maximum baseline abstract execution length is331.
   56448 specifications redirect a removable state to another state. Another
   49952 specifications identify a pair after taking the0 row from one member
   and the1 row from the other. These counts describe specifications; some
   generated tables may coincide. The latter family includes cross-row sharing
   absent from a search consisting only of direct redirections.

   Exactly one specification passes all affected runtime cases: old5 -> old64.
   It is the already known prepared252-state runtime core. It removes the
   initializer; this package has no proof that its blank start searches ZFC.
   No mixed-row specification passes this checker.

   First reason for rejecting a specification:
                         single       mixed
   symbolic fuel          53173       46974
   unexpected exit          176         191
   unsupported box         1666        1991
   unsupported run peel    1432         796
   runtime success            1           0

   Thus100147 specifications are unresolved because the symbolic fuel budget
   of700 was exhausted. Unsupported abstract operations likewise give no proof
   of inequivalence. The appropriate conclusion is NO CERTIFIED BLANK-INPUT
   IMPROVEMENT FROM THESE EXPERIMENTS, not impossibility of a smaller machine.

4. A bounded search for an alternate bootstrap of that prepared252 core. From
   blank start old64,5000000 steps visit dispatcher96 on7445 occasions. Of
   these,3047 have the full strict tape-frame shape, but the maximum observed
   header gap is32, below the inherited gap40 contract. No such frame matches
   any of20000 reference RM-prefix states with sufficient gap. The original
  253 machine's312975-step endpoint is independently reproduced. The prepared
   core does not reach that endpoint at that time. These facts do not prove
   that the prepared core halts, runs forever, or fails to represent Con(ZFC).

SYMBOLIC CHECKING SCOPE

runtime_fold_search.py runs the pinned upstream affine executor against the
complete6460-leaf program, with both branches of each decrement, giving8391
cases. Register values and the extra gap n>=0 are symbolic, not sampled values.
It uses the existing register-file contracts as opaque operations. The actual
rows used by those contracts are protected, and their entry/exit states remain.

The protected footprint is recorded in runtime-fold-results.json. Three
return-state boundary rows, old3/read0, old6/read0, old48/read0, are outside the
opaque excursions. Box.v's ret_file qa qb uses qb/read1, then stops before
qb/read0; its applications use(qa,qb)=(1,3),(4,6),(63,48). Those three0 actions
are handled by explicit symbolic steps. No protected accessed row is modified
by a tested fold. This distinction is necessary: protecting source states
alone does not automatically protect target labels in their transitions.

For unaffected instruction cases, the original recorded execution reads no
changed row and therefore remains valid. All affected cases are rerun. A
passing affine trace means the exact original output tape, control path, and
register effect, for every represented register file and gap. It is not a
kernel check of this new Python search implementation.

The only unread nonbox state/symbol pair across runtime cases is old5/read0:
exactly the initializer action. Purely deleting that state loses its startup
work. Altering the initializer, changing more transitions, using a different
interpreter/encoding, and stronger symbolic domains remain possible routes.

UPSTREAM VERIFICATION EVIDENCE

The full upstream source-only checker was run locally and passed: exact table,
state maps,160-source dependency closure,194 assumption-report declarations.
No local Coq compiler was available, so the kernel build was not rerun here.
The exact-head GitHub CI metadata and job log were independently retrieved:
run38829447100, job116744561855, success at2026-10-16T00:49:43Z. The log reports
160 compiled modules,194 closed reports, and recursive coqchk acceptance.
ci253-proof-excerpt.txt and ci253-status.json retain this evidence.

E2E253.v proves external equivalences with finite refutations of SIR, ZFc,
and ZFc+AC. ZFc omits Regularity. The existing Z_main.ZFCReg_equicons gives
the exact external transport to ZFc+Reg+AC. These external Coq propositions
must not be described as an already exported arithmetic proof compiler or a
literal formal theorem internal to PA/ZFC. That internalization is a separate
task. The source assertions are discussed in the accompanying research report.

REPRODUCIBILITY (Python3, standard library only)

Run from this directory. All commands are offline and write only local reports.

  python3 quotient_certificate.py --check
  python3 vendor/busy-beaver/ZF/m253/tools/generate_candidate.py --check
  python3 vendor/busy-beaver/ZF/m253/tools/gen_sites253.py --check
  python3 runtime_fold_search.py
  python3 prepared_prefix.py
  python3 prepared_frame_search.py

The full fold grid took approximately3 minutes on the research host. It may
take longer elsewhere. Do not run Python with-O/-OO, which disables assertions.
quotient_certificate.py without--check regenerates its certificate.

To reproduce the independent ProveIt window audit:

  python3 audit_tm.py vendor/busy-beaver/ZF/m253/machine/zfc_253.tm \
    --expected-sha256 84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95 \
    --expected-states 253 --expected-halt 253 \
    --window-radius 6 --macro-steps 256 --trace-steps 312975 \
    --output audit253-radius6-reproduced.json

Only the selected public sources needed for these experiments and their
attribution/context are vendored. This is not the160-module Coq build closure.
For a full kernel rebuild, use the pinned upstream repository and its
ZF/m253/check.py instructions. UPSTREAM_SOURCES.json records URLs and hashes;
FILE_MANIFEST.json hashes this complete audit package.

ATTRIBUTION

The original254 machine is Mira-Cult's; the253 reduction is mira-emmy's. Jeff
supplied the accepted proof layers. Andrew James Wade's interpreter/compiler
lineage and its MIT No Attribution notice are preserved in LICENSE.wade.
audit_tm.py is copied unchanged from ProveIt at
4747142d5d15213eb711bdadfa3cc7e769fcb7a7; LICENSE.ProveIt is included.
Upstream README files preserve the original authorship and dependency notices.
The new search, diagnostics, and quotient-certificate programs are research
artifacts for incorporation into ProveIt under its MIT No Attribution license.
