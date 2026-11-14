PA194QNS: a distinct 194-state machine for Con(PA)
================================================

RESULT
------

No machine below 194 working states was established. This release supplies
the requested fallback: the concrete PA194QNS machine and its PA194QS
companion, both with 194 working states, 388 binary transitions, and a
literal all-zero blank start. Their exact source programs and physical
implementations have been checked.

The primary theorem, using the supplied ordinary mathematical PA/calculus
calibration, is

    PA proves: Halt_blank(PA194QNS) iff exists p Prf_PA(p, code(0=1)),

and hence PA proves Nonhalt_blank(PA194QNS) iff Con(PA).

The new part is an all-natural-register finite-trace equivalence with the
supplied PA194QN, a compatible physical construction, and its independent
checks. The component Q emitter, no-push MP protocol, and symmetric guard
idea are credited to the supplied work. The inherited logical calibration
remains a named proof dependency. This is not a newly compiled end-to-end
Lean/Rocq proof or a completion of the repository's iPRA formalization goal.

Read report/report.pdf for the detailed comparison, proofs, complete primary
transition table, all 40 recovered prior frontier classes, all 54 deliveries,
bounded searches, and further encoding proposal. report/report.tex and all
its inputs are included.

MACHINE CONVENTIONS
-------------------

machines/PA194QNS/machine.tm is the authoritative primary table.
Each row is: state read write L-or-R next
Alphabet: {0,1}. Blank: 0. Two-way infinite tape.
Initial head: 0. Initial control: 0. Working controls: 0..193.
Halt control: 194, with no outgoing transitions.
There is no external program or initialization apparatus.

Primary dense-table SHA256:
7eb36aea69e5de46cc47fa7aab0191f191657ab500dafb808dc3c394640591b8

Companion dense-table SHA256:
fcfa7e87fcec2117ea21a84312dc8bb15841fb3c8cfd267ed40946a5ca4b1407

Native tables use start 74 and halt 254. labels.json maps dense to native,
including the halt label. The raw construction has 202 working controls:
135 fixed + 67 AX readers. Seven AX folds plus one controller fold give 194.

WHAT CHANGED
------------

QNS combines the exchanged-premise Q emitter, no-push successful MP, and
a symmetric implementation of the ORIGINAL sum-based Shift guard.
It is distinct from the older cache-only HS/NS protocol. The same name
PA194NS occurs for two different prior designs; the report disambiguates them.

Relative to the incoming QN table, the exact changed native rows are:

  state read    old action       new action
     28 0       0 R 41           0 R 330
     38 1       1 R 20           1 R 30
     41 0       0 R 24           deleted
     41 1       0 R 25           deleted
     70 0       0 R 41           0 R 330
    310 1       1 R 62           1 R 330
    330 0       absent           0 L 31
    330 1       absent           1 L 46

The comparator receives (H,X)=(1,k) instead of (k,1), with k=t+h+x
for arbitrary incoming T=t,H=h,X=x. Both halt precisely when k=1;
otherwise both leave the same complete register store. Three primitive
source sites disappear. The source-level saving per visit is 0 for k=0,
4 for k=1, and 2k+4 for k>=2. This is not a claim of a uniform literal-TM
speedup.

QS keeps the original successful-MP push: native (164,1) is 1 R 98
instead of QNS's 1 R 114. The remaining native rows are identical.

REPRODUCE
---------

Python 3.10+ and its standard library suffice for the accepted constructions.
Use assertions; do not run with -O or PYTHONOPTIMIZE.

From this directory:

    python3 -B verify_all.py --quick
    python3 -B verify_all.py

Quick mode rebuilds both tables and their sources, checks all 32 fold
cases, exact startup, Q head and exchange proof, independent source
bindings, the all-register replacement's literal block binding, and exact
novelty against the frozen 40-class corpus. It verifies the identity of
the recorded physical receipts but DOES NOT rerun their physical symbolic
proof engines. The full command additionally replays both engines on both
machines. Replays write to a fresh temporary directory, leaving frozen
evidence unchanged.

To reconstruct one machine only:

    python3 -B build.py --family PA194QNS --output /tmp/pa194qns-rebuilt
    python3 -B build.py --family PA194QS --output /tmp/pa194qs-rebuilt

Construction and physical verification are deterministic; the optional
stochastic searches are unnecessary for reproducing the accepted machines.

To regenerate report tables:

    python3 -B report/generate_includes.py

To compile the report, run twice in report/:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex

A normal LaTeX installation with amsmath, amsthm, lmodern, microtype,
booktabs, longtable, enumitem, needspace, fancyhdr, xcolor and hyperref is sufficient.

RECORDED VERIFICATION
--------------------

                                  QNS                QS
Working states                    194                194
Source sites                    3,651              3,670
Source outcomes                 4,751              4,776
Construction symbolic steps 1,512,246          1,518,350
Literal symbolic steps      1,106,186          1,110,647
Generic list lemmas                  4                  4
Simultaneous fold cases             32                 32
Exact blank startup steps      58,004             58,004

The literal checker rederives list lemmas from actual transition rows
without the construction engine's arithmetic-box oracles. Its contracts
cover arbitrary natural register values, an arbitrary natural gap,
and arbitrary finite nonempty spare lists of arbitrary natural values.
Symbolic step counts refer to the proof engine, not a bounded simulation
over numerical register examples.

Finite clock probes support diagnostics only. The universal source
preservation argument is the explicit induction in report/source_preservation.tex.

CORPUS AND NOVELTY
-----------------

Snapshot: 317b07268681b44ff352d173a162e2a8c241b2fe
Repository: https://github.com/VladimirReshetnikov/ProveIt

The comparison covers 51 filed PA research packets plus all three incoming
archives at that snapshot. The fresh literal census recovered 39 prior
194-state whole-graph classes; the JSON supplement adds one, for 40.
It verified all 2,431 tracked candidate files against the pinned Git blobs.
The 40 classes include rejected candidates and research auxiliaries; they
are not 40 independently established consistency theorems.

Exact graph comparison allows arbitrary control renaming, any spanning
root, global left/right reflection, and global bit complement. Neither
new candidate matches any recovered prior class. This is novelty in the
recognized pinned corpus, not a claim of global priority or semantic
inequivalence. The recognition scope and JSON limitations are explicit
in the report and comparison receipts.

The frozen novelty test works without a repository checkout:

    python3 comparison/check_novelty.py machines/PA194QNS/machine.tm

One original raw table per prior class is in comparison/frontier40_tables/,
with hashes and source locators. The historical repository census and
machine classes are preserved under comparison/repository/. The full
census scripts record their original workspace layout; use the frozen
corpus and standalone novelty checker for portable reproduction. A fresh
repository rescan requires the pinned checkout and matching source paths.

OPTIONAL RESEARCH
-----------------

research/joint_grammar/ contains the unsuccessful 240-second exact-Q-word
search for one further compatible saving. Its actual log records
1,366,615 proposals, 220,787 accepted moves, and no qualifying 193-state hit.

research/additional_reductions/ contains five completed bounded local
screens on the supplied PA194N6, longer 17-cell windows, a checked source
invariant, actual logs, and a self-contained replay. All five screens
returned zero candidates. Run its replay.py from that directory; a C++17
compiler is needed. These results are not state-count lower bounds.

research/nested_binary/ contains a new total formula-code recoding and
its proof translations. The corresponding grammar experiment is in
research/additional_reductions/nested2_experiment/. Its best score still
has scanner penalties and unverified fold compatibility. It is not an
accepted 203- or 207-state machine and yields no verified 193/194 machine.

PROVENANCE AND LICENSES
----------------------

PROVENANCE.json records the pinned source, copied file identities and new
work. SHA256SUMS covers all released files except itself. Inherited source,
logical references and license notices are retained; imported code is
attributed in verification/reference/ and the additional research packet.

The complete mathematical argument must be assessed together with its
explicit inherited PA calibration. A passing Python audit is not labeled
as a proof-assistant kernel theorem.
