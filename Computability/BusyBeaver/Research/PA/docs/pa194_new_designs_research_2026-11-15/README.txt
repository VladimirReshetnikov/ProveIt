TWO NEW 194-STATE MACHINES FOR CON(PA)
===================================
ProveIt snapshot: 793c68737d94bffa4e32a75bce6cc8058d6d22f0
Delivery update: 99f17206a77a04d36a9bb7dd04ce2e5d0360cf7d
Research date: 15 November 2026 (UTC)

RESULT
------
No justified machine below 194 working states was obtained. This package
delivers two new 194-state, 388-row, binary single-tape blank-input machines:

  PA194-LCSF3 / PA194LCAX11HSF3
  PA194-MP    / PA194AX11HMP

Both use working states 0..193, start 0, and separate halt 194 in dense
numbering. Native start is 74 and halt is 254; native194 is a working state.
The tape is two-way infinite, initially all zero; the initial head is at0.
Each nonterminal row writes0/1, movesL/R, and enters a possibly identical
state. No extra tape, symbol, input word, or uncounted runtime control is used.

The written relative arguments in iPRA give explicit positive halting
witness maps. The desired nonhalting <-> Con(PA) equivalence follows from
the exact revised AX11H written calibration and, for LCSF3, the LC and SF
transfers. The imported calibration ZIP has SHA-256:
93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075

This is an ordinary mathematical/computer-assisted construction, not a
new completed end-to-end Lean theorem. No PA-consistency assumption is used
in either relative proof. The logical arithmetic calibration and uniform
physical-rule soundness remain identified written dependencies.

WHAT CHANGED
------------
LCSF3: one guarded physical return on the selector-bearing LC_AX11H parent:
  native190/1: 1 L73 -> 0 L42.
The unique predecessor writes1 on the cell immediately left of the head.
One child step therefore equals three parent steps on the complete tape.
The positive witness bounds are t (parent->child) and3t (child->parent).
This affects61 recurring constructor continuations; startup stays57918.

MP: reassociate ((A,B),(C,D)) to (A,(B,(C,D))) at the MP block, preserving
all3671 resolved instructions. Four native rows and87 source addresses
change. The budget is134 fixed+67 readers-7 folds=194. Every one of4778
arbitrary-register/list symbolic outcomes passed on the final folded table.
Both directions of halting transfer have bound58066+9t*t+685t.
Its exact blank startup is58066, versus57922 for its calibrated parent.

MAIN CONTENTS
-------------
pa194_research_report.tex/pdf   Complete manuscript, comparison and tables.
construction/                  LCSF3 builder, independent checker and proof.
mp_construction/               MP builder, complete runtime replay and proof.
comparison/                    Base83-design,31-family,97-delivery ledgers;
                               723 literal classes,520 spanning194 frontier;
                               novelty and corpus verifiers.
comparison/latest_head/        Three later archives/eight additional named
                               designs:91 named,100 deliveries,528 frontier
                               classes at the exact delivery snapshot.
research/reductions/           Rejected193 exact52-cycles, source inputs,
                               independent MP coefficient audit, retained
                               previous-run negative search summary.
research/root_research/        Fresh sound interval invariant and separate
                               certificate checker; sibling of reductions.
research/architecture/         Retained logical/scanner investigation record.
validation/                    Observed final reproduction receipts.
RESULTS.json                   Machine identities and claim boundaries.
PROVENANCE.json / NOTICES.txt   Pinned sources and inherited attribution.
SHA256SUMS / verify_package.py  Byte integrity and TeX/table equality check.
compile_report.py              Portable two-pass LaTeX compilation.

REPRODUCE
---------
Python3.10+ and its standard library suffice for the machine verifiers.
Do not run them with python -O: assertions are essential.
The MP default replays all4778 symbolic cases and can take several minutes.
Run each command from this directory:

  python3 -B construction/reproduce.py --output lcsf3_replay
  python3 -B mp_construction/reproduce.py --output mp_replay
  python3 -B comparison/verify_corpus.py --output corpus_replay.json
  python3 -B comparison/novelty_check.py construction/candidate/machine.tm mp_construction/candidate/machine.tm --output novelty_replay.json
  python3 -B comparison/check_new_pair.py mp_construction/candidate/machine.tm construction/candidate/machine.tm --output pair_replay.json
  python3 -B comparison/latest_head/verify.py --output latest_head_replay.json
  python3 -B research/reductions/replay_cycles.py
  python3 -B research/root_research/verify_intervals.py
  python3 -B research/reductions/check_clock_bound.py --contracts mp_construction/verification/runtime/contracts.json
  python3 -B verify_package.py

Compile with a normal LaTeX installation:

  python3 compile_report.py

The TeX source is self-contained; rebuilding it does not require Pandoc.
Individual construction proofs and inherited manuscripts are also supplied.
The complete reference calibration ZIP is in
construction/reference/references/ax11h_calibration.zip.

EVIDENCE SCOPE
--------------
Both new tables are distinct from all520 recognized base-snapshot spanning194
classes under explicit bijections, all possible corpus roots, reflection,
global symbol exchange and erased terminal-entry decorations. Each novelty
check tries403520 comparisons; another6208 comparisons per machine cover
the eight added classes, totaling409728 against528. A separate776 checks
distinguish the pair.
Symbol exchange is only an additional structural test, not a theorem about
zero-blank input. The520 objects include83 named designs,419 research
auxiliaries,14 rejected classes and4 seeds; they are not520 independently
verified consistency constructions.

The corpus is pinned. It recognizes complete numeric five-column tables
and documented explicit JSON tables, including recursively nested ZIPs.
It is not a claim about arbitrary generators, prose-only or opaque formats.
The filed93-packet corpus is accounted for by its pinned catalogue; the
four current incoming archives and126 further PA input files were freshly
parsed and checked against their Git identities.

The temporary environment reset during packaging. Positive constructions,
their checks, the corpus, novelty and exact rejection cycles were faithfully
rebuilt from pinned surviving sources and rerun. Earlier unsuccessful search
counts and some exploratory counterexamples are explicitly retained
previous-run records; their lost raw search trees are not claimed present.
No finite search in this package proves that a193-state machine is impossible.

DELIVERY-SNAPSHOT SUPPLEMENT
----------------------------
The PA/docs tree is unchanged at the final inspected head; the three added
incoming archives contribute AX11GDH/GDHS/GDHF/GDHR, LCGMS/LCGSMS, and
H5X/JH5X. Their complete explicit-text/JSON screen adds eight194 classes,
all distinct from both delivered machines. A new runtime193 class remains
a rejected research candidate. Changes to98 Lean/Markdown/shell/Python
files outside PA/docs add no changed explicit-table input of the recognized
formats. The evolving Lean changes were not re-audited as a new theorem.

The witness supplement removes the old logical obstruction for the coupled
dual-head+H5X family. It supplies explosion independently of the old first
head. Fresh finite logical replay and a focused two-tree grammar repricing
are included; their best nominal prices200 and205 yield no smaller machine.
The marker split/merge composes with both new constructions but remains194.
The complete mathematical comparison and scope are in report Section11.
