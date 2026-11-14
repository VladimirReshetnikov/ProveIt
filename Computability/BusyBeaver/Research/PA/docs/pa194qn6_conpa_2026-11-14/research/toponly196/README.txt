TOP-ONLY SHIFT: 196-STATE RESEARCH PROTOTYPE
==========================================

This is a negative state-count result from the current research, separate
from the accepted PA194QN6 construction. The direct top-only Shift design
has 196 working states, 392 binary transitions, start 0 and separate halt 196.
The native start/halt labels are 74/254. The tape is two-way infinite and
all zero initially, with head 0. Every transition moves one cell left/right.

SOURCE CHANGE

The ordinary separated-head coefficient-four calculus and AX emitter are
retained. Modus ponens uses N's no-push controller: success returns
(b,w,b,0), b=d+x. Shift halts exactly when the visible top t equals 1;
otherwise it returns (h,tail(w),d,head(w)).

The source node168 transfers old T to X, old H to T, and X to H, so the
inherited destructive comparison tests old T rather than T+H. node163
uses node54 rather than node55 to avoid pushing a dummy zero. The six
changed/added native rows are shown explicitly in build.py.

The original primary decoder has 67 raw AX readers and seven compatible
folds. The modified fixed program needs 136 controls, giving 203-7=196.
An additional one-history helper-fold scan found no accepted further fold.
That finite scan is not a state lower bound.

REPRODUCE

  python3 -B build.py

Python 3.10+ and its standard library suffice; keep assertions enabled.
No network, repository checkout, solver or proof assistant is needed.
Use --output PATH to write the rebuilt artifacts elsewhere.

The command checks all 4,754 primitive outcomes across 3,653 source sites,
28 complete local fold cases, and the full literal blank-start tape.
It emits dense/native/raw tables, source nodes, paths, instructions,
fold certificates, label map and an observed receipt.

EXACT EVIDENCE LIMIT

The full construction checker was run for this prototype. Its generic
arithmetic blocks use the inherited interface; their literal rows remain
unchanged. The separate independent block engine used for PA194QN6 was not
replayed for this prototype, and no separate end-to-end Con(PA) endpoint
or novelty claim is presented here.

The main no-push proof-word construction adapts at the abstract level:
AX's generated entries are never 1; Push, Pop and the axiom selectors remain
safe; the reserved-zero MP word returns the consequent; final Shift halts
on a derived 1. In the two-Shift MP fragment, top-only Shift simply reaches
the required premise store even when its antecedent is 1. This mathematical
observation is a design note, not an additional executable proof compiler.

PROVENANCE

Pinned ProveIt revision 2337ce611a26e308697ccbddb2a1636f989f01c3.
The primary grammar/folds come from
Computability/BusyBeaver/Research/PA/docs/pa194hs_conpa_2026-11-13/construction/inputs/.
The frozen base source DAG comes from
Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean.
The primary raw table is reconstructed from the same grammar and the
upstream PA196 fixed program. compiler.py, symbolic_runtime.py and support.py
are inherited verification code; retained notices are under licenses/.
build.py and this top-only source/table modification were made in the current
research. The package is a source/table/receipt supplement to the main report.
