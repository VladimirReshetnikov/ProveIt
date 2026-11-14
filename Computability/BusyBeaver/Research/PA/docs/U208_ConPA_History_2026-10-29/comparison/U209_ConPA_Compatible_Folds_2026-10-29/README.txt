U209: three compatible decoder reductions
Prepared for Vladimir Reshetnikov, 29 October 2026

RESULT
======
An explicit 209-working-state, binary, one-tape Turing-machine candidate for
Con(PA), including blank initialization. Dense states are 0 through 208;
209 is the separate halt. There are 418 total transition rows. The tape is
indexed by the integers, blank is 0, the initial state and head position are
0, and only left and right moves are used.

Read report.pdf for the full comparison, new construction, proofs, inherited
logical calibration, verification evidence, and complete transition table.
The editable source is report.tex plus paper/transition_table.tex.

WHAT IS NEW
===========
The three supplied U211 proposals independently delete native states 180, 181, and 218
from the same U212 parent, using incompatible source layouts. A new closed
source association preserves all three helper contracts simultaneously:
181 -> 220 via 129; 218 -> 157; 180 -> 163 via 211. Native 215 now hosts the closed
tail (218,116), freeing 163 for (90,211). The result deletes all three states.
The 3,909 source primitives and their complete control-flow graph are unchanged.

PROOF STATUS
============
The final machine has a complete new mathematical reduction and fresh
executable symbolic-induction evidence. The direct local quotient from its
reassociated 212-state precursor is proved on every common initial tape from
state 0. Source/runtime/startup checks connect the final table to the specified
inherited numerical proof search. Composing with the supplied numerical-
calculus and Theory U/PA finite-refutation translations gives the intended
PA-formalizable consistency biconditional.

This archive does not supply a newly compiled Lean, Rocq, MM0, or internal-PA
endpoint certificate. The machine searches the inherited native calculus D_U,
calibrated via unrestricted covering plus irreflexivity; it does not newly
compile the separate positive dyadic stream in the unary-theory report.
Actual nonhalting follows if PA is consistent. No global minimality or
priority claim is made.

REPRODUCE OFFLINE
=================
Python 3.10+ and the standard library are sufficient. From this directory:

    python3 reproduce.py

The default run verifies the manifest, rebuilds the machine, compares exact
delivered bytes, checks all three input proposals, replays independent local
and source/startup audits, and freshly derives every universal primitive
contract. It compares the new case records with the saved data. No network,
discovery search, solver, or proof-assistant installation is required.
Allow several minutes depending on the computer.

    python3 reproduce.py --quick

Quick mode explicitly skips the universal runtime replay. It is not a
substitute for the full command. The full symbolic engine requires enabled
assertions: do not run it with -O or PYTHONOPTIMIZE. The independent finite
checkers are separately replayed with -O to ensure their explicit checks remain.

Generated checks go under build/ and leave the delivered evidence unchanged.
The manifest covers the frozen payload, excluding itself and generated build/
or TeX auxiliary files. Verify the supplied PDF before rebuilding it, since
TeX metadata can change the PDF hash.

To compile the PDF:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

KEY EVIDENCE
============
209 working states; 418 literal rows; all 209 graph-reachable.
3,909 primitive sites; 197 distinct source subtrees; 5,083 successor edges.
5,084 arbitrary-natural primitive contracts; 1,250,049 symbolic inference steps.
418/418 literal rows covered; minimum affine duration constant 5.
48,140 literal blank-start transitions exactly matching U212.
414 ordinary old rows and 10 special local cases checked; 12 corruptions rejected.
Source depth 42; maximum consecutive-zero run 6; 3,096 changed addresses from U212.

FILES
=====
machine/u209.tm             Primary dense literal table.
machine/u209.native.tm      Same machine with inherited native labels.
machine/prefold212.native.tm Exact precursor for the direct local proof.
machine/sites.json         Exact final 3,909-leaf source.
machine/state_map.json     Native/dense isomorphism.
machine/construction.json  Deterministic source, layout, and fold ledger.
code/                     Builder and independent/reproducible checkers.
inputs/                   Pinned common U212 input table/source and provenance.
evidence/                 Fresh local, source/startup, universal and replay data.
comparison/               Pinned GitHub identities and proposal comparisons.
reference/                Four original source ZIP archives, unchanged.
licenses/,NOTICE.txt       Inherited licenses and attribution.

IDENTITIES
==========
Source repository revision:
da4ab9dd68ccfc47ac852118601eaf1fdae53795

Final native table SHA256:
d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16

Final dense table SHA256:
5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08

Final source SHA256:
cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164

See the Further research questions section of report.pdf, especially a kernel
certificate for the exact endpoint and constrained synthesis of another
compatible decoder reduction.
