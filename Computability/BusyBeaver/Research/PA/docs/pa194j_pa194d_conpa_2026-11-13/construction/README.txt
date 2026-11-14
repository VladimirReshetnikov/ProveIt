PA194J: a 194-state source-invariant decoder redesign
====================================================

Reproduce using Python 3.10 or newer, standard library only:

    python3 rebuild.py
    python3 independent_verify.py

Run without Python -O: assertions implement the certificates. No network,
repository checkout, or installed proof assistant is needed. The second
command can take several minutes because it checks 4,755 symbolic cases.

machine/pa194j.tm is the dense literal table, with working states 0 through
193, initial state 0, and terminal state 194. It starts at head position 0
on a blank zero tape. Each row is 'state read write L/R next'. The halt
control has no rows and is excluded from the working-state count. The
native table starts at state 74 and halts at 254. The exact dense-to-native
map, including the terminal label, is machine/pa194j.labels.json.

rebuild.py uses the pinned primary PA194 table and source tree. It installs
the supplied Combined and symmetric-Shift controller, then converts ten
jump sites into zero tests of provably zero registers. It regenerates both
source graphs from the tree and independently computes both positivity
closures, each containing 263,180 pairs. Every modified source step is
identical on this closed set. See PROOF_NOTES.txt and the evidence folder.

independent_verify.py imports neither a compiler nor an arithmetic-box
oracle. It derives four unary-list sweep lemmas from the actual literal
rows, then proves the complete source-frame contracts symbolically for
arbitrary primary values, gap, and nonempty finite spare list. Both outcomes
of every decrement are covered. Two independent path resolvers check the
full instruction map. A separate bytearray simulator checks exact whole-
tape blank initialization after 60,062 transitions.

These executable certificates support ordinary mathematical proofs of
finite source and machine transformations. No new kernel-checked Lean or
Rocq endpoint is claimed. The logical calibration of the supplied PA194CS
source to Con(PA) is an inherited mathematical argument and must be stated
separately from what these scripts verify. No sub-194-state claim is made.

Provenance and attribution
--------------------------
Inputs are from VladimirReshetnikov/ProveIt at revision
17f92105e2bc4317feae6c219cb2143437b482ff:

- inputs/Program.lean: PA/jamesyc-upstream/pa196/PA196/Program.lean.
- inputs/pa194.native.tm and pa194.grammar.json: the primary packet
  PA/docs/pa194_conpa_2026-11-13/construction/.
- inputs/pa194CS.instructions.json: incoming
  pa194_new_designs_2026-11-13.zip, secondary/pa194CS/machine/.

The published Combined six-row edit and symmetric-Shift fold of state 41
into state 330 are reproduced explicitly in rebuild.py. The source-node
parser and structured successor construction follow those packets'
documented algorithms.

The preserved reference files contain the independent unary-list runtime
and arithmetic/interval source resolvers shipped in incoming
pa194c_conpa.zip, verification/independent/reference/. Their original README
and license notices are retained in that directory.
