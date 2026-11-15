# Two source-preserving 194-state designs

This directory contains **PA194ORMP** and **PA194ORMPLC3**, two complete binary,
single-tape, two-way, zero-blank Turing machines. The state counts include
initialization and exclude the distinct halt label. No justified machine
below 194 states was obtained in the recorded searches.

| Quantity | PA194ORMP | PA194ORMPLC3 |
|---|---:|---:|
| Working controls / transitions | 194 / 388 | 194 / 388 |
| Resolved source instructions | 3,671 | 3,671 |
| Arbitrary-register source outcomes | 4,778 | 4,778 |
| Source addresses changed from revised AX11H | 154 | 449 |
| Whole blank startup transitions | 58,014 | 58,010 |
| Independent symbolic events | 1,101,819 | 1,100,304 |
| Maximum symbolic events per outcome | 403 | 403 |
| Minimum positive duration constant | 3 | 3 |

The dense tables are `machine/machine.tm` and `accelerated/machine.tm`.
Working states are 0 through 193, the start is 0, and halt is 194. A row is
`current_state read_bit write_bit L_or_R next_state`. The head starts at cell
zero on the all-zero infinite tape. Native labels 74/84/254 are the start,
source boundary, and halt; the supplied label bijections introduce no new
physical controls.

Dense SHA-256 values:

- PA194ORMP: `a0473681d6d5fb68e5fccfc473f35bc67aa48083d847e349ba3c52865f293629`
- PA194ORMPLC3: `6d8a8cf2f5578ccdc28dd7025bc41a7c279dfbc09c5d3893cb965d70292d10f4`

## What changes

PA194ORMP jointly rebrackets the operand routine and the modus-ponens routine.
The operand code changes from `((A,(B,C)),D)` to `(A,(B,(C,D)))`; MP changes
from `((E,F),(G,H))` to `(E,(F,(G,H)))`. The operand routine's hidden
backward-history use is repaired as part of the construction. The complete
source array, including the zero and positive decrement successors and every
counted-return target, is unchanged. The count is 135 fixed controls plus 66
AX readers minus seven simultaneously checked folds.

PA194ORMPLC3 additionally rebrackets the four-increment loop tail, retags its
61 counted continuations from depth 2 to depth 3, changes a history selector,
and applies three exact local accelerations. All 3,671 *resolved* instructions
still match revised AX11H. Its source opcodes are therefore not claimed to be
byte-identical: the retagged continuation syntax is explicitly checked.

Both tables are different from all 548 spanning 194-state transition-graph
classes in the fresh pinned corpus, and from each other, under the enlarged
structural comparison allowing every possible start root, arbitrary state
renaming, reflection, symbol exchange, and ignored final-edge decorations.
The census and exact comparison receipts are supplied elsewhere in the outer
research package. Symbol exchange is used only for this structural comparison;
the machines' semantic specification keeps zero as the blank symbol.

## Mathematical conclusion and proof boundary

The new written relative theorem in `relative_proof.tex` proves in iPRA that
each new machine halts from blank tape exactly when the exact revised AX11H
machine does. The direct parent has dense SHA-256
`c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a`.
`verify_relative.py` binds that table and its entire source graph directly to
the supplied revised calibration archive, whose SHA-256 is
`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.

Composing the relative theorem with that inherited written AX11H calibration
gives the requested iPRA equivalence between nonhalting and its explicitly
mapped Foundation `Con(PA)` sentence. This is an ordinary mathematical proof
with reproducible symbolic certificates; a newly completed end-to-end Lean
theorem is not asserted. The absolute PA proof translation and event-rule
soundness remain credited to the retained calibration manuscripts. No
assumption that PA is consistent enters either relative theorem.

## Reproduction

Python 3.10+ and the standard library suffice. Run with assertions enabled.
From this directory:

```sh
python3 -B reproduce.py --output /tmp/pa194_ormp_replay
```

The full command rebuilds both machines, compares their exact frozen tables
and sources, independently replays all 4,778 source outcomes for each new
machine and the parent, derives all four generic list traversals from literal
rows, and verifies the direct parent binding and arithmetic clock premises.
The literal replays can take several minutes.

Individual commands are also available:

```sh
python3 -B build.py --output /tmp/pa194_ormp
python3 -B build_accelerated.py --source /tmp/pa194_ormp --output /tmp/pa194_ormplc3
python3 -B check.py /tmp/pa194_ormp
python3 -B check.py /tmp/pa194_ormplc3
python3 -B check.py parent --output /tmp/pa194_parent_replay
python3 -B verify_relative.py --candidate /tmp/pa194_ormp --parent-replay /tmp/pa194_parent_replay --output /tmp/pa194_relative.json
```

The endpoint inspector verifies every nonhalting padded address against two
independent source resolvers, zero head displacement, zero address overflow,
all nonnegative affine duration vectors, and the absence of a halt edge from
every nonhalting contract and expanded one-block traversal. It checks all
recorded parent duration fields against the fresh parent replay. It does not
substitute finite tests for the written arithmetic induction argument.

## Files and provenance

- `machine/`, `accelerated/`: complete new tables, source trees, resolved
  instructions, label maps, startup evidence, and independent contracts.
- `parent/`: exact revised AX11H artifacts extracted unchanged from the retained
  calibration archive; `parent_replay/` contains the fresh independent replay.
- `inputs/`: the ORH construction inputs from the current incoming report.
- `vendor/`, `independent_vendor/`: attributed construction and literal-checker
  modules, with no network or repository dependency.
- `relative_inspector.py`: the retained finite endpoint inspector; the new
  wrapper extends it to the joint designs and exact direct parent binding.
- `calibration_AX11H.zip`, `calibration/`: the exact inherited written proof
  archive and the principal proof manuscripts extracted for convenient review.
- `PROVENANCE.json`, `licenses/`: source paths, pinned revision, and retained
  author and license notices. The mathematical calculus and compiler/runtime
  infrastructure are inherited; the new contribution is the joint designs,
  their fresh complete verification, comparison, and relative proof.

Repository snapshot: `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`.
