# Actual DagPerm versus p215 control catalogues

26 October 2026. Read-only supplement to the frozen whole-root proposal
`c222-dagperm-control-proposal-20261026.md` (379e99bc11449432073342bade242393a6456711ebb51ad769f242d749c8683b).
No Lean source, prerequisite object or Git state was changed. No Lean compiler,
historical generator or archive program was executed.

ROOT suggested comparing the fully resolved actual catalogues before planning
a new internal tree simulation. I read the complete current
`KSource215Program.lean`, rechecked the physical-register and path-successor
definitions, and wrote a separate finite audit against the literal source.
The earlier root audit independently agreed with the occurrence-exit layout.

The result is more specific than equal leaf counts:

- DagPerm has root 0, 487 nodes and depth 178; p215 has root 178, 179 nodes
  and depth 47. Both unfold to 4,751 leaves within their actual ptree fuel.
- Their numbered rows are not literally equal. Exactly 512 rows differ.
  All successor fields agree, including halt 0 and positive root restart 1.
- The differences are exactly 256 disjoint adjacent pairs of distinct-register
  INC instructions in opposite order. The first pair is at controls 34/35:
  physical registers 8 then 5 versus 5 then 8.
- Each first instruction proceeds to the second, and each second proceeds to
  the following control. No other control edge enters a pair's second
  instruction. Root control 1 is not such an interior.
- A root-preserving, edge-labelled, opcode/register-preserving control
  renumbering fails. Deterministic successor propagation first reaches a
  mismatch at control 4706 on both sides. Thus ordinary PC renumbering alone
  cannot justify the bridge.

The current row SHA256s, with compact JSON encoding, are:

| Catalogue | SHA256 |
| --- | --- |
| DagPerm | 42bcd1c057e73b82f6e13d151dbe280f1d30e06784575e788dbe2a8430704dcd |
| p215 | 7bbbab9793f6e6ec2b82593b9ad51b8845753b1a1658ca40517adf30a12c938f |

The complete pair list, source pins, failed literal-isomorphism diagnostic and
all successful finite checks are retained in
`c222-dagperm-control-plan/p215-control-compare.json`
(b3f9921cc61e4b935f9a43971b7616fe2b696f99e1531bee1d3f980497d6bae2).
Its fully read script is `p215-control-compare.py`
(72f8a04cca56eec496a92f382452cfa67b733c4dd1d1b3ae959cad9c40f4cffe).
The initial comparison version and output are also preserved separately.

## Existing internal theorem already fits

A new generic INC-commutation simulation is unnecessary.
`ArithmeticControlBisim.segment` accumulates increments before the next test
or halt. Its `checkEntry`, `checkFrom` and `halts_iff_of_check` already turn
a finite segment certificate into halting equivalence in every internal
model of IΣ1, with genuine represented state relations and positive segment
clocks. This module is already among the authenticated fresh prerequisites.

The source audit constructs a simple candidate certificate at root 1 and
every successor of a test instruction. There are 2,850 distinct controls.
At each entry the two sides use the same control and explicit nine-zero
offset vectors. Both straight-line segments, with fuel 6, finish at the same
test or halt and have exactly equal accumulated offsets. Every test branch
returns to a certificate entry. Use literal nine-zero vectors rather than
`[]`: the checker's normalization returns a nine-element zero vector, and
`entryIs` compares those lists literally. Root entry is index 0.
Canonical candidate-entry SHA256 is
22677a305a6889a1d731f1d78467314bca4ae1f9a889705fffed70d61065b6db.

This is currently a finite audit, not a proved `checkFrom = true`. A later
separate leaf can bind both concrete table definitions, prove their complete
catalogue identities and the finite check, then instantiate
`halts_iff_of_check` with actual `controlRun`, file operations and graphs.
Its conclusion would compare actual DagPerm and p215 control interpreters
for every internal starting file and internal time witnesses. It would not
by itself prove the 215 Turing machine's register/site/boot simulation.

## First checkpoint and remaining boundaries

The previously proposed `ArithmeticDagControlPerm222` checkpoint remains
unchanged: the actual fixed whole DagPerm table, unconditional root occurrence,
positive restart exits and represented interpreter. Its frozen cache plan has
138 modules / 95 Foundation modules, 137 reused modules with 422 artifacts,
39 external boundaries, and one explicitly proposed unchanged-source
`PackedTables` refresh. The present comparison adds no compiler work to that
first checkpoint. A later p215 table leaf needs its own exact selected-cache
audit before execution.

The root dispatch and EnumStepPerm222 internal equivalence, its positive-clock
argument, the remaining literal 215-machine simulation, source-ZFC calibration,
Pell arithmetization and HA proof-existence endpoint all remain separate.
The 1,426 normalized-tree certificate is not used as an assumed internal
semantic premise. The simpler segment-certificate route above is a concrete
replacement plan for that part only.
