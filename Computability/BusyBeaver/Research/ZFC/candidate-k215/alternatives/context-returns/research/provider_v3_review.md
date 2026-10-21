# Independent audit of the five-row engine variant

## Verdict

PASS. `research_machine/build_provider_v3.py` was independently read and rerun successfully. The emitted table has 215 working states and SHA256 `da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627`. Its five modified transition rows admit six exact finite context cases, because state13/read1 splits according to the preceding tape symbol.

This is an ordinary finite local proof plus a universal composition argument. It proves halting equivalence from the blank start to the accepted native K215 table. It does not by itself replace the accepted table's logical calibration or claim a new kernel-checked proof of ZFC consistency equivalence.

## Precondition audit

For four entries, every incoming transition in both tables writes the required neighboring symbol and moves toward the entry cell. Because none is the initial state, the one-step predecessor guard holds on every reachable occurrence.

For state13/read1, all two-transition incoming histories imply either the left neighbor is one, or the left neighbor is zero and its left neighbor is one. The backward enumeration preserves the latest write at each tape position via `setdefault`. It ignores read compatibility and therefore enumerates a superset of realizable histories; proving the guard for this superset is sound. Its only read-one filtering discards histories whose forced final scanned symbol is zero. The check separately establishes that the initial state cannot reach13 before two transitions have occurred, in both tables.

## Whole-tape block audit

For every context case, every tape read during either local block lies inside the explicitly specified finite context. The two traces terminate in the same state, at the same head displacement, with exactly the same contents of every supplied cell. No exterior cell is read or written, so equality extends to every arbitrary exterior tape. These are complete-tape statements, not merely matching control-state endpoints.

Every block interior avoids all five modified rows. Durations are positive, and the common endpoint is reached in finitely many transitions. Consequently synchronized runs can be decomposed successively at modified entries: unchanged transitions agree step for step, and changed entries agree after the certified finite blocks. The reachable-entry guards apply independently to both tables each time. This gives a stuttering simulation in both directions and therefore equivalence of halting from blank.

The state13/read1 context with preceding zero uses two additional transitions in the variant. This is an actual change to execution, not a state-name permutation. Other local cases preserve their certified block duration. The novelty or practical value of the altered engine wiring should be described separately from the mathematical equivalence proof.
