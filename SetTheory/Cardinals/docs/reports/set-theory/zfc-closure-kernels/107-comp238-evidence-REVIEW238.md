# Independent review of the Boundary239 → 238 composition

## Review conclusion

The concrete state reduction is sound on the proved execution domain. I found no missing local context premise, truncated-tape comparison, zero-time simulation problem, or unverified row edit in `composition_check.py`. The required nonlocal right-neighbor guard was independently rerun on the exact Boundary239 input, rather than inherited from the different Rotation240 input. It passed. The finished 238-state table also has a completed direct unbounded instruction proof and complete blank-tape initialization checks.

The accepted conclusion is an ordinary mathematical construction of a 238-working-state binary blank-tape machine, with halting equivalent to the inherited calibrated proof-search source. Composing that conclusion with the specifically identified source/calculus/ZFC calibration gives the requested nonhalting–Con(ZFC) biconditional. This review does not claim a newly compiled Lean/Rocq theorem for the binary table, a new serialized object-theory proof, or an independent rebuild of every inherited logical dependency.

## Material reviewed

I read the entire independently written `composition_check.py`, the unchanged affine/list engine and runtime helper used by the guard driver, the full adapted guard driver, the source agent’s construction and proof fragment, the completed direct-runtime and source-control receipts, the pinned `RegisterPath.lean` semantics, and the pinned `CalibratedRotation240.lean` endpoint. I also completed the universal guard execution myself. The root and source agents executed the independent construction, initialization, and direct-runtime checks reported here; I reviewed their exact receipts rather than presenting those executions as my own.

The exact inherited-label input table has SHA-256 `d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719`. The reduced inherited-label table has SHA-256 `069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c`. The canonical 238-state table has SHA-256 `909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08`.

## Exact construction and finite local proof

The parser checks binary symbols, one left/right move per row, duplicate rows, a complete pair of rows for every working state, the start convention, and a unique target without outgoing rows. The expected output is reconstructed by deleting state 169, mapping every target 169 to 80, and replacing rows 80/0 and 91/1. Comparison with the exact new table establishes that the only retained-row changes are 80/0,91/1, 147/0. There are 473 unchanged retained rows. Relabeling and the entire canonical transition relation are independently checked, not inferred from an output filename or state-count assertion.

The syntactic predecessor invariant is checked on all admitted Boolean windows. The nine-cell window [-4,4] is sufficient: the old invariant needs at most three cells behind the head, and one transition moves the head by one cell, so the postcondition cannot inspect outside this window. Every assignment of the exterior tape restricts to one enumerated window. Initialization at 95 is vacuous. The complete incoming-row inventory is also verified directly. The result therefore proves an inductive invariant for every old tape at start95, not merely an observed invariant from the blank run. The recorded number of admitted state/window checks is 121,024.

Each exceptional block is checked on every assignment satisfying its stated guard in the five-cell footprint [-3,1]. Before every old or new step, the checker requires that the read position lie inside the represented footprint. It compares the complete resulting dictionary, as well as the head and mapped state. No exterior cell is read or written, so agreement of that dictionary entails agreement of the entire infinite tape. There are 22 assignments across the four blocks. Their lengths 5, 3, 5, 9 are all positive. An attempted interior halt would fail because a transition must exist at every prescribed internal step. All 474 other old rows commute exactly with the state map in one step.

The guard needed by the169/read1 block is explicitly listed as a separate obligation in the composition receipt. The local checker does not quietly treat the stronger runtime guard as a consequence of the syntactic predecessor invariant.

## The universal guard on the changed source

The guard audit uses Boundary239’s exact table and exact source-site file. Its structural source-tree validation repeats the original checks with the new source pin; both affine/list engine and helper bytes remain unchanged. The table has 239 working states, the source has 6,455 leaves of maximum depth 48, and the source identity/calibration remains a separate checked component.

At every symbolic visit to 169, the driver requires rightward orientation and a normalized explicit run. If it reads one, the run length has nonnegative affine coefficients and constant term at least two. Thus the neighboring cell is one for every assignment of the independent natural parameters. The completed run encountered 32 nonvacuous such visits, with minimum constant term 23.

No169 visit can be omitted by the accelerated proof rules. Neither 169 row is a unary self-loop. All four generic one-block list traces are rederived from the exact table and checked to exclude 169, as are their entry states. Unary-run induction and finite-list induction therefore preserve the instrumentation’s coverage. Every original whole-tape instruction endpoint and positive-clock assertion remains active.

The completed receipt has status `PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD`: 8,386 guarded cases, 2,247,513 symbolic rules, all 478 old rows, minimum constant instruction duration 13. The exact 409,691-step blank initialization additionally checks all six 169/read1 visits. These are quantified affine/list proofs and a separately designated finite prefix, not a general nonhalting inference from bounded simulation.

## Global simulation and the blank prefix

Map 169 to 80 and leave every other old state, the head, and the tape fixed. At an old configuration satisfying the invariants, the appropriate positive block reaches the image of its one-step successor. Induction constructs new checkpoints at times τ(n), with n≤τ(n)≤9n. Because no simulated block halts internally, an infinite old run gives an infinite new run, while an old halt gives a new halt. Positivity is essential here and is supplied by the explicit block lengths.

The root checker compares all 409,692 old blank-prefix checkpoints with their new counterparts, including the entire finite support of the tape. Its independent dense interpreter uses the canonical table and checks the represented boundary before every step. Consequently this finite dense run cannot read or write an omitted exterior cell. Its final support equals the sparse result exactly. The common full dispatcher frame occurs after 409,835 new steps, with the 144-step difference accounted for by the four exceptional visit counts (18, 12, 6, 3).

The frame parser verifies all nine physical register blocks and all 167 spare blocks; its final support condition excludes stray one-cells outside the parsed frame. The marker at -6, head at -5, and header at 176 give the runtime gap parameter 117. The specified physical register map sends the checked physical values to the calibrated logical seed (3, 0, 0, 0, 3, 0, 0, 0, 0). The source-interface receipt independently identifies this same mapping and seed from the pinned definitions.

## Direct runtime, source semantics, and the logical endpoint

The finished 238 table separately passed 8,386 unbounded instruction cases with 2,255,513 symbolic rules, minimum constant duration 13, and all 476 rows covered. The represented domain includes arbitrary natural primary values, arbitrary additional gap, an arbitrary first spare value, and an arbitrary finite spare tail, with zero exterior. For a decrement, the zero case and the positive 1+n case exhaust all natural values.

The source bridge must preserve the actual `RegisterPath` consumed-path convention, including truncation at the encountered leaf. Equality of instruction order alone would be insufficient. The reviewed source-control receipt checks 8,385 nonhalting control edges and one halt descriptor at each of 13 stages, with 25 rotations total. It explicitly certifies canonical successor paths: discarded suffix bits are zero. Hence the next source leaf’s zero-extended path represents the same physical tape prefix. This closes the clean-frame concatenation argument; it is a required premise, not a consequence of the binary state-count calculation.

The source changes preserve all primary registers and instruction successors. Spares remain nonempty, increments append a value-one spare, and the gap remains nonnegative. Concatenating the unbounded instruction lemmas is therefore legitimate. Strictly positive durations prevent an infinite source run from collapsing to finitely many binary steps.

The pinned `CalibratedRotation240.halts_iff_zfc_refutation` identifies the inherited register source at `LogicalSeed246.initial` with a refutation in its explicitly encoded ZFC proof system. The supplied source interface identifies the actual ordered source data and seed, and the source certificate transfers that endpoint to the shorter source. The runtime and initialization arguments transfer it to the 238 table. The ordinary in-ZFC biconditional uses the inherited logical calibration and the formalizability in ZFC of these finite calculations and natural/list inductions. It does not infer actual consistency of ZFC or actual nonhalting without that consistency assumption.

## Independence and remaining scope

The four-block/checkpoint verifier and the dense initialization implementation are independently written checks. The direct unbounded runtime and the additional guard audit share the inherited affine/list proof method and runtime helper; they provide different proof routes and obligations, not two independently trusted proof-assistant kernels. Their shared mathematical engine should remain visible in the attribution and provenance.

No unclosed new premise remains in the A239→238 composition. The remaining inherited dependency is the source/calculus/ZFC calibration described above. A closed Lean/Rocq endpoint for the 238 binary machine, an internal serialized ZFC derivation, and any claim of state minimality are outside the completed result. The unsuccessful bounded search on the other 239-state branch has no lower-bound implication.

## Review artifact hashes

- `composition_check.py`: `87b3e01b01565bcbe3754fb250eb2240e6d908ac68e4e44346769ea849591d70`
- `certify_guard169_A.py`: `4d7254f0fa8d37ffc226e50a5ff36e9d49f650f15ea4018444cb3268214b8444`
- `guard169_universal.json`: `e3a250889f518752df45902483d64a49c45625cdd5fc7b44785ce140f8d87eb9`
- `universal238.json`: `ab0e8f686ceb095b35d8a7d54cbe01b042d4654fc0198f354c6263da58500f75`
