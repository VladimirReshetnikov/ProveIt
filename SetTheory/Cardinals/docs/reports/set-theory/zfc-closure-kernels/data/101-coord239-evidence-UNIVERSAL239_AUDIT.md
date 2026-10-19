# Independent mathematical scope audit of the 239-state target106 machine

## Conclusion

The fresh target106 runtime check proves the required **unbounded instruction simulation**, in the ordinary mathematical sense, for the exact new 239-state table. It is not a test on a bounded collection of register values. Together with the exact blank startup, the unchanged source identification and the existing source/ZFC calibration, it closes the new ordinary mathematical nonhalting/consistency equivalence. It does **not** constitute a new Lean or Coq theorem for the literal 239-state machine. The proof-assistant endpoint remains a distinct implementation task.

The independently reviewed candidate bytes have SHA256
`76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b`.
The unchanged 6,455-leaf source has SHA256
`74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d`.
Inherited labels are start 95, dispatcher 96 and halt 254. The total binary transition table has 239 working states and 478 rows; all moves are left or right. Initialization is part of those 239 states. These facts were checked separately by `audit_input_and_boot_clock_239.py`; its receipt is `input_boot_clock_239.json`.

## Exact quantified frame theorem

For each source leaf, place the machine in dispatcher 96 at an arbitrary translated head position. The tape has a marker 1 immediately to the left of the head, the leaf's instruction bits followed by zero padding, a header 1 at relative position `64 + g`, and then blocks

\[
B(v)=0\,1^{v+1}.
\]

There are nine primary blocks, in physical order determined by
`PHY = (6,2,0,4,3,7,8,5,1)`, followed by a nonempty finite list of spare blocks. The exterior is all zero. The variable `g` is an arbitrary natural number. The nine logical values are independent arbitrary natural numbers; at a decrement site the cases are value 0 and value `1+x` for an arbitrary natural `x`. The first spare value is arbitrary and the remaining spare list is an arbitrary finite list, including the empty list.

The checker establishes a finite positive literal execution to precisely the expected next whole dispatch frame, or to the sole halt control for the halt leaf. Increment changes the designated primary value by one and appends a spare of value 1. A positive decrement subtracts one and increases the gap by one. Failed decrement, break and continue have the published source path arithmetic. Increment overflow moves the marker/head one cell left and adjusts the gap; the checker separately establishes the exact head displacement. Spare contents, marker, header and both zero exteriors are included in the equality.

The actual replay in `helper91_target106_239_full_runtime.json` covers all 8,386 guarded cases: 3,862 decrement cases, 2,596 increments, 128 breaks, 1,799 continues and one halt. It executes 2,330,575 symbolic rules, uses all 478 literal rows, and proves a minimum duration of 13 actual steps. Root's separately repeated unchanged full checker additionally emits every case's affine duration and motion; it is the preferred main receipt for the final packet.

## Why the checker is unbounded

I read the execution rules in the inherited `symbolic_runtime.py` and the helper functions it actually calls in `independent_runtime.py`. The proof rules are:

1. **Literal transition.** A run can be consumed one bit at a time only when its affine length has constant term at least one. Thus no step branches on a symbol whose existence has merely been sampled.
2. **Unary induction.** When the actual table row is a self-loop moving in the scan direction, an arbitrary natural-length run is traversed by induction on that length. The case of length zero is included.
3. **List induction.** Four one-block traversals are re-proved from the *new literal table*, with an arbitrary natural value and opaque untouched contexts. Their entries are 73, 95, 48 and 112. Each consumes exactly `v+2` cells/steps. Structural induction then gives traversal of an arbitrary finite list. It preserves the list's value sequence, with the stated temporary block format where applicable.
4. **Word identities and affine equality.** Adjacent equal-bit runs are concatenated, finite zero runs are absorbed into an adjacent infinite zero exterior, and the exact list identity `C(A)1 = 1B(A)`, where `C(v)=10·1^v`, converts the temporary format. The list identity follows by empty/cons induction. State, direction and both complete tape halves must match the target. An affine motion equality fixes the absolute head displacement.

The thirteen affine slots are a constant, the gap, nine primary values, the first spare value and the total width of the remaining spare list. Every traversal of that same list uses its same width; changing between B and C preserves width. No restriction is imposed on its length or constituent values.

The 50- and 4,000-iteration limits in the proof search bound the number of *symbolic proof rules attempted*. Success has already discharged every arbitrary run/list by induction. These limits do not bound the represented machine runtime, register values, spare count, gap or tape extent. Every accepted case has a strictly positive affine duration. An early unintended halt would prevent reaching the required target because the halt control has no transition rows; the literal/list/unary derivations cannot silently step past it.

## From leaf cases to the entire source run

A complete finite binary tree has a leaf on every infinite bit path. The separately validated tree has maximum depth 51, below the 64-cell reserved instruction region. Source paths are most-significant-bit first with implicit trailing zeros. `RegisterPath.walk` finds a leaf at depth `d`; `consume` zero extends or truncates the stored path to exactly `d` bits *before* executing the instruction.

The relevant clean-path invariant says that all bits at and beyond the consumed leaf depth are zero. It holds at the empty path and is preserved by every source step. There is a short direct proof. Continue produces a prefix of the current consumed leaf, so the next decoder follows that prefix and then only zero bits. Break first takes such a prefix and then increments it. For increment, either all bits overflow to zeros, or a suffix has the form `A 0 1^m` and changes to `A 1 0^m`. Because `A0` was a followable prefix, A is an internal tree node; the next leaf lies at or below its 1-child, and every bit after that branch is zero. The same argument handles ordinary increment and positive decrement. Therefore truncation at the next leaf discards only zeros.

Consequently a reachable source path and its consumed leaf have identical tape encodings. At the root the first leaf is `000`/`CD8`; the empty path and `000` encode the same zero instruction region. Each of the 8,386 proved leaf cases can thus be applied at the next reachable dispatch frame. This is exactly the generic `RegisterPathClean` argument in the archived attributed source, not an assumption that every arbitrary dirty interior path is sound.

Positive finite durations make the accumulated binary times strictly increasing. Determinism and the absence of intermediate halts prove both directions of the halting equivalence. An infinite source run cannot be squeezed into finitely many binary steps. Conversely, a source halt has a finite concatenation of finite binary segments ending at halt 254.

## Startup and source calibration dependencies

The new machine's blank execution must reach the genuine root frame with logical values
`(3,0,0,0,3,0,0,0,0)`, logical register tail zero, and the separately represented spare blocks. The exact target106 startup is 409,835 steps, head −5, marker −6, header 176, gap 117, 351 one-cells and 167 spare blocks all of value 1. Root independently checks the candidate's complete tape with sparse and dense simulators.

As a cross-check, my separate census checks the *entire old* 409,691-step startup and all guards for the four new stuttering blocks. Its exceptional visit counts are 18, 12, 6 and 3. The added clock is

\[
4\cdot18+2\cdot12+4\cdot6+8\cdot3=144.
\]

Together with the independently checked local blocks this predicts the same 409,835-step candidate frame. Startup is a finite exact calculation, whereas continuation is the unbounded proof above.

The calibration being reused is specifically

\[
\operatorname{RegisterPath.Halts}(\operatorname{SourceRotation240.program},
\operatorname{LogicalSeed246.initial})
\iff
\operatorname{BProv}(\operatorname{ZFCax\_s},[],\operatorname{Form.fBot}).
\]

`CalibratedRotation240` obtains this by the all-register-file source rotation theorem, the prior calibrated source theorem and `LogicalSeed246.halts_iff_zfc_refutation`. `LogicalSeed246` identifies the explicit nine values above with zero logical tail; its source proof uses the native-theory calibration, the well-founded-part comparison to ZF, and the constructible-model comparison of ZF and ZFC refutations. The underlying theory is the repository's exact standard ZFC axiom presentation, not a model hypothesis added to the machine theorem. The formula/stack safety of the seed is already supplied by `DirtyProgram254`; arbitrary physical spare values are a runtime resource and are not arbitrary extra logical source registers.

The exact source-data bridge was freshly rederived here. `source_bridge/check_source_bridge.py` reads the actual pinned `ProgramRouting245`, `ProgramRotation244` and `SourceRotation240` definitions, with their Git blob identities verified. It parses all 203 literal rows, parses and evaluates the entire `rawLookup` conditional tree, checks the bounded nodes wrapper and the actual program fields, and applies the two explicitly parsed override wrappers. Expansion from root 202 produces a byte-identical copy of the 6,455-leaf list, with maximum depth 51 and all 8,386 guarded cases. Every child index decreases; only row 4 is unreachable. The receipt is `source_bridge/independent_source_bridge.json`, alongside all three exact Lean source snapshots. Thus the runtime data are directly identified with the calibrated source, not merely accepted by hash. The source equivalence and consistency calibration themselves remain inherited proofs, as explicitly distinguished from this fresh literal extraction.

## ZFC provability and proof-assistant status

The new argument uses finite word arithmetic, induction on natural runs and finite lists, exact finite table calculations, and the source theorem already calibrated to ZFC refutation. These are ordinary arguments formalizable in ZFC with standard encodings of finite traces and proofs. Composition gives

\[
\mathrm{ZFC}\vdash
\bigl(\exists t\;\mathrm{Halt}_{239}(t)\bigr)
\leftrightarrow
\bigl(\exists p\;\mathrm{Proof}_{\mathrm{ZFC}}(p,\bot)\bigr),
\]

and hence the requested nonhalting equivalence by negation. This inference does not assume that ZFC is consistent, has an actual set model, or is sound. No uniform reflection principle is used: the calibration concerns the one fixed refutation-search computation.

An externally checked Lean proposition and a serialized proof *inside the object theory ZFC* are different deliverables. The current packet supplies the ordinary mathematical internalizable argument and executable checks, not a new serialized ZFC derivation or closed Lean/Coq endpoint for 239. The inherited Lean calibration records report only the usual `propext`, `Classical.choice` and `Quot.sound` axioms; this task has not freshly rebuilt that ancestor chain. The remaining implementation trust is the correctness of the small checker rules, Python's execution of them, and the accuracy of finite calculations/source parsing. Their mathematical content has been independently read, and the decisive local block identities have a second independently written open-tape checker. These are normal computer-assisted proof dependencies, not additional conjectural hypotheses about unbounded register sizes.

## Evidence read for this audit

- Fresh source bridge: `source_bridge/check_source_bridge.py`, `source_bridge/independent_source_bridge.json`, and the exact pinned Lean snapshots and fetch identities in that directory.
- Fresh files in this directory: `symbolic_runtime.py`, `independent_runtime.py`, `verify_helper106.py`, `helper91_target106_239_full_runtime.json`, `check_local_blocks_239.py`, `local_blocks_239_independent.json`, `audit_input_and_boot_clock_239.py`, `input_boot_clock_239.json`.
- Pinned ProveIt: `Computability/BusyBeaver/Research/ZFC/candidate-rotation240/README.md`, `calibrated_rotation240.md`, `source_rotation240.md`, `rotation240_runtime.md`, `dirty_program254.md`, and `calibrated-rotation240/history.json.gz` (the exact checked calibration source was read and its stored hash verified).
- Archived attributed modules: `code/71-qt-reference-baseline245-reference-context246-sources-lean-RegisterPath.lean`, the matching `RegisterPathClean.lean`, and `code/68-route245-reference-current-LogicalSeed246.lean` under `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`.

The runtime checker is inherited source73/source80 code, reviewed and replayed here. Its original “self-authored” comments describe its original author; they do not attribute that code to this audit. The open-tape local-block and startup-clock checkers in this directory were independently written in the present task.
