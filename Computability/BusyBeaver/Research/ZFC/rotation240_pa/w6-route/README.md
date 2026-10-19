# W6: exact Rotation240 control interpreter to binary arithmetic run

Source-only implementation map, 2026-10-19. No supplied script, guard, compiler, simulator, or publisher was invoked. `catalogue-comparison.json` records an independent source-data calculation, not a Lean proof. The supplied sources remain unchanged. Root reports Startup240 checked and published; this note does not independently re-audit that execution.

## Exact interface and the first concrete result

The final target, for every `IΣ₁` model `V`, is

```lean
(∃ t : V, ArithmeticCantor.first (ArithmeticMachineRunRotation240.run t) = 0) ↔
  ∃ n : V, ArithmeticControlTable.controlRun ControlBisimRotation240.tableR n
    (ArithmeticControlFile.liveValue 1 (ArithmeticL2.enc seed)) = 0
```

Here the internal record `seed : ArithmeticL2.AS V` is `⟨3,0,0,0,3,0,0,0,0⟩`. Its physical fields are exactly `[0,0,0,3,0,0,3,0,0]`. Logical register `r` is field `physOf r`, with permutation `[6,2,0,4,3,7,8,5,1]`. `LogicalSeed246.seed` itself is the external Nat record, so an internal seed definition or explicit field casts are necessary. Live logical values use `cantor control file + 1`; logical halt is `0`.

The own strict parser independently expanded all 203 stored rows and compared every packed row, including **both successor fields on non-test rows**. All 6,455 four-field rows match `ArithmeticControlTable.rowOf TreeRotation240.tree`. There are 1,931 tests, 2,596 increments, 128 breaks, 1,799 continues and one halt: 8,386 branch guards in total, depth 51. Raw register fields are below 9, unused high slot bits are zero, and all successors are in range. Initial control 1 is path `000`, edge `decnz 8`, packed row `(2,1,3,2)`; the unique halt control is 6,321. These are fresh source-data observations, not inherited Prog254 control numbers.

Own reader history preserves three stopped metadata drafts: decimal-versus-hex literal syntax, a regex argument-order mistake, and a redundant hand-written initial-row expectation. The complete four-field comparison was unchanged by the last correction. All original source files were rehashed at close.

## Smallest module order

| Unit | Concrete deliverable | Reuse and fresh obligation |
|---|---|---|
| A. `Rotation240ControlCatalogue` | Exact packed-table equality and a source/row lookup interface | Drop owns this. Use `ControlCatalogue` ranks and cached subtree counts, not `List.idxOf` or old finite-control numbers. |
| B1. `ArithmeticOneRegisterBlocksRotation240` | Total internal repeated `011` code; concatenate/append laws and Nat bridge | Source/audit are frozen separately, 9 probes/11 callers. It adapts the fixed Blueprint proof of `ArithmeticZeroRegisterBlocks254`, with update `8*x+6`. No machine theorem is assumed. |
| B2. `ArithmeticMachineScansRotation240` | Actual240 literal left/right steps and arbitrary-internal writing/unchanged scans | Root owns this. Reuse generic numeric tape algebra from `ArithmeticMachineUniformScansPerm252`, but use actual `ArithmeticMachineRunFromRotation240.runFrom` and Graph240 lookup equations. |
| C. `ArithmeticRegisterBoxesRotation240` | Internal mark, carry, rollback, positive/zero decrement and increment contracts for the nine physical fields plus internally many one-spares | New actual-machine work. Follow `Rotation240Boxes` and `RegisterMarkRotation240`; old Perm252 increment/decrement contracts have different spare effects. Split into carry/return and operation units if needed. |
| D. `ArithmeticSymbolicExecutionRotation240` | Interpret current `SymbolicRotation240` syntax and prove the erasure/soundness of its exact `sstep`, `verifies`, and `verifiesHalt` | Port the existing arithmetic symbolic proof pattern. Arbitrary internal values/gaps/counts; induction on external checker fuel. Prove exact checker equality rather than substitute an alternative checker. |
| E. `ArithmeticDispatchRebaseRotation240` and `ArithmeticControlFrameRotation240` | Site-to-canonical-entry rebasing, represented whole frame, Σ₁ relation, exact five instruction cases | Use `SitesRotation240.all_sites`, Tree240 walk binding, the new table equality, and generic path-cleanliness. Margin64, statecode85, new spare/gap accounting below. |
| F. `ArithmeticControlSimulationRotation240` | `related_step`, `related_halt`, then internal halting equivalence | Use generic `ArithmeticControlTable.spec_get` and `ArithmeticPositiveSimulation254.halts_iff`; no new logical iterator and no old `ArithmeticControlRun254`. Finish with the exact seed frame and checked Startup240. |

Do B1/B2 now in parallel with A. C is the next substantial proof boundary. D can be prepared once C's exact endpoint contracts are frozen. The existing 565-module decoder proof family is already complete: E consumes its final theorem and does **not** regenerate or replay it.

## A: catalogue equality and minimal public API

Prefer the exact statement

```lean
PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR =
  (ControlCatalogue.leafEntries TreeRotation240.tree).map
    (ArithmeticControlTable.rowOf TreeRotation240.tree)
```

The initial binding module can import `BisimCertRotation240`, `ArithmeticControlTable`, and `TreeRotation240`, avoiding the full `ControlBisimRotation240` certificate proof merely to name its table. A later alias theorem to `ControlBisimRotation240.tableR` is definitional. These upstream sources still require accepted exact object providers before a guarded child build; merged source and an upstream compile claim alone are not a fresh provider record.

Useful public corollaries are: catalogue length 6,455; initial entry/row; source acceptance and length bound; register bound; no node leaves; successor range/nonzero for nonhalts; and for each `i < 6455`, the exact lookup at control `i+1`. Obtain acceptance using `leafEntries_sound` and `SiteCoverage.allSites_sound` with `SitesRotation240.all_sites`. Obtain the next entry via `ControlCatalogue.entry_at_crank` and `TreeRotation240.walk_eq_tree`. `PackedTables.rowsOf_some` plus `ArithmeticControlTable.spec_get` supplies the internal represented step equation.

The path must be the **consumed** leaf path, with implicit trailing zeros. `rowOf` stores `crank (annotate tree) (outgoingPathOf path edge branch) + 1`, not a source-program node number. Canonicalization also needs path cleanliness/padding equality; rank identity alone does not prove equal binary tape contents.

## B–D: what actually changes in the arithmetic runtime

The machine-independent codec remains `frame q left right = cantor q (cantor left right)`, and `registerBlock v suffix = 2 * bitPrefix true (v+1) suffix`. Finite external syntax may still be `List V` of length nine. An internal model's unbounded number of spares must **not** be represented by an external `List.replicate` over a purported Nat count.

Choose the spare invariant

```text
spareTail extraCount = oneBlocks (167 + extraCount) 0
```

where `extraCount : V` starts at 0. This guarantees a following spare for physical register 8 and avoids a separate positivity invariant. Increment increments `extraCount`; other instructions preserve it. `oneBlocks` repeats `011`, so its recurrence is `8*previous+6`. The append law absorbs the newly written final block without dropping tape cells. `oneBlocks_bitsCode 167 []` supplies the ordinary finite seed comparison; model transfer remains a separate defined-function/numeral lemma.

Rotation240's ordinary `Rotation240Boxes.shift_suffix` traverses the entire suffix. Its new arithmetic counterpart needs two inductions: external induction on the fixed remaining physical fields, then Σ₁ induction on the **internal** repeated-one count (and scans on each internal register value). The positive and zero branches can exploit the fixed first spare being one. Each successful box endpoint must retain both complete numeric tape halves and a positive internal clock; the zero exterior used by `carry_end` is an explicit invariant.

The old files are named `ArithmeticMachineUniformScansPerm252`, `ArithmeticRegisterForwardPerm252`, `ArithmeticRegisterReturnPerm252`, `ArithmeticRegisterIncrementPerm252`, `ArithmeticRegisterFilePerm252`, `ArithmeticRegisterDecrementPerm252`, `ArithmeticRegisterZeroPerm252`, `ArithmeticRegisterMarkPerm252`, `ArithmeticSymbolicTapePerm252`, `ArithmeticSymbolicBoxesPerm252`, `ArithmeticSymbolicExecutionPerm252`, `ArithmeticSitePerm252`, and `ArithmeticDispatchRebasePerm252`. There is no existing `ArithmeticBlocksPerm252` or `ArithmeticTapesPerm252` module to port. Prefix246 provides Graph/Step/Run/RunFrom/Bootstrap/prefix-shift adapters, not an alternate generic internal register-frame library.

Pure `bitPrefix`, `frame`, `registerBlock`/file-code equations, fixed-field projections, and path-cleanliness lemmas can be reused or factored. Machine-execution lemmas mentioning Perm252 `actionLookup`/`runFrom` cannot be instantiated merely by changing state numerals. `ArithmeticSymbolicTapePerm252` also fixes the old `SymbolicPerm252` types: either port its normalization proof to Rotation240's syntax or prove an explicit syntax translation; the old theorem's name alone is not an adapter.

## E: exact frame and update obligations

Define a compact finite PC lookup from the bits of each exact catalogue path, using `ArithmeticControlTable.compactRows`/`lookupValue`. A proposed entry is

```text
entry q file extra gap =
  frame 85 1
    (pcValue q + bitPrefix false 64
      (bitPrefix false gap
        (2 * blocksValue [physical fields 0..8] file
          (oneBlocks (167+extra) 0) + 1)))
```

The dispatch is canonical binary state84, hence arithmetic statecode85. The path budget is64. Existing Frame254 uses statecode95 and budget40, a different literal frame. Its spare suffix starts with eight zeros and one one, followed by internally many **zero** blocks; its positive decrement appends a zero. None of those concrete choices is correct for Rotation240.

After arithmetic interpretation of an accepted site, canonical rebasing must prove this exact update table:

| Site | File update | extraCount | gap increment |
|---|---|---|---|
| increment r | physical field `physOf r` plus1 | plus1 | `digit (allOnes Q)` |
| decrement r, zero | unchanged | unchanged | `digit (allOnes (stripPath false 1 Q))` |
| decrement r, positive | physical field minus1 | unchanged | `digit (allOnes Q) + 1` |
| break k | unchanged | unchanged | `digit (allOnes (stripPath false k Q))` |
| continue k | unchanged | unchanged | 0 |

The target's extra gap argument is 1 only for positive decrement. Generalize the old rebasing budget to `64 + overflow.toNat + extra`; canonical next leaf paths still have length at most51. Use generic `RegisterPathClean.clean_inc`/`clean_prefix`/`execute_clean` reasoning and `clean_suffix`/`gap_consume` to preserve the whole padded PC region. `entry_at_crank` connects that consumed next path to the next table control. Do not replace this tape equality by a statement that only the next control number agrees.

The represented relation can follow the Frame254 shape: nonzero logical code, supported nonzero opcode, and existential **internal** `extraCount` and `gap` witnessing exact entry equality. `compact_lookup_supported` classifies the control as one of the finite standard indices. This excludes invalid/default rows; otherwise an invalid opcode can look like an immediate logical halt without a checked binary halt leaf. The relation's graph must be Σ₁ before invoking internal induction.

At the exact seed, `pcValue 1 = 0` because the first consumed path is `000`. The 181 initial zero cells become **gap117**, because the entry already supplies64 zeros. Thus the concrete bridge to prove is

```text
(ArithmeticBootstrapRotation240.bootCode : V) =
  entry 1 (ArithmeticControlFile.fileValue ![0,0,0,3,0,0,3,0,0]) 0 117.
```

The boot zipper's head coordinate is irrelevant to this numeric codec; left tape `true :: replicate 9 false` has code1. Use the already checked checkpoint identity/bootCode and numeric codec laws, then defined-function absoluteness or explicit numeral evaluation. No second 409,691-step finite proof is needed. Prove a small final equality between that physical file and `ArithmeticL2.enc seed`; this keeps broad W4/W5 imports out of the early arithmetic box proofs.

## F: final assembly and limits

Instantiate `ArithmeticPositiveSimulation254.halts_iff` with logical step/run from **`ArithmeticControlTable` at the new table**, binary run `ArithmeticMachineRunFromRotation240.runFrom`, `Halted b := first b = 0`, and the new Σ₁ relation. Its positive clocks dominate every internal proposed halting time. Required contracts are `related_live`, `related_active`, `related_step` when the next logical code is nonzero, `related_halt` when it is zero, and binary halt persistence. Existing RunFrom240 supplies zero/add/absorption. `spec_get` and the literal source cases discharge the logical equations, so a copied Prog254-specific `ArithmeticControlSimulation254` finite table is unnecessary.

This yields seed-control halting iff binary seed halting. Startup240's `blank_iff_seed_halts` then closes the documented W6 semantic interface. A fixed arithmetic sentence and IΣ₁/PA completeness corollary can follow that semantic theorem. Neither external `Core` runtime nor static packed-row agreement alone proves the all-model statement. W4/W5 scheduler identification and R2/R3 consistency calibration remain separate obligations.

Key source locations (all pinned in `source-inventory.json`): `ArithmeticControlTable` rowOf at lines183–219, controlRun at355, spec_get at479; `ControlCatalogue` leafEntries at27 and crank at96; `TreeRotation240.tree` at1258 and its walk binding at1268; `SiteRotation240` minDistance/target/checkOperation at20–65; `SymbolicRotation240.boxBits` at53; `Rotation240Boxes` carry_end/shift_suffix/increment at287/300/327; `BootstrapFrameRotation240` spares/target at20/33; `ArithmeticL2Lib254.enc` at52; `ArithmeticPositiveSimulation254.halts_iff` at104. The inventory records declaration locations mechanically, so it is authoritative if a prose locator drifts.
