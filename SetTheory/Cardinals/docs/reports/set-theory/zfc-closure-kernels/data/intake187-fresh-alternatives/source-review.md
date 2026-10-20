# Source141 portable execution and engine comparison

Reviewer: opening_encoder. This is an independent source/API and fresh direct-leaf replay review; I authored only the local extraction/launch adapter. Root owns intake placement. No canonical candidate was modified.

## Exact inputs and execution boundary

Pristine archive extraction: `/tmp/zfc-intake187/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20`. All supplied execution uses the separate unchanged copy `/tmp/zfc-intake187/opening-execution/packet`. The embedded K219 baseline ZIP was independently safely extracted into `opening-execution/recovered`; its exact accepted hash is `04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b`. The baseline source/table match the current accepted K219 pair (`0f6d9d99...` / `b255f8ee...`). The two runtime modules and original label map were copied from the previously accepted K221 extraction, with exact pins rechecked. Own read-only nested-ZIP member comparison then established that all three are byte-identical to their members in this new packet’s embedded K220→K221 ancestry (`runtime-input-lineage.json`). No ancestor proof suite was run.

I read the complete portable construct, source, canonicalization, runtime and reproduce scripts; all four selected verification scripts; and the exact two runtime dependencies. The executed leaf closure uses Python's standard library only. Explicit output arguments confine writes to scratch; temporary malformed-certificate controls use a scratch TMPDIR. The driver records separate raw stdout/stderr, elapsed time, exit status and timeout status. It sets `-B`, removes optimization/PYTHONPATH overrides, and uses a new process group with a 180-second hard cap for each full runtime job (60 seconds for each small job). The delivered wrapper, manifest/checksum suites, historical baseline wrappers and proof assistants are not invoked. Consequently the wrapper's `SELF_CONTAINED_THREE_ALTERNATIVES_REPLAY_PASS` label is not our actual result.

Plan and exact CLI vectors are in `/tmp/zfc-intake187/opening-execution/plan.json`. The own launch/extraction sources are adjacent to this note. Runtime checking is serial, with one full runtime process at a time.

## Exact source changes

All sources have 4,744 leaves, 206 distinct DAG nodes (183 interior), and maximum depth 38. There is no DAG/state saving in this packet.

* Zero-terminal: four literal equality-macro replacements, changing only eight `CB1` leaves to `CD6`, at ordinals 4570, 4576, 4588, 4594, 4602, 4608, 4711, 4717. Each changed leaf has exactly one incoming edge in the complete new CFG, namely the zero branch of the unchanged `CD6` two ordinals earlier. Thus every reachable entry from source entry has register 6 zero. The new zero branch has exactly the old break successor and does not change any register. The source proof applies to arbitrary initial natural register vectors, not just the blank seed.
* Retagged: 81 disjoint replacements `(((I,I),(I,I)),CC2)` by `((I,I),((I,I),CC3))`, where `I=CI1`. Exactly 405 addresses and 81 continuation arguments change; every ordered ordinal CFG edge remains identical. Both open macros increment register 1 four times then return continue1.
* Composed: the complete source rewrites commute. Both orders reproduce the exact delivered tree and independently reconstruct the same ordinal list. The zero-entry predecessor proof is repeated in the retagged background. This is stronger than an inference from disjoint table patches.

The elementary open-macro explanation of zero-terminal is also sound. Put `P=(CD6,CC2)`, `U=(P,CB1)` and `V=(P,CD6)`. Positive register 6 makes P decrement and return continue1, so neither right child is reached. Zero register 6 makes P return normally with register 6 unchanged and zero; either right child returns break1 unchanged. Thus U and V have the same all-natural open contract. No exceptional register value is discarded.

The runtime wrapper deliberately calls the inherited engine’s generic `prove_blocks` and `case` APIs. It does not call that engine’s standalone CLI validator, which is specialized to an older 6,455-leaf source. The new exact table/source pins and complete source/tree/domain checks are supplied by this packet’s own direct leaves; all 4,744 occurrences and both decrement guards are enumerated.

## Literal physical tables and prior failed engines

The release normalizes upstream 301→102 and 302→120, leaving every other state label fixed. This is a bijective renaming, not deletion. Start 0, dispatcher 84 and halt 254 remain fixed; working labels number 219 and total rows 438.

Zero-terminal changes nine rows of the normalized accepted 219 table:38/1,53/0,53/1,88/1,102/1,103/0,119/0,119/1,134/1. In particular 53/0 now enters shared 108 ; 119 becomes a pure binary decoder with 0R68/1R69. The accepted 219 increment engine, state 108's own rows and helper 302 (normalized 120) remain unchanged.

Standalone retagged changes 139/0 to 0R99, 139/1 to 1R160, 160/1 to 1L63. **Composition uses 139/0=0L139 instead.** Its 12-row table is zero-terminal plus that distinct three-row seed, not the literal union of the two standalone tables. Each final table therefore needs its own startup and runtime check.

This differs materially from our recorded `k219-engine-rebase` failures. Those altered the 220 increment engine and tried new right-CI5/CI6 entries. The first full runs failed CD6-zero at 4568; a careful shared 108 repair passed 255 focused guards but then failed the unsupported right-CI entry at 4570. This packet retains the accepted 219 engine and puts CD6 rather than a new CI at the changed terminal. Its source reasoning makes the extra positive cases unreachable, **but its generic physical proof still checks them**: zero-terminal/composed 6175 cases versus retagged 6167. It does not inherit success from the old failed experiments.

## Fresh results and limits

The first nine jobs passed: exact reconstruction, independent complete source/table transport, three source checks, three canonical/whole-startup checks, and the independent small source/startup audit. Exact startups are 313845, 312707, 314043 steps for zero-terminal, retagged, composed. All reach dispatcher 84/head −5 with the same complete 277-one-cell tape, logical `[3,0,0,0,3,0,0,0,0]`, 130 one-valued spares, header 139 and extra gap 80.

All 14 direct jobs finished successfully with no stderr, timeout or failed attempt. All 18,517 generic cases passed, followed by the independent runtime/block audit and all 10 malformed-input rejection controls. The three full-runtime process times were 145.730, 147.102 and 143.787 seconds. Their symbolic-step totals were 1,518,671, 1,514,311, 1,518,914 respectively. Every variant covered all 438 literal rows. Fresh source, startup, complete case arrays and canonical tables are byte-identical to delivered evidence; runtime records agree after removing only measured elapsed seconds. The terminal status is `FRESH_DIRECT_LEAVES_PASS`, not the skipped wrapper’s status. Fresh full runs use independent arbitrary natural primary values, gap and first spare plus arbitrary finite remaining spare tail. Four literal-table block lemmas support finite-list traversal. The 4000-rule limit bounds construction of each symbolic proof, not represented values or actual machine time. The independent result audit checks full ordered domains, positive affine durations, all 438 row coverage and independently rederives the four block identities; it does not itself regenerate every symbolic derivation.

This is ordinary executable mathematical certification, not a new Lean/Rocq exact-table theorem. Logical calibration is inherited through the exact accepted K219 source and these source equivalences; it is not freshly replayed here. No result below 219, unconditional nonhalting, proof of Con(ZFC), or minimality follows.

## Composable idea

The useful change is replacing a control return by a register test under a mechanically established zero-entry invariant, then separately certifying the new physical branch for arbitrary inputs. This supplies a different correct decoder realization without the unsupported right-CI entry introduced in our previous equality hit 2. Source reassociation with continuation retagging composes exactly with it, but physical composition requires the changed 139/0 seed. Drop owns further state-fold stacking and reports that the old delete-302/cooperative-27 failures survive these new layouts; this review does not reclassify those failed reductions as successes.
