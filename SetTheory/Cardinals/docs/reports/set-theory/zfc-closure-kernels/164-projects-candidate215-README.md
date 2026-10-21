# K215: composition of partial-selector and permuted-command constructions

The primary machine is `k215.native.tm`, with **215 working states**, 430 transitions, native start 0 and external halt 254. Its dense canonical renaming is `k215.tm`, with working states 0–214 and halt 215. `sites215.json` is the exact source. The full source-to-binary primitive proof and blank initialization were freshly replayed for this table; their receipts are supplied by the enclosing packet.

This is a new composition of two credited public 216-state constructions, not a claim to have invented their individual reductions. The partial-selector construction supplies the extra 164/183 marker fold and its context-correct source layout. The permuted-command construction supplies the MP-only input schedule, the useful read/load reassociation, the210 command order, and the local81/0 helper replacement. A constrained decoder assignment makes these changes coexist and removes one additional physical state from the partial-selector 216 parent.

## Exact identity

| Artifact | SHA-256 |
|---|---|
| Native table | `04b4dbb537306f40f8965ad6a0ee6034e9953f079c233153e9696acdf06c2712` |
| Canonical table | `6c0fff966c4409eb726e634d6d5753552e198da0f8c7bfe7fc39ec0151f1de7a` |
| Source | `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba` |

The source has 202 distinct subtrees, 4751 primitive occurrences, maximum depth 47 and maximum zero run 6. The literal table deletes native 185 from the partial-selector 216 parent, changes 36 retained rows, and adds no state. The earlier partial-selector fold has already deleted native 183 from K217. The complete row diff, including both rows deleted at 185 and the81/0 repair, is `recipes/table210.json`.

## Deterministic reproduction

From any current directory:

```sh
python /path/to/candidate215/build.py --output /path/to/output
```

This uses Python's standard library only. It authenticates both original predecessor archives, reads only the required members in memory, rebuilds the source, applies the explicit finite row recipe, and checks the exact fixed decoder assignment. No optimizer, solver, network, or external repository is needed. `--partial-archive` and `--permuted-archive` can override the archive locations while retaining their required hashes.

The unchanged partial-selector archive is under `parents/`. The unchanged permuted-command archive is shared with the enclosing packet at `../upstream216/K216_Permuted_Commands_2026-10-21.zip`. Their original mathematical reports, code, source inputs, full tables, nested parent packets, licenses and attribution are preserved inside those exact archive bytes. Extracted construction inputs are additionally retained under `inputs/` and authenticated against those archives.

The output contains rebuilt native/canonical tables, source, canonicalization map and `construction.json`. The construction check is independent of the discovery solver. It verifies both guarded successors at every decrement through independent graph algorithms, equality with the calibrated public 210 source graph, selector wire fields and return routes, all internal prefix bindings, preservation of both marker-fold provider fragments, and literal output hashes. The separate quantified runtime and complete blank tape proofs discharge the machine-level obligations; the finite prefix check is not used as their substitute.

## Source transformation

Use the partial-selector 216 source as the starting tree. In its original leaf ordinals, remove intervals[23,37) and[187,201), and replace[228,254) and[4659,4685) by a local counter read followed by the existing 26-leaf counter load. The 14-leaf read is `(walk11,transfer3)`. Use the right-associated form `(walk11,(transfer3,load26))`; all three factors are closed and halt-free. This avoids the seven-zero source address in the earlier transplant.

Then permute the three closed command bodies at paths `111`, `110101`, `110100101` in order 210. The command tag meanings are NIP, DROP, MP for tags 0, 1, 2; selectors at least 3 continue to mean AX, with the same residual AX parameter. The final source has exactly the same complete guarded ordinal graph as the public calibrated 210 source, although its AX factorization retains the partial-selector layout. The public command-calibration proof therefore applies without a new logical axiom system or input-language assumption.

## Physical allocation

The composed source has 157 inherited internal subtree roles represented by 143 retained physical states, plus 22 new internal subtree nodes. There is a 23-state retired/root decoder pool. The fixed assignment uses 22 of these states and leaves 185 unused. Together with the 50 remaining engine states, this gives 215 physical states.

Some retired decoder states still serve the arithmetic engine, so they cannot be overwritten freely. The assignment preserves native rows 11/0,26/0, 26/1, 37/0, 92/0, 213/0 and 213/1. The public whole-tape local replacement 81/0=`0L111` frees 92/1 for decoding while retaining the original 69 marker fold. Both the 69 fold's provider rows and the 164 fold's 201/195/196 selector fragment remain literal. All changed assignments and protected rows are explicit in the recipe; the unbounded runtime replay checks their complete use, including contexts beyond these local constraints.

The initial discovery used a small binary assignment optimization. That search is unnecessary for reconstruction: each node's fixed source path and state assignment is listed in the recipe, and the standard-library builder checks the resulting table directly.

## Secondary variant

`secondary120/` is an exploratory alternative 215-state allocation using command order 120. Its exact source/table reconstruction and clean blank prefix were checked, but this packet does not assert a full primitive-runtime certificate for it. It is not the principal machine. Add `--secondary` to the construction command to reproduce its source and table as well. Its blank prefix reaches a clean frame after 96308 transitions, with registers(4,0,0,0,0,0,0,0,0), head −8 and extra gap 1.

## Attribution and proof scope

The new contribution is the composition, constrained fixed decoder allocation, exact 215-state tables, source correspondence and fresh verification. The individual partial-selector fold, command permutation, MP-only schedule, local81 repair, numerical-calculus consistency calibration, proof compiler, unary runtime, and earlier machine ancestry belong to their upstream authors. See `inputs/PARTIAL_SELECTOR_ATTRIBUTION.md`, `inputs/PERMUTED_COMMANDS_ATTRIBUTION.md`, and the unchanged predecessor archives for exact attribution and inherited terms. No replacement license is asserted over inherited work.

The proof is ordinary mathematics with executable finite certificates and symbolic unary-loop induction, formalizable in ZFC. No proof-assistant kernel endpoint, absolute consistency proof, minimality claim or priority claim beyond this exact composition is asserted.
