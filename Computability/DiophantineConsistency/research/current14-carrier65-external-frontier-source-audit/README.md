# Carrier65 recorded external frontier: bounded source-header expansion

This read-only inspection expands the **recorded** Carrier65 retry05 and linked-base external frontier by one generation of currently available source headers. It does not run Lean, change retained evidence, establish which providers Lean would load, or authenticate compiled objects as products of the observed source files. The accompanying `observation.json` is a non-atomic snapshot of source bytes, recorded object hashes and selected companion paths.

An [independent review](../../reviews/current14-carrier65-external-frontier-source-independent/README.md)
reconstructs the bounded header and artifact observations without establishing
compiled-import or runtime closure.

## Seeds and the recorded boundary

The 239 completed retry05 stages directly name 55 distinct external modules. Their recorded base dependencies reach 172 of the 1,000 linked base producers via recorded project edges, with 23 distinct external names at that reachable-base boundary. For a deliberately broader survey, the seed set is the union of **all 99** external names declared by the 529-stage plan and the **106** distinct external names recorded by **all 1,000** linked base producers. Their union has 138 names: 99 Mathlib, 37 Foundation, `Init`, and `Lean.Elab.Tactic.Omega`. This broad set includes modules outside the completed prefix and is not asserted to be the exact dependency closure of its next stage.

For each seed the inspector compares the current selected package `.olean` bytes with the hashes recorded by the plan and/or base state; it also records each observed package/toolchain candidate path, realpath and hash. For all 37 Foundation seeds, the `.olean` hash matches the existing pinned `build-all-receipt.json` object entry, and 11 observed artifact suffixes per seed match that receipt's recorded hashes. That receipt describes a Foundation build on **inherited external package and dynamic ancestry**; its file and recorded hashes are observations, not independent authentication of its producer, complete runtime closure, or proof that the current source bytes produced the objects. The inspector records 138 seed `.olean.private`, 138 `.olean.server`, and 138 `.ir` files as present, among other suffix observations. Presence and matching hashes do not by themselves establish which companions a future Lean process needs or loads.

## Source headers and `import all`

All 138 seed source paths are currently available under the selected Mathlib, Foundation and toolchain source roots. Their explicitly named imports add 639 new source modules; the inspector reads those headers too, giving 777 observed source headers and 3,157 explicit header edges. It intentionally stops there: 764 distinct names appearing at the next boundary are **unexpanded**, not necessarily missing. No first-generation source path was missing among the observed modules.

The bounded header parser handles initial `module`, `prelude`, and single-name `import`, `public import`, `meta import`, `public meta import`, and `import all` commands, including nested block and line comments. It rejects an unrecognized import-shaped header rather than guessing. It stops at the first other command, is not a Lean parser, and does not infer implicit/prelude or runtime imports. The paths and SHA-256 values are recorded to make this particular observation reproducible; they do not associate source content with the seed `.olean` producers.

The observed headers contain **13 `import all` edges to 12 distinct targets**, including these three in seed sources:

* `Mathlib.Data.Nat.Bitwise` imports all of `Init.Data.Nat.Bitwise.Basic`.
* `Mathlib.Data.Nat.Digits.Defs` imports all of `Init.Data.Repr`.
* `Mathlib.Tactic.ReduceModChar` imports all of `Mathlib.Tactic.NormNum.DivMod`.

The first two are also external names on the recorded reachable-base frontier; the third is in the broader seed set but not that reachable subset. All 12 observed `import all` targets have a `.olean.private` candidate in at least one inspected package/toolchain root. Such companion candidates matter to investigate, but the source text and present files do not prove the actual compiled imports, their versions, or Lean's companion selection. The remaining ten `import all` edges are in first-generation source headers and are listed individually in the receipt. The 464 `meta import` edges are likewise source-header observations; tactic/plugin, shared-library, executable and other runtime inputs remain unclosed.

## What this does not establish

The recorded project edges, Lake/Foundation receipts, `.trace` and `.hash` files do not by themselves prove that these currently observed sources produced the selected objects, or that all transitive and implicit imports, private/server/IR companions and dynamically loaded code are compatible. The source roots for first-generation package modules are selected by namespace and may not be the actual source used to build an object. Search precedence, unobserved alternatives, filesystem mutations between checks and additional output/companion names remain unresolved. Cached hashes and non-atomic reads cannot detect intervening mutations. A future continuation must authenticate and isolate its exact providers and runtime inputs, rerun actual guarded dependency resolution, and independently check the completed proof chain; this packet is not a launch plan or authorization.

Run from the repository root, while the recorded paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-carrier65-external-frontier-source-audit/inspect.py | cmp - Computability/DiophantineConsistency/research/current14-carrier65-external-frontier-source-audit/observation.json
```
