# Direct-BFS943 trace75 closure: source promotion

7 November 2026. Author-side promotion by the Claude session; not a paired
replay. Template: [`compact44-source-promotion`](../compact44-source-promotion/README.md).

## What is promoted

The research final assembly of 3 November
([`trace75-bfs-ipra-final-assembly-plan`](../../research/trace75-bfs-ipra-final-assembly-plan/README.md),
`observations/attempt01/result.json`, status `PASS`) compiled the fixed-port
trace75 client `Trace75BFSFixedIPRA` in a temporary union of 2,016 modules. Its
import closure has 1,868 project modules. Each was resolved to one source:

| Class | Modules | Treatment |
|---|---:|---|
| tree module (identical, one-of-several, no producer record, or changed since) | 978 | used as it is (tree-first rule) |
| source equal to the Compact44 manifest source | 445 | the existing `DiophantineConsistency.Compact44.<X>` |
| research source, promoted here | 341 | copied to `BFS943/<X>.lean` |
| source never committed | 4 | reconstructed here (below) |
| `ArithmeticWangTableChunk*` | 95 | dropped: only the closure's variant of the tree `ArithmeticWangTable` imports them |
| research IPRA stages | 5 | replaced by the authored endpoint |

Resolution order (as for Compact44): the tree name; the explicit overrides
(`CompactRankVariationRetry` ← `CompactRankVariation.lean`,
`OldWordIdentification` ← `-DRAFT.lean`, `DirectBFSOriginBlockResidue` ← the
tracked stage-044 snapshot of `direct-bfs-80-coherent-rebuild`,
`DirectBFSCoverageAggregate` ← the aggregate retry); the recorded producer
`.olean` → source hash; the Compact44 manifest; a unique content. Every chosen
research source's `import` lines equal the serialized header captured by the
assembly (modulo the `DiophantineConsistency.` prefix and `Init`).

## The copies

- Module names `DiophantineConsistency.BFS943.<X>`; **Lean namespaces
  unchanged**. Before promotion no copied module's namespace was opened by any
  tree file.
- Only import names were rewritten: a tree import stays; a Compact44-reused
  import becomes `DiophantineConsistency.Compact44.<X>`; a promoted or
  reconstructed import becomes `DiophantineConsistency.BFS943.<X>`.
- The copier parsed each header with comments (`--`, nested `/- -/`) skipped,
  and checked for every copy that the number of `import` lines in the whole
  file equals the number of parsed names, that the bytes after the header are
  unchanged, and that the rewritten import set equals the import set recorded
  in the assembly, mapped through the module map. All 341 passed.
- [`manifest.tsv`](manifest.tsv) records source path, source SHA-256,
  promoted SHA-256 and relation: 19 `identical`, 322 `imports-only`, 4
  `reconstructed`, 1 `authored`.
  [`tools/check_manifest.py`](tools/check_manifest.py) re-checks every row
  (hashes, relation, every import resolving to a tree source file, folder
  contents).
- Trust scan of all 346 files: no `sorry`, `admit`, `native_decide`, `axiom`,
  `unsafe`, `implemented_by` or `maxHeartbeats 0`.

## The four reconstructions

The sources of `DirectBFSCarryRoom`, `DirectBFSFieldParity`,
`DirectBFSForeignBands` and `DirectBFSUniformForeign` existed only in another
agent's worktree and were never committed; 82 closure modules depend on them.
Each statement was fixed from its call sites (every use was found by name; no
copy opens these namespaces) and each proof is a port of the Compact44 lemma at
the BFS943 layout. Each keeps the import set recorded for the lost module.

| Module | Statement | Call sites | Port of |
|---|---|---|---|
| `DirectBFSCarryRoom` | `aligned_room : (∑ j, (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j)*3)+1 < 2^66` | `Trace75BFS`/`DirectBFS80` `AlignedShift`, `CellShift`, `UniformReset`; `DirectBFSMarkerParity`, `DirectBFSUniformDecoder` (as `hroom` of `FractionalAnchorConflict.conflict`, `TemporalCarryExact.clean_exact`, …) | `ConcreteCarryRoom.aligned_room`, via `DirectBFSModelMass.natural_mass` and `stencil_below_half` |
| `DirectBFSFieldParity` | `vertical`, `horizontal`: `FieldWindowParity`'s statements with the coefficient `alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies` | `Trace75BFSFieldMarkers`, `DirectBFS80FieldMarkers` | `FieldWindowParity`, with `DirectBFSRawParity.expand` and `DirectBFSCarryRoom.aligned_room`, exactly as the promoted `DirectBFSMarkerParity` ports `FieldMarkerParity` |
| `DirectBFSForeignBands` | `foreign_and_bare`: `ForeignBandsZero`'s statement with `DirectBFSRawColumn.columnBand` | `Trace75BFSOccupied`, `DirectBFS80Occupied` | `ForeignBandsZero.foreign_and_bare` (reusing its `source_zero`) |
| `DirectBFSUniformForeign` | `at4393`, `at5495`: `UniformForeignZero`'s statements with `DirectBFSRawColumn.columnBand` | `DirectBFSUniformDecoder`, `DirectBFSMarkedTarget` | `UniformForeignZero` |

No call site was ambiguous. The callers rewrite with these lemmas at a
`let n := 8807*N`; the statements use the literal `8807*N`, as the Compact44
lemmas do at the same Compact44 call sites.

## The endpoint

[`BFS943/IPRATrace75.lean`](../../Lean/DiophantineConsistency/BFS943/IPRATrace75.lean),
namespace `DiophantineConsistency.IPRATrace75`:

- `fixedPorts := CompactSymbolicPorts.ports betaNat (DirectBFSSymbolicKernel.paramKernel rho) lowNat highNat`
  (`![β, K0, MC, β + MF_native]`);
- `expression := Trace75BFSSyntax.literal fixedPorts`, which is
  `TenPositiveTrace75.expression (fun j => (fixedPorts j : ℤ))` (`expression_def`, `rfl`);
- `positiveBridge : IPRAOrdinary12.PositiveModelBridge expression`, from
  `Trace75BFSModelIff.positive_model_iff` and `Trace75BFSSyntax.literal_zero_iff`.
  The four port hypotheses are the generic lemmas `ports_zero … ports_three`,
  proved by `rfl` over arbitrary `β K L H` and only then instantiated, as in the
  research fixed client;
- `native_equivalence`, `standard_equivalence`, `reference_equivalence` via the
  `IPRAOrdinary12Chain` helpers, and `standard_translated_equivalence`,
  `reference_translated_equivalence` with the negative translation of the
  source ZFC sentence (`IPRABoundedRhoZFC.zfcEquiv`), the research stage-4
  variants.

The research adapters `PositiveModelIPRA*` are not promoted: their
`PositiveModelBridge` is the tree's `IPRAOrdinary12.PositiveModelBridge`
verbatim.

## Binding to package 163

Finite external checks, not Lean theorems about files:

| Check | What | Result |
|---|---|---|
| [`tools/check_ports.py`](tools/check_ports.py) | transcribes the pinned Lean definitions of `fixedPorts` (BFS rows, slots, selector, mask support and digits, high digits, β) and compares the four integers with the `raw_sha256`/bit lengths of `163-trace-radical/compact/equations/trace75_degree402.json` and with the retained payloads | PASS: K0 `0a86821a…` (592,884 bits), MC `6007cabd…` (590,069), MF `48333b0d…` (590,070), β `0664a868…` (590,069) |
| [`tools/check_bytes.py`](tools/check_bytes.py) | `research/direct-bfs-lean-kernel-prototype/check-bytes.py` re-pinned to the promoted `BFS943/DirectBFSSymbolicKernel.lean` and `Compact44/CompactSymbolicKernel.lean`, each also required to equal its research source outside the import lines | PASS_EXTERNAL_RECIPE_BYTES, raw `0a86821a…`, 74,111 bytes |
| `research/trace75-bfs-decimal-display/check_lean_graph.py` | the JSON circuit vs the tree `TenPositiveTrace75.lean` (unchanged) | PASS |

## Build

- **Tree:** the root workspace at `e679320a0a`. Since `df8beb801d`, where the
  build started, the only Lean changes are new Compact44 P66 modules, which
  this closure does not import. No tracked file was changed by this promotion.
- **Discipline:** 346 targets, one `lake build +DiophantineConsistency.BFS943.<M>`
  per invocation, strictly serially, in dependency order, with `LAKE_JOBS=1`
  and `LEAN_NUM_THREADS=0`.
- **Outcome:** every target exited 0 at the first attempt. No source needed a
  fix, so every promoted file is still exactly as recorded in
  [`manifest.tsv`](manifest.tsv) (`check_manifest.py`: ok).
- **Time:** 8,560 s of wall time over the 346 invocations, most of it Lake's
  replay of already-built dependencies. The longest invocations were
  `DirectBFSSymbolicKernel` (177 s; the module itself 38 s) and the endpoint
  `IPRATrace75` (114 s; the module itself 33 s). Peak memory was not measured.

## Axiom reports (Lean metatheory)

- **Endpoints:** each of the following reports exactly
  `[propext, Classical.choice, Quot.sound]`:
  - `DiophantineConsistency.IPRATrace75.positiveBridge`
  - `DiophantineConsistency.IPRATrace75.native_equivalence`
  - `DiophantineConsistency.IPRATrace75.standard_equivalence`
  - `DiophantineConsistency.IPRATrace75.reference_equivalence`
  - `DiophantineConsistency.IPRATrace75.standard_translated_equivalence`
  - `DiophantineConsistency.IPRATrace75.reference_translated_equivalence`
- **The whole closure:** all 80,980 `#print axioms` reports in the 346 build
  logs (own and replayed) name only axioms from that set; no log contains an
  error or `sorry`. The only warnings are replayed Foundation library warnings.

## Scope

- **What this shows:** in native, standard and equality-only iPRA,
  *no natural zero of `positiveShift IPRATrace75.expression`* ↔ *Con(ZFC)* for
  the selected Foundation ZFC consistency predicate, where `expression` is
  package 163's 75-operation circuit `TenPositiveTrace75.expression` at the
  direct-BFS943 ports.
- **What it does not show:** it is not an independent paired replay, and the
  correspondence of the Lean literal and ports with the JSON circuit and the
  payload bytes is the finite external checks above, not a Lean theorem. The
  four reconstructed modules are new proofs of the lost modules' call-site
  statements, not recoveries of their bytes.
