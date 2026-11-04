# The 94-, 92-, 91-, 90- and 89-operation 12-variable endpoints: source promotion

3 November 2026. Author-side build by the Claude session; not a paired replay.
This record extends the [compact44 calibration promotion](../compact44-source-promotion/README.md).

## What was promoted

The 95-operation free-J literal has five smaller successors in this lane. All
five keep the 12 positive coordinates and the fixed compact44 port tuple
`CompactSymbolicModelIff.p = ![β, K, L, β+H]`, with `β = 2^590069 − 1`:

| Ops | Lean expression | Exact degree | Lean source / JSON graph (SHA-256 prefix) | Research home |
| --- | --- | --- | --- | --- |
| 94 | `FreeJSumSquares.squareLiteral p` (three residual squares) | 84 | `77f22764` / `candidate.json` `dc13e87a` | `ordinary12-sum-of-squares-candidate` |
| 92 | `(FreeJQCube92.graph p).output` (`Y = q³s`) | 164 | `d79c…` / `candidate.json` `3a21d323` | `ordinary12-qcube92-candidate` |
| 91 | `(FreeJXQ91.graph p).output` | 172 | `6160…` / `candidate.json` `fde7510b` | `ordinary12-xq91-candidate` |
| 90 | `(FreeJDirectMainGraph.graph p).output` | 172 | `6e465bd6` / `graph-dag.json` `82dd1f55` | `ordinary12-direct-main-probe` |
| 89 | `(FreeJAbsorb89.graph p).output` (first-root absorption) | 172 | `c74d9a67` / `graph-dag.json` `280b23e5` | `ordinary12-absorb89-probe` |

**Where the numbers come from:**

- The degrees come from the lanes' external degree checkers.
- The Lean-source hashes are those the lane checkers pin. The 94-, 92- and
  91-operation lanes use `check_lean_graph.py`; the 90 and 89 lanes use
  `check-dag.py`.
- The promoted copies differ from those sources only in import lines (see the
  manifest).
- The 92 and 91 checkers were rerun with `py -I -X utf8` and pass. Their
  default cp1252 decoding breaks the `→`/`ℤ` matching.

For 94, `FreeJSumSquares.zero_iff_literal` proves that, at every valuation,
the expression has the same zeros as the 95-operation literal. For 92, 91, 90
and 89, `FreeJQCube92Halt`, `FreeJXQ91Halt`, `DirectMainHalt` and
`Absorb89Halt` each prove `positive_model_iff`: in every model of `𝗜𝚺₁`, the
graph has a positive zero iff machine 215 halts. Each proof chains
positive-zero equivalences down to `CompactSymbolicModelUnconditionalIff.model_iff`.

**The copies.** The research import closure of those halt modules has 87
modules not yet in the tree. They were copied into
`Lean/DiophantineConsistency/Compact44/` as `DiophantineConsistency.Compact44.<X>`,
by the same rule as before: namespaces are unchanged, and only import lines are
rewritten. [`manifest.tsv`](manifest.tsv) records each module's source and
SHA-256s:

- 5 copies are byte-identical;
- in the other 82, removing the import lines makes the two files equal;
- there are no other differences.

**The source of each module.** The resolver took the module's lane home
directory first, then a unique byte content among same-named research files.
Four explicit overrides apply:

- `Absorb89ModelReflection` and `Absorb89FullReflection` come from the
  independently reviewed
  [`reviews/ordinary12-absorb89-reflection-independent/`](../ordinary12-absorb89-reflection-independent/);
- `CompactLowByteBoundary01` is the corrected, warning-free window in
  `compact44-low-byte-boundary01-fix`;
- `CompactLowByteAssembly` is the guarded assembly in
  `compact44-low-byte-assembly-attempt2`.

Every import resolved, and no copied name clashes with the tree.

**The new endpoint.** The only authored module is
`Compact44/IPRAOrdinary12Chain.lean`.

- Three generic helpers (`native_of_positive`, `standard_of_positive` and
  `reference_of_positive`) take any `PositiveModelBridge` through
  `IPRAOrdinary12.bridge_of_positive` and the existing iPRA pipeline.
- For each N ∈ {94, 92, 91, 90, 89} the module defines `expressionN`,
  `positiveBridgeN`, and the native, standard and equality-only equivalences
  `native_equivalenceN`, `standard_equivalenceN` and `reference_equivalenceN`.

## Build

- **Tree:** the root workspace at `159f84a7ba`. The 31 upstream commits through
  `origin/main` at commit time touch nothing under
  `Computability/DiophantineConsistency/Lean`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` or `ProveIt.lean`.
- **Build discipline:** 88 targets, one
  `lake build +DiophantineConsistency.Compact44.<M>` per invocation, in
  dependency order, with `LAKE_JOBS=1` and `LEAN_NUM_THREADS=0`.
- **Outcome:** every target exited 0, with no errors and no warnings. The peak
  resident memory per target was at most 4.4 GB, for the endpoint itself
  (186 s).

## Axiom reports (Lean metatheory)

- **Endpoints:** each of the 15 `IPRAOrdinary12Chain.{native,standard,reference}_equivalence{94,92,91,90,89}`
  reports exactly `[propext, Classical.choice, Quot.sound]`.
- **The whole closure:** the 88 build logs contain 13,173 reports. Each is
  within that same set, and 277 report no axioms.
- **Source scan:** across all 560 files of `Compact44/`:
  - no `sorry`, `native_decide`, `axiom`, `unsafe` or `implemented_by`;
  - the only `admit` match is English prose in a doc comment.

## Scope

- **What this shows:** for each of the five expressions, native, standard and
  equality-only iPRA each prove

  > *no natural zero of `positiveShift expressionN`* ↔ *Con(ZFC)*,

  for the selected Foundation ZFC consistency predicate.
- **Relation to the research endpoints:** Codex's
  [`ordinary12-direct90-ipra-endpoint-draft`](../../research/ordinary12-direct90-ipra-endpoint-draft/README.md)
  is a separate route to the 90-operation statement. It works over the byte-port
  recipes, in a guarded historical provider, and has an independent receipt
  audit. The present endpoint states the symbolic-port form in the current
  root workspace. The research
  [`ordinary12-xq91-ipra-endpoint-draft`](../../research/ordinary12-xq91-ipra-endpoint-draft/README.md)
  remains uncompiled; the 91-operation statement here supersedes its purpose.
- **What it does not show:**
  - It is not an independent paired replay.
  - As with the 95-operation endpoint, it does not bind the Lean expressions
    to the JSON graphs, payload bytes or PDF displays by a Lean theorem. That
    correspondence rests on the external graph checkers named above.
  - The speculative 88- and 86-operation graphs are outside this record.
