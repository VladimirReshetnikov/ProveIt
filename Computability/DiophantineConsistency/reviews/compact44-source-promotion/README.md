# Compact44 calibration and the 12-variable free-J endpoint: source promotion

3 November 2026. Author-side build by the Claude session; not a paired replay.

## What was promoted

The all-model calibration of the compact44 tuple,
`CompactSymbolicModelUnconditionalIff.model_iff`, had been proved only in
research prototypes under
[`research/ordinary12-ipra-bridge`](../../research/ordinary12-ipra-bridge/PLAN.md).
Its import closure there had 472 modules spread over many prototype, retry and
exploration directories, and it compiled only in historical hybrid providers.

**The theorem.** In every model `V` of `𝗜𝚺₁`, the literal 12-variable free-J
graph `Ordinary12FreeJ.literal CompactSymbolicModelIff.p` has a zero with all
coordinates positive iff machine 215 halts. The free-J graph has 12 positive
coordinates, 95 operations and exact degree 70.

**The ports.** `CompactSymbolicModelIff.p` is the concrete port tuple
`![β, K, L, β+H]`:

- `β = 2^(67·8807) − 1 = 2^590069 − 1`;
- `K` is `paramKernel (2^67)` over the 943 rows of `Compact943Data`;
- `L` and `H` are the low and high mask values of `CompactSymbolicPorts`.

**The copies.** All 472 closure modules were copied into
`Lean/DiophantineConsistency/Compact44/` under the module names
`DiophantineConsistency.Compact44.<X>`.

- Their Lean namespaces are unchanged.
- The copier rewrote **only import lines**: closure imports became
  `DiophantineConsistency.Compact44.<X>`, and bare tree imports became
  `DiophantineConsistency.<X>`.
- [`manifest.tsv`](manifest.tsv) records, for every module:
  - the research source path,
  - the SHA-256 of the source and of the promoted copy, and
  - the relation between the two.
- **The relation checks out:**
  - 31 copies are byte-identical;
  - in the other 441, removing the import lines makes the two files equal;
  - there are no other differences.

**The source of each module** was chosen in this order:

1. the module exists in the tree, so no copy is needed;
2. one of four explicit overrides, for names whose accepted source lives in a
   differently named file or prototype:
   - `FixedGraphMarkedHalt`
   - `TwoBand`
   - `FreeJGraphCongruenceExplore`
   - `CompactRankVariationRetry`, which comes from `CompactRankVariation.lean`;
3. sources pinned by hash in a recorded `source-scan.json`;
4. hashes recorded in the lane's `providers.json` files;
5. a unique byte content;
6. the unique top-level, non-exploration copy.

The resolver reported no conflict, and every import resolved.

**The new endpoint.** The only authored module is
`Compact44/IPRAOrdinary12.lean`. It adds:

- `PositiveModelBridge`, the statement shape of `model_iff`;
- `bridge_of_positive`, which turns a positive-model bridge into the
  `PolynomialBridge` of the once-shifted expression (`positiveShift`);
- the native, standard and equality-only iPRA equivalences, through the
  existing `IPRAExpressionNative`, `IPRAStandardTheory` and
  `IPRAReferenceInductionConversion` pipeline.

## Build

- **Tree:** the root workspace at `5753b3f955`. No file under
  `Computability/DiophantineConsistency/Lean`, `lakefile.toml`,
  `lake-manifest.json` or `lean-toolchain` changed between that commit and
  `3c85f4fc1c`.
- **Build discipline:** 473 targets, one
  `lake build +DiophantineConsistency.Compact44.<M>` per invocation, in
  dependency order, with `LAKE_JOBS=1` and `LEAN_NUM_THREADS=0`.
- **Outcome:** every target exited 0. The peak resident memory per target was
  at most 4.4 GB, for the endpoint itself (155 s).

## Axiom reports (Lean metatheory)

- **Endpoints:** each of the following reports exactly
  `[propext, Classical.choice, Quot.sound]`:
  - `DiophantineConsistency.IPRAOrdinary12.native_equivalence`
  - `DiophantineConsistency.IPRAOrdinary12.standard_equivalence`
  - `DiophantineConsistency.IPRAOrdinary12.reference_equivalence`
- **The whole closure:** every `#print axioms` report printed during the
  closure's build names only axioms from that same set.
- **Source scan:**
  - no `sorry` and no `native_decide`, so `Lean.ofReduceBool` cannot appear;
  - no `axiom` declarations;
  - no `unsafe` and no `implemented_by`.

## Scope

- **What this shows:** in each of native, standard and equality-only iPRA, the
  following is provable:

  > *no natural zero of `positiveShift IPRAOrdinary12.expression`* ↔
  > *Con(ZFC)*, for the selected Foundation ZFC consistency predicate.

  The underlying `model_iff` is now a current-source Lean result of the root
  workspace.
- **What it does not show:**
  - It is not an independent paired replay.
  - It does not bind the Lean literal at the concrete tuple to the retained
    payload bytes or to a PDF display. That binding remains the finite
    hash/substitution checks of the free-J prototype and its
    [independent audit](../ordinary12-freej-prototype-independent-audit/README.md).
  - The other frontier packages that share the compact44 tuple still need
    their own reductions to this outer data. Examples are the ten-positive
    75-op/degree-402 equation and packages 72, 101, 113, 115, 170, 184 and 193.
