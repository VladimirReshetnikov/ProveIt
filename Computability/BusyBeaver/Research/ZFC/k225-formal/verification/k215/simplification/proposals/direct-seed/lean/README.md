# Direct seed semantics, with joint Lean validation

Baseline: `VladimirReshetnikov/ProveIt` commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## Result

The new checked theorem `KSeed222.seed_direct` constructs the seed property for
every named formula, including formulas with literal equality, on the original
model domain. `fullSeed_direct_of_derivable` therefore returns `FullSeed mem`,
where the earlier constructor returned `FullSeed (KIndisc222.qmem mem)`.

The generic `KEndpoint.c222_of_zf_refutation` now applies the semantic lower
construction to that original domain and uses the original valuation witness
`e 0`. Its public type is unchanged. The later tagged-domain construction,
bisimulation quotient, well-founded part, and model of ZF remain unchanged.

This implements and validates the already documented proposal at
`k225-formal/verification/k215/simplification/proposals/sharing-interfaces/calculus/DIRECT_FULL_SEED.md`.
That proposal credits the existing Rocq `rocq224/src/Complete222.v` fresh-label
construction. The new contribution here is the compiled Lean implementation,
compatibility split, typed endpoint clients, and exact current-source validation;
the underlying strategy is credited prior work.

## Mathematical argument

Write `th` for `KEind222.th`. The completeness interface has two different
premises: the syntactic premise requires derivability of `enc (th f)`, while its
model premise supplies satisfaction of the original named formula `f`, with
literal equality. The direct construction uses that distinction.

For any named formula `psi`, put `m = not (not psi)`, `k = enc (th m)`, and
`B = bundleNF 0 1 k m`. Free names of a formula remain free after `th`.
Every occurring name of an encoded formula is smaller than its code. Therefore
`k` is not free in `m`. The outer double negation ensures `k > 1`, so the private
container name differs from the input and output names.

The named bundle constructors introduce only membership atoms, so `th` commutes
with those constructors. Consequently `enc (th B)` is precisely the enabled
numerical bundle instance `bundle222 0 1 k`. It follows that `B` belongs to the
existing theory `DerivableNF`.

The new `NamedBundleSemantics.bundle_iff_seed` proves the named bundle semantics
directly. It uses freshness to remove the private container assignment from the
matrix valuation. Named falsity is genuine falsity, so this lemma does not require
irreflexivity. Applying the model premise to `B` gives seeds for `m`; classical
double-negation elimination and `seedProp_congr` give seeds for `psi`.

There is no assertion that satisfaction of `th psi` reflects satisfaction of
`psi` on an arbitrary original domain. The semantics is evaluated on the original
bundle throughout. There is also no numerical encode/decode round trip in this
lower proof. The numerical upper proof, including irreflexivity and coincident
input/output cases, is retained unchanged.

## Files and compatibility

`direct_seed.patch` applies cleanly to the pinned baseline. It adds the two
production modules `KSeedInterface222` and `KSeedDirect222`, edits four existing
modules, and adds the typed audit `KSeedDirectAudit`.

`KSeedInterface222` contains the existing named bundle definitions, `DerivableNF`,
and `KIndisc222.FullSeed`, preserving their namespaces, types, and bodies.
`KSeedModel222` and `KIndisc222` retain the legacy construction through imports.
`KLowerSeed` imports the shared interface; `KEndpoint` imports the direct proof.
The machine table, source program, and machine-specific endpoint file are not
modified.

The joint source snapshot additionally contains the independently supplied shared
implication basis (`DominatedImplication` and `Lukasiewicz`) and `SharedBasisAPI`.
Those two production replacements belong to the separate shared-basis patch;
they are not duplicated in `direct_seed.patch`.

## Measured scope

The independent source-graph audit reports the following change for the direct
seed refactor alone, excluding the separate shared-basis replacement:

| Metric | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| KEndpoint215 project import closure | 179 modules | 178 modules | 1 module |
| Selected source bytes in that closure | 2,129,439 | 2,121,905 | 7,534 |
| Physical source lines in the selected closure | 41,170 | 41,020 | 150 |

`KSeedModel222`, `KIndisc222`, and `Code254Models` leave that import closure.
`KSeedInterface222` and `KSeedDirect222` enter it. `Code254Models` stays available
to older clients elsewhere in the repository.

Keeping the legacy APIs has a cost: the six production files directly involved
in this refactor total 25,899 bytes, compared with 19,104 bytes in the four
original files, an increase of 6,795 bytes. The demonstrated source reduction is
on the selected endpoint dependency boundary. It is not a repository-wide
deletion or a measured compile-time improvement.

## Validation

The final joint source snapshot contains 116 project modules. The delivered
`reproduce.py` was run from this packaged source directory and freshly compiled
all 116 modules serially with Lean 4.32.0. It verified all 26 exact selected axiom
reports. `verification/receipt.json` records that complete replay and binds its
source manifest, object hashes, and per-module logs. The source manifest records
every original repository path, baseline hash, import, and changed-source hash.

The audits cover the direct construction, the unchanged generic lower and
machine-to-ZFC endpoint types, the two legacy seed interfaces, and the old
generic, numeric, and unrestricted implication APIs. All selected reports use
only subsets of `propext`, `Classical.choice`, and `Quot.sound`; the pure shared
basis declarations use no axioms. The newly added proof and audit files have no
warnings. Eighteen linter warnings occur in unchanged upstream source files.

The literal machine-specific `KEndpoint215` closure is not rebuilt here.
`KEndpoint` is its generic endpoint provider, and the machine-specific file is
unchanged. A production acceptance run should rebuild that full endpoint under
the repository's maintained driver and compare its printed axiom reports.

## Reproduce

With Lean 4.32.0 installed, run from this directory:

```sh
python3 reproduce.py --lean /absolute/path/to/lean --out /absolute/new/output
```

The output path must not exist. The script checks the complete source inventory,
exact SHA256 values, import order, absence of proof holes or added assumption
declarations, and toolchain version. It creates every compiled object afresh,
fails on any compiler error, and requires exact selected axiom reports. It does
not reuse received object files, source modification times, or an external
repository. `--check-only` validates inputs without claiming a compilation.

`source_bindings.json` records every snapshot source and its baseline repository
path and hashes. `proposed/` and `direct_seed.patch` are the reviewable integration
artifacts. The legacy module statements are checked by explicit typed clients;
their continued existence is not inferred from a filename or a historical log.

## Next simplification

An additional possible contraction is to obtain `FormSeed` directly at named
roles 3 (input) and 1 (output), matching `Code254GIC.names`, instead of passing
through `FullSeed` and the input-name wrapper in `KLowerSeed`. That requires a
separate compatibility split and a measured net saving. It is not implemented
or claimed by this packet. Another worthwhile step is to share the named and
numerical bundle normalization through an explicit matrix/freshness interface,
while preserving the numerical theorem's degenerate-role behavior.
