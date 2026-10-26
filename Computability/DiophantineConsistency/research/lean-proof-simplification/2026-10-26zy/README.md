# Further Lean proof simplifications for DiophantineConsistency

This packet proposes **three concrete changes in two families**, after treating all mechanisms in the designated 41 research packets and `docs/incoming` as already applied.

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned revision: `3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114` (26 October 2026).

Toolchain: `leanprover/lean4:v4.32.0`.

Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.

## Read first

- `report.pdf` is the rendered review; `report.tex` is its complete editable source.
- S1 derives the computability endpoint from the project's existing concrete scalar realizer, after separating semantics to avoid an import cycle.
- B1 proves the factor-two Pell bound using only row 1. Its stronger isolated contract needs no beta-sign hypothesis. The smaller compatibility patch retains and uses the original beta hypothesis.
- B2 recovers beta positivity from a positive source zero and removes the external guard from the positive-zero equivalence. It is an application of B1's arithmetic family, not independent new mathematics.

The actual-pin measurements are **216 fewer lines** for S1's complete affected/new modules and **eight fewer lines** for B1's compatibility declaration. B2's additive compatibility integration **adds 90 lines**. None is a measured marginal saving in a hypothetical checkout containing every older alternative proposal. Do not add these figures to older reports' savings.

## What was checked

The four isolated Lean files passed Lean 4.32.0:

1. `RealizerPrimrecBridge.lean`: freshly compiled exact `ScalarPRCode` source plus natural/vector realizer bridges.
2. `GenericREAdapter.lean`: the proposed search-to-recursive-enumerability argument with function and semantic equivalence as explicit parameters.
3. `MinimalPellBootstrap.lean`: ten named bounds/sign results, including the actual compatibility candidate body bound to a byte-exact source table.
4. `GuardDischarge.lean`: both exact source tables, recovered beta guards, generic equivalence transport, and existence/emptiness adapters. The maintained guarded equivalence is an explicit parameter.

All reported axioms are among `propext`, `Classical.choice`, and `Quot.sound`. No admissions or new axioms were introduced. The original failed vector attempt (missing an import) and corrected successful run are both retained.

All three patches pass `git apply --check` against the pin. Independent static analysis follows 19 project modules in S1's import closure, finds no project cycles or unresolved project imports, and confirms that the direct enumerator differs by exactly one import. This is static evidence, not an elaboration check.

**The complete production import closures and downstream project were not rebuilt.** The patches are concrete, reviewable integration proposals. The extracted proofs and generic bridges do not justify reporting full integration success or performance improvements.

## Replay the focused Lean checks

The `lean/` directory is a small independent Lake project. In a network-enabled environment with Elan/Lake:

```sh
cd lean
lake update
lake exe cache get
python3 check.py
```

The manifest configuration pins the exact Mathlib revision. `check.py` builds the local copied scalar-code module and runs the four examples, saving fresh output under `.checks/`. It never applies the production patches. The recorded checks were executed through equivalent direct Lean invocations with the same compiler and Mathlib sources/caches; the Lake setup is supplied for portable replay, not represented as another completed clean dependency download/build.

The exact old source table is 1,774 UTF-8 bytes including its final LF; the gap table is 1,609. See `evidence/algebra/source_rows_binding.json` and `evidence/guard/table_binding.json` for hashes and extraction boundaries.

## Review the production patches

Use a clean checkout at the recorded pin. Each patch is independent of the others:

```sh
git apply --check /path/to/packet/patches/S1-realizer-dependency-inversion.patch
git apply --check /path/to/packet/patches/B1-source-Y-row-one.patch
git apply --check /path/to/packet/patches/B2-guard-free-equivalence.patch
```

Apply desired patches in a review branch, then build the affected modules:

```sh
lake build DiophantineConsistency.Computability DiophantineConsistency.Bridge
lake build DiophantineConsistency.NativePellBootstrap
lake build DiophantineConsistency.GapSource66
```

Replay the project's existing named-endpoint axiom checks as appropriate. `proposed/S1/` and `proposed/B2/` contain complete candidate files, so the integration choices can be read without applying diffs. Keep external beta guards for arbitrary tuples and retain independent bounds such as beta at least 15.

## Build the document and inspect integrity

```sh
python3 scripts/build_report.py
python3 scripts/verify_package.py
python3 scripts/verify_sources.py /path/to/ProveIt
```

The report uses XeLaTeX, standard TeX Live packages, Latin Modern Roman, and DejaVu Sans/Mono. Building the report changes its PDF and auxiliary files, so the original `SHA256SUMS` verifies the delivered files before rebuilding. `verify_sources.py` is read-only: it verifies the pin, recorded source hashes, and patch applicability; it does not compile or mutate the repository.

## Directory map

| Directory | Contents |
| --- | --- |
| `lean/` | Checked source files, exact scalar-code copy, pinned Lake setup, replay helper |
| `patches/` | Three production proposal diffs |
| `proposed/` | Full structural and guard candidate modules |
| `audit/` | Exclusion ledger, machine-readable decisions, inventories, findings, source hashes |
| `evidence/` | Actual compiler logs, binding/measurement receipts, static dependency evidence |
| `scripts/` | PDF build and read-only integrity/source verification |

## Provenance and scope

All production-source quotations and copied tables are attributed to the pinned ProveIt repository. The exact copied `ScalarPRCode.lean` retains its original content. The packet does not relicense upstream code. It is a research proposal, not an upstream commit or a published change to the repository.

The exclusion review covers principal report indexes, cumulative taxonomies, relevant detailed passages and notes, candidate-specific searches, and the incoming retirement ledger. It does not claim a line-by-line semantic rereading of every historical snapshot or log. `audit/novelty_decisions.json` records closest prior contracts and explicitly excludes repeated mechanisms, including deferred and future-work suggestions.
