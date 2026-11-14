# Split-gate source experiment: rejected diagnostic

This directory records an attempted separation of the supplied combined guard into independently selectable proof-search heads. It is research evidence, not a new consistency machine.

## Result and exact limits

The repaired portable script `price_split2.py` was rerun against ProveIt commit `567266818aaeceb0f3a8f82debf303c8d84bddaf`. The fresh output is `price_split2.log`, with the machine-readable receipt in `split_price.json`.

| Quantity | Result |
| --- | ---: |
| Raw working states in the constructed candidate table | 206 |
| New source-reader states | 72 |
| Maximum matching size in the enumerated pair-fold opportunity graph | 6 |
| Nominal score, 206 minus 6 | 200 |
| Primitive source sites | 3,672 |
| Branch-sensitive symbolic runtime contracts | 4,782 |
| Contracts successfully checked before the first failure | 4,543 |

**The nominal 200-state score is not a validated physical machine.** The program only computes a maximum matching in the current opportunity graph. It does not apply that matching, check interactions between selected folds, emit a folded table, or prove a runtime theorem for such a table. The historical printed field `count_lower_bound` means only raw count minus this particular matching size; it is not a lower bound over other compilations or Turing machines.

The **unfolded 206-state candidate already fails** the universal source-to-runtime boundary check. The first reported failure is source site 3496, the zero branch of logical `dec 5` (physical register 7). Its source instruction is `('dec', 5, 3500, 3497)`, and its path is

```text
1010100111110000000
```

That path has seven trailing zero edges. The longest source path is 36 edges, and the maximum consecutive-zero run over the source is seven. These measurements and the failed boundary check are recorded exactly in the receipt. No claim of source simulation, blank-tape behavior, or equivalence with Con(PA) follows from this candidate.

The source edit drops the extra head when the guard is zero and leaves it when enabled. The two printed `HELPER` runs only exercise this local helper on two concrete register assignments; they do not establish the whole-source invariant. In particular, the changed stack shape would need a matching proof-search selector/compiler argument even if the runtime check succeeded.

## Files

- `probe_macros.py`: loads the pinned compiler and upstream source nodes; supplies a small concrete source interpreter for diagnostics.
- `map_nodes.py`: reconstructs the primary PA194 native table and maps source subtrees to existing physical controls.
- `split_v.py`: reads and expands the primary PA194 macro grammar; prints its macro word when executed directly.
- `price_split.py`: earlier version using an explicit clear-register loop. Its previously observed raw/matching/nominal counts were 207/6/201 and it also failed the runtime check. It is retained for provenance and was not rerun for this bundle. If run, it writes `split_price_explicit_clear.json` here.
- `price_split2.py`: revised version reusing the existing `node146` clear-register macro. This is the version reproduced in this bundle.
- `split_price.json`, `price_split2.log`: fresh receipt and full standard output from the revised version.
- `provenance.json`: upstream revision, Python version, and SHA-256 hashes of the upstream inputs used here.

The five diagnostic scripts originated in this investigation. Packaging changes replace the original absolute checkout path with `PROVEIT_REPO`, direct receipts to this directory, disable Python bytecode writes, and add explicit status/failure fields to receipts. The candidate source transformation and pricing procedure are unchanged. No upstream source files are copied into this bundle.

## Reproduction

Use Python 3 and a checkout of the pinned ProveIt revision containing the requested PA research area. No third-party Python package is needed. Set the environment variable to the repository root, not to its PA subdirectory:

```bash
export PROVEIT_REPO=/absolute/path/to/ProveIt
git -C "$PROVEIT_REPO" rev-parse HEAD
# Expected: 567266818aaeceb0f3a8f82debf303c8d84bddaf

cd /absolute/path/to/this/research/split_gate
python3 price_split2.py > price_split2.log 2>&1
```

The script exits normally because a failed candidate is its recorded research result. Inspect `runtime_validation.ok` in `split_price.json`; the expected value is `false`, with `failed` equal to `[3496, [7, true]]`. A normal process exit is not successful machine validation.

The principal upstream dependencies are:

```text
Computability/BusyBeaver/Research/PA/
  docs/pa194_conpa_2026-11-13/construction/compiler.py
  docs/pa194_conpa_2026-11-13/construction/symbolic_runtime.py
  docs/pa194_conpa_2026-11-13/construction/source/pa194.grammar.json
  docs/pa194_conpa_2026-11-13/construction/source/pa194.sites.json
  docs/pa194_conpa_2026-11-13/construction/tables/pa194.labels.json
  docs/pa194_conpa_2026-11-13/construction/tables/pa194.tm
  docs/pa196_research_2026-11-13/search/rotations/allocator-screen/build221.py
  docs/pa196_research_2026-11-13/search/rotations/allocator-screen/source_language.py
  jamesyc-upstream/pa196/PA196/Program.lean
  jamesyc-upstream/pa196/PA196/Conjugacy.lean
  jamesyc-upstream/pa196/data/pa196.tm
```

The numeric contract checker is the supplied independent Python symbolic executor, specialized from `BusyBeaver/M6/Runtime.lean`; this run does not produce a newly checked Lean theorem.
