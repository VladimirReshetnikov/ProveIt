# Exploratory scanner-layout records

This packet supplies the records behind the report's scanner-layout discussion. **No scanner-state reduction or smaller complete Turing machine was obtained.** The data distinguish decoder geometry from valid contextual runtime sharing.

The original shared decoder has 203 nodes, maximum consecutive zero-edge depth 7, and maximum path depth 34. All 238 first-step closed-subroutine reassociations retain a maximum zero depth of at least 7. A historical beam search visited 30,564 distinct layout keys, including its initial layout, over 12 rounds at width 12. It saved four layouts with maximum zero depth 6: three have 204 shared nodes and one has 205. A possible one-state scanner saving is therefore offset by at least one additional decoder node in these saved examples.

Combining each of these four layouts with each of the three negation variants yielded 12 changed source DAGs. The prefilled and direct variants retain maximum zero depth 6; the add-eight-afterward variant has maximum zero depth 7. All 12 attempted contextual emissions with the shorter scanner were rejected by the strict sufficient checker at guarded source case 139. Four attempts on the saved layouts without a negation rewrite also failed at case 139. These failures provide no new binary-machine bound.

## Portable quick replay

```sh
python -B verify_layouts.py --output layout_recheck.json
```

Python 3.10+ standard library is sufficient. There is no checkout or network dependency. Assertions must be enabled.

The quick verifier:

1. Checks the frozen input/import hashes and the exact original 203-node source DAG.
2. Reconstructs all 238 first-step choices, verifies that they are distinct, and measures their zero depths.
3. Replays every step of each of the four saved histories, checking that each step is one of the allowed closed-subroutine reassociations or commuting-increment choices of the current DAG.
4. Checks that each replay yields the exact recorded DAG, root, node count, zero-depth metric, and path depth.
5. Independently measures the 12 included combined DAGs and matches them with the source-metric and failure records.

It **does not rerun the 30,564-layout beam search or the contextual TM emitter**. Their counts and case-139 failures are explicitly historical recorded results. `replay_result.json` records what the quick replay actually checked. No expensive search was rerun during packaging.

The unchanged pure geometry helpers are in `vendor/`. Loading their definitions does not execute their historical command-line drivers or read an external checkout.

## Included recorded outputs

| File | Contents |
|---|---|
| `records/short-zero-layout.json` | Original beam parameters, 12 round summaries, four complete saved DAGs and their mutation histories, final best layout, elapsed time |
| `records/short-zero-price.json` | Original four failed contextual-emission attempts on those layouts, including source paths and first failed case |
| `records/combined-source-metrics.json` | Original node, leaf, depth, and zero-depth measurements for 12 negation/layout combinations |
| `records/combined-runtime-prices.json` | Original 12 failed contextual-emission attempts, all first failing at source case 139 |
| `data/original203.json` | Frozen shared original decoder, also checked against exact `Prog254.v` in the separate negation packet |
| `data/combined_*_dag.json` | All 12 literal changed DAGs supplied to those pricing attempts |

The field `states_examined` in the beam log counts **visited decoder-layout keys**, not working states of a Turing machine. Its final value 30,564 includes the initial layout. The result does not mean that every possible 204-node layout was examined. The beam retains only a bounded frontier and imposes geometry filters.

The pricing log's `physical: 2` for the failing `CC` instruction is the stored **continue depth 2**, not a register selection. At that path the inherited contextual emitter reaches an unapproved extra increment before the expected continuation; the strict checker reports an unsupported second Box action. The field name comes from the generic historical pricing driver.

## Historical drivers and their dependencies

Files under `historical/` are unchanged snapshots of development scripts. **They are not the portable entry point.** Their path assumptions refer to the original development workspace; running them directly from this flat archival directory will not reconstruct that workspace.

`import_manifest.json` records every copied file's exact development-relative source path and SHA-256. To rerun a historical driver, restore those paths beneath a workspace root and provide the pinned ProveIt inputs described below. The manifest permits this restoration without guessing the intended directory hierarchy.

- `agent_runtime/short_zero_layout.py` imports `agent_runtime/grammar_search/cost_search.py`, which imports the included rotation, DAG, context, and table helpers. It loads `grammar_search/decoder_entries.json` and the original 254 table under `agent_runtime/upstream253/ZF/m254/machine/zfc_254.tm`; it also computes its historical protected initialization trace at import. It does not use a new proof-assistant build.
- `agent_runtime/price_decoder.py` uses those same contextual-emitter inputs plus the pinned ProveIt `Computability/BusyBeaver/Research/ZFC/candidate252_independent_audit.py` and `lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm`. It applies the existing physical permutation and, with `--scan8`, identifies scanner label 74 with 84. Its successful runtime pricing would still require the declared Box contracts. The included attempts all failed.
- `agent_architecture/combine_short_zero.py` imports `inspect_negation_regions.py` and `macro_signatures.py`. The inspection helper reads the pinned source09 DAG utility and the exact upstream `Dag254.v` and `Prog254.v` under the ProveIt checkout. It reads `agent_runtime/short-zero-layout.json` and emits the included 12 DAGs. That historical helper prints exploratory diagnostics at import; none are required by the portable replay.

The historical beam invocation used width 12, depth 12, and a 300-second limit. The logged 12-round run reached the depth bound. This is a completed run of that bounded beam policy, not an exhaustive source-layout search.

## Provenance

All pinned ProveIt inputs refer to commit

```text
a2bf288dead95b653919b86608e3f2cca47552f7
```

<https://github.com/VladimirReshetnikov/ProveIt/tree/a2bf288dead95b653919b86608e3f2cca47552f7>

The two unchanged `vendor/` helpers and the historical `cost_search.py`, `prior_context_search.py`, `prior_rm_verify.py`, `analyze_table.py`, and `strict_affine.py` are exact copies of:

```text
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/
27-variant-experiments-machine_search-grammar_search-<filename>
```

The contextual entry metadata is copied from the corresponding file:

```text
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/
27-variant-experiments-machine_search-grammar_search-decoder_entries.json
```

The imported upstream machine/source pin is
`297ab8df7e5de329605c3875b4934643b371a5e3` in `jeff87654/busy-beaver`.
The original machine is Mira-Cult's work, with the referenced verification supplied by Jeff; the reused compiler and related research authorship are preserved by the main packet's provenance. No imported source is relicensed here.

The new contributions in this packet are the recorded beam experiment, combined-source experiments, and the small portable geometry/history verifier. A valid finite graph reassociation and a smaller zero-depth number do not establish that the original interpreter shortcuts remain sound in the new contexts. The failed pricing attempts are precisely why no scanner saving is claimed.
