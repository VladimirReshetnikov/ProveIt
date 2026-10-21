# Recovering and checking the composed215 submissions

Run these standard-library Python commands from the repository root.
Recovery executes no supplied code and restores all 149 original members,
including archive-only articles, PDFs, ancillary proofs and notices:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake198.py /tmp/composed215-recovered
```

The two packet roots are
`/tmp/composed215-recovered/K215_Composed_Commands_Selector_2026-10-20/K215_Composed_Commands_Selector_2026-10-20`
and
`/tmp/composed215-recovered/K215_Composed_Selectors_2026-10-20/K215_Composed_Selectors_2026-10-20`.
Arrival commits001695a82b and 7e8cc0ee93 retain the ZIPs; placementb4209acc20
retired their working-tree copies. The [placement map](data/intake198-placement.json)
binds every new file, current alias and exact historical parent.

## Inspect saved evidence without running a candidate

Source 160's77-file saved view contains all 33 selected actual inputs, every
new output and every raw log. Large JSON files are reversibly compressed;
the original actual record and input captures are unchanged. The supplied
whole archives are recovered separately, not duplicated in that view.

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake198-source160/prepare_view.py --output /tmp/composed215-saved
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake198-source160/review_saved.py --run /tmp/composed215-saved --accepted Computability/BusyBeaver/Research/ZFC/candidate-k215 --literal-comparison SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake198-literal/comparison.json --output /tmp/composed215-saved-review.json
```

Expected statuses: `EXACT_SAVED_AUDIT_VIEW_PREPARED` and
`PASS_INDEPENDENT_SOURCE160_SAVED_ACTUAL_AUDIT`. These portable invocations
were replayed successfully after publication. They check saved objects and
events without importing a supplied checker or running a candidate again.
Source 161's three fresh leaves and exact outputs are retained uncompressed
under [data/intake198-source161](data/intake198-source161/).

The complete primary isomorphism and evidence comparison can be recomputed
without any candidate execution:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake198-literal/compare.py --accepted Computability/BusyBeaver/Research/ZFC/candidate-k215 --source160 /tmp/composed215-recovered/K215_Composed_Commands_Selector_2026-10-20/K215_Composed_Commands_Selector_2026-10-20 --source161 /tmp/composed215-recovered/K215_Composed_Selectors_2026-10-20/K215_Composed_Selectors_2026-10-20 --out /tmp/composed215-literal.json
```

## Fresh selected replay

Use fresh output directories. The first runner copies Source 160, extracts
its immediate parent as dependency data, then invokes only the nine reviewed
leaves. Its eight finite jobs each have90-second caps; the secondary full
runtime has a360-second cap. It captures33 inputs before and after and gates
both exact bytes and semantic receipts; exit0 alone is insufficient.

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake198-source160/run.py --packet /tmp/composed215-recovered/K215_Composed_Commands_Selector_2026-10-20/K215_Composed_Commands_Selector_2026-10-20 --output /tmp/composed215-fresh160
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake198-source161/run_selected.py --packet /tmp/composed215-recovered/K215_Composed_Selectors_2026-10-20/K215_Composed_Selectors_2026-10-20 --out /tmp/composed215-fresh161
```

Source 160 expects `NINE_SELECTED_SOURCE160_LEAVES_PASS`: both deterministic
reconstructions, both all-natural source checks, both blank/marker audits,
both full-context folds and the secondary runtime. The secondary proves 6,176
cases/1,698,845 symbolic rules/all 430 rows/minimum 9, and its complete blank
trace has 96,284 steps. The primary95,714-step blank audit is fresh, while
its full runtime transfers from accepted215 by the exact isomorphism.

Source 161's runner stays beside `selected-inputs.json`. It executes only the
new reconstruction, source graph audit and one-case mutation control, each
under 60 seconds. Its15 selected input files remain unchanged. See the
[precise fresh scope](data/intake198-source161/fresh-reproduction.md).

No submitted wrapper, manifest validation, ancestor proof suite, search,
C++ build or proof-assistant command belongs to these selections. The
ordinary source/compiler/calculus proofs are separately reviewed premises.
No further full-runtime rerun is needed merely to inspect the publication.
