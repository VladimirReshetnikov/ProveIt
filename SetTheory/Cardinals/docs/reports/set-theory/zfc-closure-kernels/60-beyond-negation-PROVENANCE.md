# Provenance and license boundaries

## Pinned repositories

The source checkout used for this experiment was ProveIt commit
`a2bf288dead95b653919b86608e3f2cca47552f7`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/a2bf288dead95b653919b86608e3f2cca47552f7>

Its imported upstream reference is `jeff87654/busy-beaver` commit
`297ab8df7e5de329605c3875b4934643b371a5e3`:

<https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3>

The original 254-state machine was designed and built by **Mira-Cult**. Jeff's repository supplies its Coq verification. This package does not attribute the machine to its verifier or to the present experiment.

## Unchanged upstream source and backend

| Included file | Original path under upstream pin | SHA-256 of uncompressed included file |
|---|---|---|
| `data/Dag254.v` | `ZF/m254/coq/prog/Dag254.v` | `538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3` |
| `data/Prog254.v.gz` | `ZF/m254/coq/tm/Prog254.v` | `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746` |
| `vendor/TMBuilder.py` | `ZF/generator/TMBuilder.py` | `03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517` |
| `vendor/tm.py` | `ZF/generator/tm.py` | `2d00bf8c8324d8e9bc5639ba14e508091d854a7c93ecb96ab598f41c15ae9787` |
| `vendor/tmdb.py` | `ZF/generator/tmdb.py` | `4ccf4dab37438109a350d77259b5eb52e33ce110a954cd2d56a218e84e653526` |
| `vendor/LICENSE.wade` | `ZF/generator/LICENSE.wade` | `c1dffee77db98625debe39b47538e1d2f3b7956cbc7bcd6ed9363701b2177cfa` |

`Prog254.v` is losslessly gzip-compressed with a zero timestamp. Its decompressed bytes are unchanged. The checker validates the decompressed source hash, independently parses its literal register program, and checks the exact expanded tree against the small shared representation.

**Andrew James Wade** wrote the three compiler backend files. Their retained `LICENSE.wade` is MIT-0. The source import does not declare an upstream-wide license; inclusion here preserves authorship and does not relicense the Coq sources or Mira-Cult's machine under the compiler's MIT-0 license. This follows the license boundary already recorded in ProveIt's `lib/jeff-busy-beaver-zfc254/README.proveit.md`.

## Unchanged ProveIt reference artifacts

`data/reference252.tm` is the original-label table from:

```text
Computability/BusyBeaver/Research/ZFC/
candidate-permutation252/zfc_permutation252_old.tm
```

Its SHA-256 is
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
It is included as a frozen comparison and as the literal source of the 55 protected Box rows. It is not a newly constructed machine.

`vendor/strict_affine.py` is an unchanged copy of:

```text
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/
27-variant-experiments-machine_search-grammar_search-strict_affine.py
```

Its SHA-256 is
`da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce`.
It ports the symbolic rules described in upstream `M253.SymExec`; its four register-Box contracts remain attributed upstream obligations. The portable adapter in `verify_runtime.py` only loads the checker's reusable functions. It supplies an inert `cost_search` module name for an import used solely by the unused historical driver.

The original contextual emission used the ProveIt source27 code
`27-variant-experiments-machine_search-grammar_search-cost_search.py`,
the matching decoder-entry metadata, and the physical permutation in
`Computability/BusyBeaver/Research/ZFC/candidate252_independent_audit.py`.
The portable package includes the emitted initial 261-state table and checks its complete instruction contract directly, so replay does not depend on regenerating its historical contextual-sharing choices.

## New derived artifacts

`data/optimized_original203.json` is a lossless shared representation of the pinned 6,459-node `Prog254.v` tree. Its SHA-256 is
`9bcbe8c5927b28268f227ed1e40def5a13093928c8edb2b2c6cd89e6ae8df33b`.

`data/optimized_output_prefill2.json` applies the new negation replacement at all 30 matched occurrences. Its SHA-256 is
`dbbefd67b689a77ab43dddcbb9da969a852352346b5afc2c5db2bb0165a25dfc`.

The two complete optimized binary tables have these hashes:

| Table | Working states | SHA-256 |
|---|---:|---|
| `prepared_runtime/prefill261.tm` | 261 | `65ad4a3a321e76ed32dd2fd44d3e741df0fb240487f6c559579a403705fe15ea` |
| `prepared_runtime/prefill255.tm` | 255 | `463067a5a42476c8efeacb296d83df69b7366b0d1894a4e11f418840e79fb0fb` |

The source control tables in `tables/` are regenerated exactly by `verify.py`; their individual hashes are in `results.json`. They use the included Wade backend, include its complete framework, and have 281 working states each.

The new scripts are `verify.py`, `verify_runtime.py`, and `macro_signatures.py`. The first two reject disabled assertions. The latter is an engineering matcher for increment-block operation bisimulation. Neither the matcher nor the newly generated tables are represented as having a new proof-assistant-checked endpoint.

`logs/uniform_folds.json` and `logs/mixed_folds.json` are unmodified development search logs. They can contain the original scratch paths as historical provenance. Those paths are not runtime dependencies of either portable checker. `results.json` and `runtime_results.json` are measured outputs of the portable scripts; elapsed times may change on rerun.
