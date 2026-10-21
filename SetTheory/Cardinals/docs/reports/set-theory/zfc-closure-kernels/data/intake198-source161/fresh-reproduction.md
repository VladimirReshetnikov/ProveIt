# Source161 selected fresh checks

Three newly selected leaves passed in a disposable copy. Reconstruction took0.1142s, source comparison0.2646s, and the one-case mutation control0.0642s, each under its own60-second cap. All exited0 with empty stderr. Fifteen selected input files stayed byte-identical. Exact argv, working directory, caps, durations, stdout/stderr identities, semantic gates and output identities are retained in `actual.json`.

The reconstruction reproduces all four source/native/dense/map files exactly:215 states,430 rows,36 retained changes and deletion185 relative to the partial216 naming. The two independently implemented source resolvers agree on4,751 primitive operations and6,175 guarded successor edges plus halt. Reference and candidate have202 distinct subtrees;346 addresses agree, depths44/47 and maximum zero run6.

The optional mutation leaf proves the original source4697 CB1 contract, then replaces135/1=0L302 with0L10 and regenerates the block lemmas. The latter fails with the expected `Unknown run may be empty` symbolic obligation. This is a failure of the checker to establish that altered contract, used as a concrete detector control. It is not an independent semantic counterexample and does not prove general checker soundness.

No complete runtime, blank startup, wrapper, manifest, archive ancestor or proof-assistant build was rerun. Exact initial-state/dispatcher/halt-preserving conjugacy transfers the already accepted repository K215 runtime and blank result. Own inert comparison also matched all6,176 saved case records and95,714 stored startup events after renaming; delivered runtime timing remains attributed to the submitter.

The newly authored runner is portable without changing supplied source. Keep `run_selected.py` beside `selected-inputs.json`, recover the Source161 archive unchanged, then run:

```sh
python3 -B run_selected.py --packet /path/to/K215_Composed_Selectors_2026-10-20 --out /path/to/new-work
```

The output directory must not exist. The runner copies the packet, invokes only the three reviewed leaves, preserves failures and raw logs, and separately checks semantic output fields and exact reconstruction bytes. It does not import or invoke the delivered `verify.py`. `dossier.md`, `review.json` and `replay-plan.json` remain unchanged pre-execution review records; `actual-review.json` is the additive post-execution result.
