# Validation records

`integrated_full_replay.json` and `integrated_full_logs/` record the clean, relocated full primary replay: all 6,167 unbounded runtime cases were freshly derived, with exact identity to the retained case summaries. The conditional alternative was also reconstructed and checked. The recorded portable manifest is retained as `integrated_full_manifest.json`.

The final packet subsequently added the separate dense canonical startup replay and executable negative-control checks; its exact machine, source, logic proof, and runtime engine bytes were unchanged. `final_quick_replay.json` and `final_quick_logs/` then checked the final 86-file portable manifest, executed the additional checks, and reconstructed both candidates again. The final replay's primary runtime audit reads the previously regenerated unbounded derivations rather than rerunning their induction construction.

Neither run freshly replayed the inherited K224/K225/K226 ancestry or compiled a new Rocq/Lean endpoint. The unchanged ancestral archive and explicit optional replay flags are supplied for that separate scope.

A subsequent advertised `--baseline` run passed in 59.62 seconds, including the unchanged K224 quick replay and its nested K225 certificate replay. `baseline_quick_replay.json`, `baseline_quick_logs/`, `inherited_K224_quick_receipt.json`, and `inherited_K224_quick_logs/` retain that result. The full new-machine runtime was not repeated, and no old full-runtime or proof-assistant build was requested. The final portable manifest remained unchanged.
