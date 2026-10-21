# Reproduce the three fresh Source158 leaves

Recover the original `zfc217-research` packet through its intake placement/archive map. Use Python3 with assertions enabled. The own runner copies the supplied packet to a new disposable directory, runs only the three explicitly selected leaf commands with60-second wall caps, records argv/exit/time and raw stdout/stderr, and binds their selected inputs and outputs. It does not invoke a wrapper, manifest suite, search or core runtime.

```sh
python3 -B run_selected.py --packet /absolute/path/zfc217-research --output /absolute/path/new-source158-replay
python3 -B review_actual.py --actual /absolute/path/new-source158-replay/actual.json --output /absolute/path/new-source158-replay/actual-review.json
```

The output directory must not already exist. The replay keeps an exact disposable packet under `packet/`, raw logs under `logs/`, and fresh semantic outputs under `results/`. The saved-result reviewer does not execute a candidate; it checks command status, raw-log/output bindings, the79-node/code3 result, the62/3968 cylinder census and the scanner's complete frame and separate wrong-turn/reachability fields.

The three commands run inside that disposable packet are:

```sh
python3 -B code/replay_seed3.py --check-only data/seed3-proof.json --output /absolute/path/results/seed3
python3 -B code/verify_action_variants.py data/k218.native.tm data/action-variants.txt --output /absolute/path/results/action-variants.json
python3 -B code/verify_scanner_route.py --accepted data/k218.native.tm --short data/delete50.native.tm --sites data/sites218.json --output /absolute/path/results/scanner-route.json
```

These are individually meaningful results: inherited K/S remain premises of the equality certificate; row rewrites are proved separately; and the scanner output rejects the proposed local runtime argument rather than every possible calibration. The historical full core-runtime result and broad search negatives were not freshly repeated.

The later216 rebinding has its own checker, exact216 input pin and result under `/tmp/k216-source158-row-rebinding`. It is separate from this delivered-packet replay.
