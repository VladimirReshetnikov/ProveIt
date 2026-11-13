# Fixed-85 lexical frontier: bounded source-location inventory

This inventory classifies the 94 names left unresolved by `ordinary13-fixed85-native-composition-draft/scan.py`. It uses the exact source-root paths configured in the present worktree and the Mathlib package linked by this worktree, plus one explicitly identified alternate Foundation checkout. It does not copy, build, modify or authenticate providers, and it does not claim that the selected sources elaborate.

After the Foundation submodule was initialized, the current snapshot classifies the names as follows:

| Classification | Names | Location or limit |
|---|---:|---|
| Other repository source roots | 24 | 19 BusyBeaver, 4 ZFCinPA and 1 PAHF files exist under their configured `lakefile.toml` source roots. The earlier scanner searched `Computability/DiophantineConsistency/Lean` for qualified names, so it did not find these roots. |
| Configured Mathlib package | 42 | Exact `.lean` paths exist under the worktree's `.lake/packages/mathlib` link. |
| Lean toolchain | 1 | `Lean.Elab.Tactic.Omega` exists in the current toolchain source. |
| Configured Foundation source root | 26 | All exact paths now exist under this worktree’s `lib/FormalizedFormalLogic-Foundation`. Its clean HEAD equals the gitlink `32e1a0956a8622fad067328ca1959729a7634428`. |
| Missing in checked roots | 1 | `Mathlib.Tactic.Omega` has no exact source under the configured Mathlib v4.32.0 checkout, and its expected Mathlib-package `.olean` is also absent. Another source root or compiled provider may exist; none has been authenticated. |

The source path through the selected local lexical graph to the missing name is:

```
Fixed85Endpoint → Positive83GammaCalibration → Positive81ExactMain
→ Positive81Calibration → EtaNaturalGraphEarlyIndex → EtaNaturalRankIndex
→ ResidueCompactQBound → ResiduePellCoordinates → ResidueQBalanceGraph
→ ResidueSignFreePower → Mathlib.Tactic.Omega
```

The final edge is an actual import line in the pinned `ResidueSignFreePower.lean.src`. `Lean.Elab.Tactic.Omega` is a different available module. Changing the import or the proofs that use `omega` requires a separate source review and Lean validation, particularly for abstract model arithmetic; this inventory makes no claim that such a change is sufficient.

`pre-initialization-receipt.json` preserves the prior snapshot, when these 26 configured Foundation paths were absent but existed in the separate clean checkout at `/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation`. Its SHA-256 is `045fbe5b352e4fa3edd79af27ab50e1759200bb1b1b232a893df024b9ba3c5be`. It is historical evidence and will not reproduce against the initialized worktree. `receipt.json` records the current state: each name, source path and SHA-256, the configured Mathlib revision, both Foundation checkout revisions and cleanliness, and the source-only route. Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-fixed85-frontier-source-inventory/check.py | cmp - research/ordinary13-fixed85-frontier-source-inventory/receipt.json
```

The check is an environment snapshot: it reports a change if a configured path, selected file, checkout cleanliness, revision or provider availability changes. It does not scan all machine paths, follow the newly located sources' imports, examine all possible object roots, prove source coherence, inspect axioms or establish the endpoint.
