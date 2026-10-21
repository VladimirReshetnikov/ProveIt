# Phase 6 legacy continuity

The 15 legacy modules checked in phase 5 remain reusable alongside the 187-module phase 6 primary closure. The combined set has 202 modules. This is a read-only continuity check: **no legacy module or typed client was compiled again**.

The [live receipt](result.json) checks the exact source, imports, direct dependency objects, proof objects and compiler logs for all 15 retained modules against the completed primary ledger. It also checks the historical five-client audit: its source, object, log and complete 45-module project import closure are unchanged. All 202 selected provider objects and logs were rehashed after the audit binding check. These findings preserve the historical audit; they do not assert a fresh 202-module build.

The inputs are the independently reviewed [phase 6 primary packet](../lean/README.md) and [phase 5 legacy packet](../../phase5/legacy/README.md). Their exact repository-relative paths and file hashes are recorded in `result.json`; their archives are referenced rather than copied here.

The [saved review](saved-review.json) checks those two archives, their indices, the continuity bindings and the five named historical reports. It neither examines live objects nor invokes the deeper predecessor validators or proof compilers. Run it from this directory, with an unused output path:

```sh
python3 -B review_saved.py --repo /absolute/path/to/Proofs --output /tmp/phase6-legacy-saved-review.json
```

`review.py` preserves the separate live checker and its original command-line interface. `stdout.log` and `stderr.log` record its successful run; `saved-v2.stdout.log` and `saved-v2.stderr.log` record the successful saved check. The first saved-reader attempt compared four count fields with a three-element expected tuple. Its source, failure and exact correction are retained in [history](history/saved-reader-v1/correction.json); the successor adds the missing zero. No proof data or live receipt changed.
