# Portable replay of the Report58 independent audit

This adapter replays the **already frozen independent audit** of the five-signal Diophantine certificate. It does not rewrite the mathematical certificate, any checker, or any frozen receipt. It requires no third-party Python packages and no network access.

## Run

Use CPython on a POSIX filesystem. Python 3.9 or newer is required by the frozen checker syntax; the tested environment is Linux, CPython 3.12.14. Cross-version or non-POSIX behavior is not asserted beyond the explicit checks.

Supply all three paths explicitly. They must be canonical absolute paths, with no symbolic-link components, `.`/`..` components, doubled leading slash, or trailing slash. Spaces are supported when shell-quoted.

```sh
python3 -I -S -B /absolute/path/replay_report58.py \
  --packet-dir /absolute/path/frozen-certificate \
  --audit-dir /absolute/path/frozen-independent-audit \
  --output-dir /absolute/path/new-replay-output
```

- `--packet-dir`: an exact copy of the complete **33-file** frozen author packet. This includes source documents, all four DAGs, existing author receipts/manifests, and inert author Python files. Those author programs are **never executed or imported**
- `--audit-dir`: an exact copy of the complete **11-file** root independent-audit directory, including its three frozen independent checkers, reference receipts, full witness file, reports, and `AUDIT_MANIFEST.json`
- `--output-dir`: a **nonexistent** directory whose parent already exists. It must be external to both input trees. Never point this at a scientific source or existing results folder

The full expected file inventories and SHA-256 values are embedded in the adapter and repeated for convenient inspection in `REPLAY_SOURCE_PINS.json`. Unexpected files, missing files, altered bytes, unexpected empty directories, symlinks, and nonregular entries fail authentication. Do not add a README or replay outputs inside either frozen input tree. Put these portability files alongside those trees instead.

The two source directories may be relocated anywhere and may be read-only. The adapter does not assume access to `/workspace/shared` or any other original audit path. No installation is needed. Run with `-I -S -B` as shown: the adapter refuses a non-isolated invocation, site initialization, bytecode writing, or optimization. `-O` and `-OO` are refused because the frozen independent checkers use assertions.

A successful run exits zero and prints the location of `REPLAY_RECEIPT.json`. Any refusal or check failure exits nonzero. The output directory is never reused. If failure happens after it is created, the directory is retained with `REPLAY_FAILURE.json` and available logs; use a new path for another attempt.

## What is executed

Only these authenticated independent checker sources are compiled:

1. `audit_exact_source.py`
2. `check_power_dag_independent.py`
3. `audit_arithmetic.py`

Their exact SHA-256 values are pinned in the adapter. Their source bytes are compiled unchanged, with `dont_inherit=True` and `optimize=0`; no textual or AST patch is applied. The adapter itself is also reauthenticated by the child before execution. The child is a new `python -I -S -B` process with a minimal environment, an external working directory, and private read-only copies of the authenticated source inputs. The frozen files contain only imports, definitions, and path constants before their main guards.

The POWER checker has no `main()` function. Its original main guard's call to `audit()`, JSON serialization, file write, and print are reproduced in the adapter exactly; its mathematical function is unchanged.

No author emitter, author semantic checker, author internal-audit checker, source-freezing program, upstream program, saved physical program, simulator, trajectory replay, or Lean process is run. Those files, when present in the required author packet, are hashed as inert bytes only.

## Historical paths and the inherited physical audit

The frozen independent checkers contain original absolute path constants, and the exact-source receipt records those original path strings. A small logical-path facade redirects only the read, write, glob, and display operations that these pinned checkers use. It keeps the old path strings in regenerated receipts while routing all actual reads to the explicitly supplied authenticated input copies and all writes to fresh results.

This avoids modifying the scientific source and avoids normalizing away receipt differences. The facade is narrowly limited to the pinned input inventories and the four allowed result files. An unexpected path or operation fails.

The historical external physical-audit lookup is redirected to the already included, SHA-256-pinned `sources/INDEPENDENT_AUDIT.md` copy. Therefore replay checks the **frozen inherited physical-audit bytes**, not a newly discovered or independently reread external original. Its historical comparison with the packet copy is served by that same authenticated copy. The original root audit established byte identity to the external physical audit; portable replay relies on that frozen hash. This introduces no hidden external dependency and does not claim a new physical-proof audit or a new upstream-commit authentication.

## Exact comparisons and preservation

The following regenerated files must match the frozen independent-audit files **byte-for-byte**, in both the child and parent:

- `exact-source-receipt.json`
- `POWER_DAG_RECEIPT.json`
- `arithmetic-receipt.json`
- `full-positive-witnesses.json`

The arithmetic checker's captured stdout must also exactly match frozen `arithmetic-run.stdout.json`. There is no selective field comparison, path-stripping normalization, or tolerance. Printed historical paths are preserved deliberately.

Before and after execution, the adapter snapshots original and staged trees and checks file bytes, entry types, permission modes, sizes, modification/change timestamps, device/inode identifiers, link counts, and ownership. Access time is excluded because reads may update it. It never changes permissions of the supplied inputs. Staging copies are made read-only; the adapter verifies they also remained unchanged. A mismatch prevents a PASS receipt.

The fresh output contains:

- `REPLAY_RECEIPT.json`: authentication, exact-match hashes, source-preservation results, and actual worker isolation flags
- `results/`: the four exactly regenerated frozen result files
- Three checker stdout logs and worker stderr
- `_sandbox/`: private authenticated read-only source copies, retained to make the run inspectable

Keep outputs outside the release directory too if you want the release archive itself to remain pristine. The adapter enforces non-overlap with both explicitly supplied source trees; it does not infer a larger enclosing release root.

## Re-run the portability tests

The included test harness mutates only fresh temporary copies and checks that the original frozen sources stay unchanged:

```sh
python3 -I -S -B /absolute/path/test_replay_report58.py \
  --packet-dir /absolute/path/frozen-certificate \
  --audit-dir /absolute/path/frozen-independent-audit \
  --adapter /absolute/path/replay_report58.py \
  --receipt /absolute/path/new-portability-test-receipt.json
```

The receipt path must be new. Temporary workspaces are retained for inspection. The checked-in `PORTABILITY_TEST_RECEIPT.json` records 33 successful expected-outcome cases: relocated paths with spaces; read-only inputs; polluted Python environment with import traps; output reuse; missing/noncanonical/relative paths; nested outputs; symlinked input roots, ancestors, files and directories; dangling or ancestor output symlinks; missing, extra, and tampered scientific/checker/reference files; unexpected directories; missing arguments; missing isolation flags; and explicit `-O`/`-OO` refusal. `PORTABILITY_REVIEW.md` and its evidence document an additional independent review and regression test of the double-leading-slash alias guard.

## Security and assurance limits

This is reproducible execution of **trusted, authenticated, inspected** independent checkers. Python `-I/-S` provides import/startup isolation; the facade restricts the pinned checkers' intended I/O, and read-only staging reduces accidental writes. This is **not** an operating-system, network, container, or hostile-code sandbox. It does not defend against a hostile interpreter/stdlib, bind-mount aliases, malicious concurrent same-UID filesystem writers, or a compromised adapter/trust-anchor file. The complete source inventory is pinned by SHA-256, not by an external digital signature.

The mathematical assurance remains the original audit's scope: exact finite-source and arithmetic checks plus a conventional proof relying on the explicitly inherited physical theorem and pinned constructive Pell theorems. A successful replay is not a new Lean build, an all-exponent numerical witness test, or an independent authentication of the remote mathlib commit.
