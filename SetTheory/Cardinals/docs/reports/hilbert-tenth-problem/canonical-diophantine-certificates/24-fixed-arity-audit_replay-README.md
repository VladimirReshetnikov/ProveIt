# Portable replay of the independent sandpile audit

This is a separate filesystem adapter for the frozen independent checker. It does not modify the checker, the submitted scientific source, or their recorded receipts. Its only scientific-runtime changes are the values of the checker's `SUBMITTED` and `HERE` path globals.

## Run after unpacking or moving the release

Use ordinary Python 3.9 or later, without optimization. Supply paths to the copied science and independent-audit directories; the adapter does not depend on their absolute locations or names.

```sh
python tools/replay_independent_audit.py \
  --source-root science \
  --audit-root independent-audit \
  --output /tmp/report50-independent-replay-unique
```

The sample directory names are placeholders for the release's actual layout. The output path must not exist, its parent must exist, and it must lie outside both frozen input roots. Choose a new external output path for each run.

The adapter:

1. Rejects `-O`, `-OO`, and `PYTHONOPTIMIZE` modes
2. Rejects symlink path components, symlinks anywhere in the input trees, nonregular input files, output overlap, and existing output
3. Verifies the exact frozen audit-manifest SHA256 and all scientific/audit file pins recorded in it
4. Loads only the authenticated bytes of the independently authored checker, directly compiling them without consulting cached bytecode
5. Disables bytecode writes, substitutes the two path globals, and runs that checker into the fresh output
6. Requires its scientific receipt and log to equal the frozen files byte-for-byte
7. Checks that both complete input trees retain the same files, bytes, modes, and modification timestamps

All submitted builders, submitted checkers, historical arithmetic schedules, and Lean files remain unexecuted. The source JSON is consumed only by the independent checker's formal polynomial comparison. The adapter is a reproducibility guard, not a sandbox for arbitrary untrusted Python. Its input manifest binds the one checker it executes to reviewed bytes.

## Outputs

- `audit-receipt.json`: byte-identical replay of the frozen scientific receipt
- `audit-run.log`: byte-identical replay of the frozen scientific log
- `replay-receipt.json`: adapter, source-preservation, and equality results
- `pell-pinned-fetch.json`: unchanged inert copy used by the checker

The scientific receipt SHA256 is `b38776cf4fad90ffe062e271cf77ea37cb869d39ee2b924dc357f37c0671c7d9`.

## Safety and relocation regression tests

The separately authored `test_replay_runner.py` is portable too:

```sh
python tools/test_replay_runner.py \
  --source-root science \
  --audit-root independent-audit \
  --output /tmp/report50-replay-safety-tests-unique
```

Keep the runner and test harness beside one another. The harness copies the frozen inputs into a temporary bundle, renames that bundle, executes the relocated runner, and requires both scientific and adapter receipts and the log to remain byte-identical. It also tests optimization refusal, output overlap, existing output, symlink paths and input members, altered source/checker pins, and ignoring extraneous cached bytes. Original files, modes, and mtimes are compared before and after all tests.

All 16 tests passed. Frozen test evidence is included under `evidence/`; the pin manifest records every packaged adapter and evidence file. Neither original science nor the original independent audit was changed to make replay portable.
