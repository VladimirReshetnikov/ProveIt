# Reproducible machine experiments

This directory contains the selected machine-side artifacts accompanying the
16 October 2026 report. It can be moved or extracted independently of the
rest of the report. Its scripts use Python's standard library; no network
access, third-party Python packages, Lean, or Coq are needed for these runs.

**No new machine below 253 working states was obtained.** The 254 and 253
tables are prior work. The 252-state table is a prepared runtime body and
has no successful blank-tape initializer. The new contributions here are
the finite row-coverage certificate and the bounded bootstrap-reuse search.

## Quick independent verification

From this directory, run:

```sh
python3 -B verify_row_witnesses.py --json verification.json
```

Expected result:

```text
PASS: 504 literal rows; 26035 witness replay steps; pinned table and program; no symbolic oracles
```

This command was run successfully from the packaged directory.
`verification.json` records the result and hashes the actual verifier and
its three input files. The verifier reads only `machine/zfc_254.tm`,
`Prog254.v`, and `row_coverage.json`. It reconstructs the runtime delta,
checks instruction paths against the literal published program, builds each
finite input tape, and executes literal Turing-machine transitions to the
claimed state/read pair. It does not import `symexec.py`, `tmlib.py`, or
register-box summaries.

Use ordinary Python with assertions enabled; do not use `python -O`.
`-B` merely avoids creating bytecode-cache files.

## Rebuild the inputs and coverage certificate

```sh
python3 -B prepare_inputs.py
python3 -B row_coverage.py
python3 -B verify_row_witnesses.py --json verification.json
```

`prepare_inputs.py` checks the SHA-256 hashes of the two pinned inputs. It
derives the old-label runtime table from the 254-state table and reconstructs
the complete instruction tree from `Prog254.v`. Its generated `paths.json`
has 6,460 leaves, 6,459 internal nodes, and maximum path depth 34, excluding
the three-bit prefix `110`. The JSON is a reconstruction from the accepted
program, not a claim of byte equality with the author's original JSON.

`row_coverage.py` executes 8,432 complete prepared-instruction cases:
8,391 ordinary cases plus 41 cases from the first 30 instruction leaves
with larger concrete register values. The input has gap 40, nine named
physical registers, and one spare block containing zero. Positive
decrements append another zero block. Every stored witness has only zero
blocks after the nine named registers.

| Coverage measurement | Packaged result |
|---|---:|
| Working states | 252 |
| Distinct state/read rows | 504 |
| Complete instruction executions | 8,432 |
| Total literal moves in the generator | 2,783,994 |
| Maximum moves for one complete case | 526 |
| Moves in the independent witness replay | 26,035 |

The earlier exploratory generator also assigned 2 to an unused tenth
block in the 41 larger-register cases. The packaged version strengthens
the input condition by keeping spare blocks zero. Its aggregate move count
and maximum are therefore the updated values in this table; the coverage
of all 504 rows and the independent replay count are unchanged.

**Scope of the certificate:** every row is reached from some concrete
prepared instruction input. It does not show that every row occurs on the
actual blank-tape run. It does not establish an instruction simulation for
all register values, a new kernel proof, or a state-count lower bound.

## Reproduce the bounded bootstrap search

```sh
python3 -B search_boot_relocation_complete.py
```

This regenerates the runtime and paths, checks the pinned Python symbolic
executor, verifies the unmodified runtime against all 8,391 affine
instruction cases, and tests the specified candidate family. The original
run took about 98 seconds on the research environment; runtime elsewhere
will vary. It writes `boot_relocation_complete.json` and prints progress.

The included result is from that completed run: **218 eligible states,
251 alternative destinations per state, four common write/direction pairs,
218,872 candidates, and no survivors.** This full search was not rerun
during packaging.

For each eligible state `q`, the search records predecessor rows that can
lead to `q/read 0` over the affine instruction suite. It redirects those
rows to one common alternative destination with one common write symbol
and head direction. It replaces `q/read 0` by `1 R97`, the known first
initializer transition. Register-box states, the dispatcher, and relevant
protected predecessor rows remain protected. A candidate must pass every
affine instruction case before being recorded as a survivor.

This is not exhaustive over all 252-state machines. It does not allow
independent replacements for each predecessor row, arbitrary multi-state
rewrites, or changes to the protected register machinery. The checker uses
the unchanged upstream register-box contracts and a fuel bound of 1,000
symbolic iterations. Fuel exhaustion or unsupported symbolic execution
rejects a certificate; it does not prove semantic inequivalence.

`symexec.py` is the upstream design executor, retained byte for byte. The
search extracts its execution definitions and adds observation-only
predecessor recording in memory. The search script contains those changes
explicitly. This Python checker is not the upstream Coq kernel checker.

An optional command for just the unmodified runtime's affine interface is:

```sh
python3 -B symexec.py machine/runtime252_oldlabels.tm . 40
```

## Machine files and conventions

Each transition line contains `state read write direction next_state`.
Directions are `L` or `R`; the alphabet and blank are binary, with blank 0.
Working-state counts exclude the distinct terminal state.

| File | Working states | Start | Terminal | Status |
|---|---:|---:|---:|---|
| `machine/zfc_254.tm` | 254 | 0 | 254 | Published blank-start table; upstream Coq proof |
| `machine/zfc_253.tm` | 253 | 0 | 253 | Prior public PR 20 table; supplied as a comparison |
| `machine/runtime252_oldlabels.tm` | 252 | 0 | 254 | Prepared runtime only |

The prepared runtime retains the 254 table's old numerical labels. Delete
states 5 and 8; replace `3/read 0` by `0 L48` and `49/read 1` by `0 R64`.
All instruction witnesses start at old dispatcher state 96. The runtime
file's `start 0` directive does not turn it into a successful blank-start
consistency machine.

The 253 table is not used by either experiment. Its prior proof claims are
documented in the pinned upstream pull request and report; this package
does not include or rerun their full Coq dependency closure.

## Files and provenance

`UPSTREAM.json` gives immutable source URLs, commit pins, file hashes, and
attribution for the five upstream inputs. `THIRD_PARTY.md` records the
license/ownership boundary. The generated input files, certificate, and
search-result JSON are included for direct inspection. Exploratory
binaries, large logs, unrelated machine variants, and Coq build artifacts
are omitted.

Primary sources:

- [254 construction and verification](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254).
- [Prior 253 reduction, PR 20](https://github.com/jeff87654/busy-beaver/pull/20),
  pinned to [mira-emmy's commit](https://github.com/mira-emmy/busy-beaver/tree/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253).
- [ProveIt research host at the inspected commit](https://github.com/VladimirReshetnikov/ProveIt/tree/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels),
  whose source 04 already records the 252-state runtime body.
