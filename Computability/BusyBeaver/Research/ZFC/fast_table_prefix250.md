# Balanced lookup for the exact prefix250 table

[FastTablePrefix250.lean](../../Lean/BusyBeaver/ZFC/FastTablePrefix250.lean) gives a balanced transition tree for the exact [prefix250 machine](candidate-prefix250/README.md). Lean checks all 500 actions against `machinePrefix250`, then proves equality of the complete machine values. Later finite computations can use the faster lookup and transfer their results to the canonical table by this equality.

This module contains two theorems, `fast_transition_eq` and `fastMachine_eq`. It has no bootstrap or unbounded runtime theorem. The first 1,024-step checkpoint is a separate development; the final 585,431-step startup and consistency endpoint are outside this module.

The exact canonical input is `candidate-prefix250/zfc_prefix250.tm`, SHA-256 `0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e`. The tree format is adapted from the maintained `BootPerm252` implementation, while every action is generated anew from this table. Attribution for the construction remains with the upstream machine authors and the supplied prefix250 reports, as recorded in the candidate and table documentation.

## Checked evidence

The first source/audit run passed in 5.846 seconds and 0.256 seconds, with zero warnings, two ordered axiom probes and four client examples. `fast_transition_eq` has no axiom dependencies; `fastMachine_eq` uses only `Quot.sound` through function extensionality. The finite table equality uses trusted `decide +kernel`, with Lean's default proof limits. No native evaluation axiom or additional proof axiom is introduced.

The [exact verification record](results/fast-table-prefix250-verification.json) has SHA-256 `4abd436a5b20d0a9a68f9cff2f6579b45096e9c782478b4233ff989898dfd7b6`. Source SHA-256 is `40198939ed5d43337f8c601198c597de9f06a8f30b6ac07d10cdbad23b7319b5`; the fresh object is `099f3113a4419941eb449971120a3f3f012a62d5fbd1eafb67b815b491b5c59d`. The [history and review record](results/fast-table-prefix250-history.json) preserves the exact executed source, audit, guard, generator, logs and successful evidence, together with the independent review. That review also independently parsed the entire tree and matched all 500 actions to the canonical table.

The isolated check reuses only `BusyBeaver.Core` and the checked `TablePrefix250` object, with the supplied toolchain's implicit `Init` boundary. It performs no dependency build, download or compiler-version query. Compiler execution is serial, with `-j1 -M4096` and one shared 120-second source/audit budget. Exact providers and fresh-object hashes are checked before and after the audit.

## Reproduction

From this directory, source regeneration can be compared without executing Lean:

```sh
python3 generate_fast_prefix250.py --check
```

By default the maintained generator handles only the fast-table source. `--boot-output /absolute/path/BootPrefix250First.lean` explicitly requests additional untrusted first-checkpoint data. This optional output is not a bootstrap proof. The generator's source-producing functions are unchanged from the executed input; publication changes only path defaults and whether that extra output is requested.

A fresh external output directory is required for the guard:

```sh
python3 check_fast_table_prefix250.py --output /tmp/prefix250-fast-prepared --prepare-only
python3 check_fast_table_prefix250.py --output /tmp/prefix250-fast-checked
```

Preparation performs no proof command. The full check needs the exact recorded compiler and cached parent objects; it refuses a changed or absent provider. Source and audit bytes are identical to the successful run. The maintained guard differs from the executed guard only in repository discovery and file defaults. Publication adds no proof replay; the [publication record](results/fast-table-prefix250-publication.json) binds the maintained files to this evidence.
