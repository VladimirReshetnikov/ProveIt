# Validation artifacts (source-only review)

These helpers do not establish that the proposed Lean refactors compile. Lean
and Lake were unavailable during this review. Python helper tests are not Lean
proof tests. See `VALIDATION_REVIEW.md` for exact evidence and limitations.

## Safe, executed here: static source analysis

From the bundle root:

```sh
python3 validation/test_tools.py
python3 validation/static_audit.py \
  sources/Computability/DiophantineConsistency/Lean \
  --json validation/active_static_audit.json --csv validation/active_modules.csv
```

The scripts read source text, write only explicitly requested reports, use the
Python standard library, and do not execute fetched source or access the
network. The output's scope excludes archived `.lean` copies.

## Later: actual Lean replay

Use a **full** checkout at commit
`60e9c5d620c6c387d932876cfa2d9376f64ea56c`, with its exact Lean 4.32.0 and
locked Mathlib already available. The focused `sources/` directory in this
bundle is not sufficient. No helper installs dependencies. Inspect scripts
before execution. Obtain authorization before installation if prerequisites
are missing.

The upstream README explicitly uses (from the full repository root):

```sh
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/ZFCAxioms.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/CompilerAxioms.lean
```

Those are **future commands, not commands reported as successful here**. Also
run every one of the 220 existing check/audit files, not only these two summary
probes. Full baseline/candidate verification can write build outputs; do it in
authorized disposable worktrees. Do not delete checks to meet a line target.

`EndpointAudit.lean` and `expected_endpoints.txt` contain a selected 35-target
additional probe. Capture both stdout and stderr, preserve the Lean exit code,
and run:

```sh
python3 /absolute/path/to/bundle/validation/check_axiom_log.py \
  /path/to/endpoint-audit.log \
  --expected /absolute/path/to/bundle/validation/expected_endpoints.txt
```

A successful log parse is only one gate; it does not authenticate logs, check
compiler exit status, compile Lean, or replace full behavioral regression
checks. The exact expected list is mandatory, and cannot be empty. Resolve
unqualified existing check targets before making a central manifest.

## Files

- `VALIDATION_REVIEW.md`: detailed trust/validation recommendations and citations.
- `static_audit.py`: conservative lexical audit and import inventory.
- `active_static_audit.json`, `active_modules.csv`: measured active-source data.
- `print_axioms_sites.json`: source locations of all 2,163 printed audits.
- `pure_print_wrappers.json`: the 60 pure wrapper candidates, not a deletion list.
- `check_axiom_log.py`, `test_tools.py`: fail-closed log policy and unit tests.
- `EndpointAudit.lean`, `expected_endpoints.txt`: proposed selected endpoint probe,
  not compiled here.
- `replay_candidates.sh`: reviewed future replay harness, requiring a full built
  checkout and existing direct toolchain binaries; no dependency installation.

### Candidate replay without editing the checkout

After the prerequisite baseline build, use existing direct toolchain binaries
(not `elan` shims):

```sh
bash /absolute/path/to/bundle/validation/replay_candidates.sh \
  /absolute/path/to/full/ProveIt \
  /absolute/path/to/installed/lean-4.32.0/bin
```

An optional third argument selects a **new external** output directory. The
harness checks the exact clean commit, compiler version, package directories,
and baseline/Mathlib `.olean` prerequisites. It does not run `lake build`,
`lake update`, cache downloads, `elan`, repository generators, or installers.
It uses the already prepared `lake env` only to obtain the dependency paths.
Run it in an offline environment if an independently enforced network ban is
required; this script is not a network sandbox.

The generic `NineCoordinatePackaging.olean` is created before its compatibility
probe. The Lake-provided `LEAN_PATH` is preserved **inside** the child shell
before the temporary candidate path is prepended. The API-preserving Split and
Gap step replacements are compiled in separate output directories so that they
cannot shadow original modules in unrelated probes. Every invocation retains
merged stdout/stderr and its compiler exit status, then applies the strict
axiom policy. A failed compilation stops and preserves all diagnostics; an
unavailable runtime exits 69 rather than reporting success.

A successful future run establishes only candidate elaboration and the selected
axiom audits. It does not recompile downstream consumers against replacement
modules, migrate their APIs, run all 220 old regression files, or establish a
full clean/incremental build timing. These remain separate acceptance gates.

Preparation-time checks actually run for this shell artifact: `bash -n` syntax
check and the deliberately unavailable-toolchain branch (exit 69). Its
successful-Lean branch was **not run**.

Platform note: the replay harness targets Linux/WSL with Bash, Python 3, Git,
and GNU-compatible `readlink -f`; adapt that preflight on other platforms.
Baseline and dependency `.olean` files must come from a trusted, successfully
prepared build of the pinned sources. The harness checks their **presence**,
not their provenance or freshness, and does not rebuild or certify them.
