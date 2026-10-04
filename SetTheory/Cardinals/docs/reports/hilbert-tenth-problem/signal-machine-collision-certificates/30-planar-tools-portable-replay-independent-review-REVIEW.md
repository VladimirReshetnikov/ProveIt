# Independent source-bound review: Report60 portable replay

## Verdict

**PASS for the stated replay scope. No outstanding release blocker found.**

The final adapter authenticates nine frozen input trees (137 files), executes
only the three unchanged independently owned physical, geometry and arithmetic
checkers, and enforces seven exact expected-output comparisons. The quadratic
science and audit trees are authenticated and preserved **inertly**; no
quadratic executable replay is claimed.

## Exact reviewed source

- `replay.py`: `7a537eeaf0e26d3c720527343f2a0cd1321d3d3486046ee947ef3b5d76b9b71e`
- `selftest.py`: `7fd51425d3f2f23f68d256d527adab669d2d0f1fa76223b860e6770d5079ece2`
- `INPUT_PINS.json`: `c9794e791685c5a03e87d15a2b3bb0727847372b38fb067b3c8f7d64da1a3818`

`SOURCE_BINDINGS.json` also binds the documentation, requirements, all three
owned checker identities and per-tree file counts. Source was inspected as
inert text before execution. No frozen science, checker, audit or supplied
fixture was modified during this review.

## Source findings

1. **Exact authentication.** `canonical_path`, `inventory`, `authenticate` and
   the admission section of `main` require canonical absolute, disjoint input
   roots below the explicit release root. Ordered relative paths, entry types,
   file sizes and SHA-256 hashes must match the pinned inventory. Missing and
   extra entries, symlinks, multiply linked files and nonregular entries fail.
   The pin file's digest is embedded in the adapter. All nine inventories and
   three checker-to-audit pin bindings were independently checked.
2. **Fresh external output.** Output must be nonexistent and canonical, have
   an existing parent, and be disjoint from the release, adapter and selected
   input roots in both ancestor directions. Input validation precedes output
   creation. A previously successful output cannot be reused.
3. **No historical fallback.** Physical `SRC` and `OUT` are rebound before its
   `main`; geometry has no packet reads. Arithmetic receives all six required
   explicit CLI inputs. Its 95 manifest entries map historical logical names
   onto supplied roots rather than accessing historical locations. The two
   Report59 text dependencies are authenticated ordinary copies in a protected
   output-local view.
4. **Owned code only.** `inspected_namespace` rehashes each independent checker
   immediately before verbatim compilation with `optimize=0`. No author
   compiler, scientific checker, physical simulator, schedule or upstream
   executable is imported or executed. The physical independent checker
   reconstructs inert rational JSON and symbolic word data without advancing
   physical particles. The final quadratic additions do not change any
   executable path or any of the seven preexisting tree inventories.
5. **Preservation.** Successful completion requires before/after equality of
   full input, adapter and release inventories: bytes, modes, nanosecond
   mtimes, sizes and link counts. Physical and arithmetic add their own
   preservation checks; the dependency view is checked separately. Metadata
   may differ across relocated copies, but must stay unchanged during a run.
6. **Expected-output replay.** All seven comparisons are mandatory against
   authenticated frozen baselines: two physical outputs, two geometry baseline
   comparisons and three arithmetic outputs. The receipt is emitted only after
   replay, comparison and preservation checks succeed.

## Independent execution and evidence verification

- **Final complete replay under Python `-B -OO`: PASS.** All seven byte
  comparisons passed. Receipt SHA-256:
  `a834868957d1a63902f1557bb3ed2a5f5c0fa980a990e602ac5e98d259abc87c`.
- **22 reviewer-owned synthetic guard probes under Python `-O`: PASS.** Tests
  cover canonical paths, symlink and hardlink rejection, nonregular entries,
  altered/extra inputs, expected-output differences and retained assertions.
  Live audit-hook tests cover excluded reads, protected/external writes,
  directory reads, relative access, process creation and links. Only synthetic
  disposable data were changed. `guard_probes.py` and `GUARD_PROBES.json` are
  included for reproducibility.
- **Independent post-run checks: PASS.** The reviewer separately re-compared
  every actual output to its baseline, compared all four preservation file
  pairs byte for byte, reauthenticated all nine trees, and rescanned the live
  fixture with an `os.walk`/`lstat` implementation against the run's complete
  release baseline.
- **Final author selftest, 25 cases: reviewed PASS.** Both normal and read-only,
  differently named relocated copies replayed completely. The reviewer checked
  report/receipt hashes, actual expected-output bytes for both runs and their
  input preservation pairs. Original-release before/after bytes agree. Negative
  cases include symlinked adapter ancestors, a role outside the release, both
  new inert quadratic trees, corrupted source/checker/expected output/pins,
  extra/missing entries, hardlinks, missing flags and output reuse.

`EVIDENCE.json`, `REPLAY_RECEIPT.json` and `SELFTEST_SUMMARY.json` carry compact
machine-readable evidence. Raw test workspaces remain outside this clean
payload; their absolute locations are provenance only, never replay fallbacks.

## Review-driven corrections checked

The adapter now rejects invocation through a symlinked ancestor. Its trusted
runtime read/protection roots include `stdlib`, `platstdlib`, `purelib`,
`platlib` and the actual imported SymPy/mpmath package directories, addressing
the inferred split-installation portability gap. The final exact source was
replayed after these changes. A separate virtual-environment installation was
not built as part of this review.

## Boundaries

The nine selected trees are digest-authenticated; the complete outer release
is preserved, not independently authenticated by this adapter's pin file.
Python, its libraries and installed SymPy/mpmath are trusted runtime inputs.
SymPy's version is checked; installed package bytes are not cryptographically
pinned. The audit hook is supplemental protection for reviewed pinned code,
not a hostile-code or concurrent-filesystem sandbox. Successful replay
reproduces finite independent evidence, does not prove the universal theorems,
does not compile Lean and does not alter existing scientific qualifications.
