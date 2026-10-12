# Forest and exceptional-kernel reproduction review

Reviewed the actual research scripts and `article/10_reproduction.tex` on
12 October 2026. This review does not modify production code or the article.
The two existing retained replay commands were checked; no full native audit
or optional expensive experiment was repeated for this review.

## Findings that affect a clean unpacked package

1. **The residual-kernel native subdivision input is mandatory in the current
   script.** Without `--skip-native`, `residual_kernel_audit.py` unconditionally
   opens
   `FAST/core_top_research/forest_exchange_audit.json` after processing the
   corpus. It does not check whether the file exists, does not fall back to
   the package evidence directory, and currently has no `--subdivision-source`
   argument. A missing file raises `FileNotFoundError`; it is not an optional
   omission of the eight subdivision cases.

2. **The article's current command sequence does not supply that input.** Its
   `forest_audit.py --output /tmp/forest-exchange-audit.json` writes a different
   path from the underscore-named file the kernel audit reads. The subsequent
   kernel command therefore fails on a clean patch-only checkout unless the
   retained forest evidence has also been installed at the expected path.
   The current article sentence saying the neighbouring input is read "when
   present" and describing it as "optional" is inaccurate for this script.

3. **The abstract graph runner has no hardcoded workspace path.**
   `run_forest_exchange_audit.py` requires `--fast`, and `--output` means an
   **output directory**, not a JSON filename. `--replay-only` reads
   `<output directory>/forest_exchange_evidence.json`. Its default is the
   directory containing the runner. Thus, if the runner is packaged under
   `tools/` and evidence under `evidence/`, a replay invocation must explicitly
   pass `--output "$PACK/evidence"`. Passing the JSON filename as `--output`
   is incorrect. Its current CLI is already portable when used explicitly.

4. **Fresh forest subdivisions require Regina; retained kernel/chain
   subdivisions do not.** `forest_audit.py` defaults to generating eight
   subdivisions with Regina. If Regina cannot be imported, the script still
   succeeds with only the 106 corpus cases and records that the subdivision
   generator was unavailable. It therefore does not necessarily reproduce
   the full 114-case retained report merely because it exits successfully.
   The retained forest JSON contains all eight raw triangulations and zero
   vectors, so the kernel audit and the chain audit can process those inputs
   without regenerating them. The retained measurement used Regina 7.4.

5. **The kernel replay is independent matrix replay, not a new geometric
   authentication run.** It reads the saved sparse source occurrence matrices,
   quotient matrices and traces, imports no planner, and checks the source
   matrix claims literally. Reconstructing those matrices from the native
   triangulations requires the full native audit and the pinned corpus.
   This distinction is already consistent with the scope of the evidence.

## Required files and input provenance

The target checkout must first be pinned to
`8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4` and receive this package's patch
or overlay, but not both as separate changes.

Files below `FAST` that these experiments directly need:

| File or group | Use |
|---|---|
| `fastunknot/core_forest_exchange.py` | Abstract joint-forest producer |
| `fastunknot/core_forest_exchange_verify.py` | Independent abstract replay |
| `tests/test_core_forest_exchange.py` | Twelve focused test methods, including exhaustive cases |
| `core_top_research/forest_audit.py` | Native restricted-strategy comparison |
| `core_top_research/residual_kernel.py` | Exact quotient and source lift producer |
| `core_top_research/residual_kernel_audit.py` | Finite matrix audit and retained replay |
| `fastunknot/core_top_reduction.py`, `core_top_reduction_verify.py` | New source top-incidence and independent native cancellation replay |
| Maintained `core_handlebody`, `normal_parallelity`, source geometry and integer codec modules | Existing native core construction and consumers |
| `marked_parallelity_research/corpus.json` | All 106 source triangulations and coordinate vectors; tracked at the pinned commit |
| `normal_orbit_research/fixtures.py` | Fresh layered-torus/subdivision generation; tracked at the pinned commit |

Package artifacts that must be retained:

| Package path | Contents / requirement |
|---|---|
| `tools/run_forest_exchange_audit.py` | Copy the reviewed scratch runner here if the README uses the commands below |
| `evidence/forest_exchange_evidence.json` | Four self-contained abstract examples and graph certificates; input for graph replay |
| `evidence/forest_exchange_tests.txt` | Full retained twelve-method test log |
| `evidence/forest_exchange_audit.json` | Native restricted-strategy results and, crucially, raw source packets for subdivisions q=1 through 8 |
| `evidence/residual_kernel_audit.json` | Six abstract examples plus 106 corpus and eight subdivision matrix certificates, 120 replay cases total |

The eight source packets occur under
`forest_exchange_audit.json["cases"]`, selecting records with
`family == "subdivision"` and reading each record's `source`. Each source
has `id`, `triangulation`, and `coordinates`. These are the actual retained
fixtures; the earlier incoming ZIPs are not needed. Corpus source packets
come from the pinned `marked_parallelity_research/corpus.json`, not from the
native forest report, which records their IDs and results.

Use the ordinary Python interpreter without `-O` or `PYTHONOPTIMIZE`: the
research audit intentionally uses assertions for its mathematical checks.
The retained runs used Python 3.12.14. The graph tests, finite matrix tests,
and both retained replay modes use the standard library. Native core
construction also uses the repository code. Regina is needed for fresh
subdivision generation, not for replay of the stored raw fixtures.

## Portable commands using the scripts exactly as currently written

The following variables are examples; all three must be absolute paths.
They do not depend on the original workspace location.

```bash
PACK=/absolute/path/ProveIt_Relative_Top_Handles_2026-10-12
FAST=/absolute/path/ProveIt/Topology/UnknotRecognition/fast
REPRO_DIR=/tmp/proveit-relative-top-reproduction
mkdir -p "$REPRO_DIR"
```

### Replay the retained abstract graph certificates

```bash
python "$PACK/tools/run_forest_exchange_audit.py" \
  --fast "$FAST" \
  --output "$PACK/evidence" \
  --replay-only
```

Expected report:

```json
{"serialized_certificates_replayed": 4, "producer_imported": false}
```

This branch reads existing evidence and does not run the twelve test methods.

### Regenerate abstract graph tests and examples in a separate directory

```bash
python "$PACK/tools/run_forest_exchange_audit.py" \
  --fast "$FAST" \
  --output "$REPRO_DIR/abstract-forest"
```

This writes `forest_exchange_evidence.json` and
`forest_exchange_tests.txt` inside the supplied directory and returns the
unit-test subprocess exit code. The test metadata should report twelve
methods, 12,350 exhaustive graph/row instances and 1,200 seeded cases.
For just the focused test module:

```bash
cd "$FAST"
python -m unittest tests.test_core_forest_exchange -v
```

### Replay the retained exact-kernel certificates

```bash
python "$FAST/core_top_research/residual_kernel_audit.py" \
  --replay-only "$PACK/evidence/residual_kernel_audit.json"
```

Expected report:

```json
{"replayed_cases": 120, "producer_imported": false}
```

No `--fast-dir` argument is needed in this branch. In fact the audit script
can be invoked directly from the full-file overlay for this one operation:

```bash
python "$PACK/integration/overlay/Topology/UnknotRecognition/fast/core_top_research/residual_kernel_audit.py" \
  --replay-only "$PACK/evidence/residual_kernel_audit.json"
```

### Regenerate only the finite matrix kernel tests

```bash
python "$FAST/core_top_research/residual_kernel_audit.py" \
  --fast-dir "$FAST" --skip-native \
  --output "$REPRO_DIR/residual-kernel-finite.json"
```

This needs neither the native corpus nor the subdivision fixture. It runs
the 21,304 ternary small matrices, 4,096 binary 4-by-3 matrices, 3,375 legal
partitions of binary 3-by-3 matrices, 2,000 seeded larger cases, large-integer
and invalid-input checks, and the six retained examples.

### Regenerate the full native kernel audit with the current fixed input path

```bash
cp "$PACK/evidence/forest_exchange_audit.json" \
  "$FAST/core_top_research/forest_exchange_audit.json"

python "$FAST/core_top_research/residual_kernel_audit.py" \
  --fast-dir "$FAST" \
  --output "$REPRO_DIR/residual-kernel-audit.json"
```

This intentionally installs the retained fixture at the path the current
script requires. It regenerates the finite matrix cases, all 106 native
corpus cases, and exactly the eight retained subdivision cases. It does not
need Regina for these saved subdivisions. Expected native counts are
100 complete corpus cores, six corpus obstructions, and eight complete
subdivision cores.

The chain audit already supports an explicit fixture path:

```bash
python "$FAST/core_top_research/chain_audit.py" \
  --subdivision-source "$PACK/evidence/forest_exchange_audit.json" \
  --output "$REPRO_DIR/chain-compatibility-audit.json"
```

The chain script derives `FAST` from its own installed location; it does
not currently offer `--fast-dir`. Unlike the kernel script, it checks that
the selected source file contains exactly subdivisions q=1 through 8.

### Regenerate native forest applicability with fresh subdivisions

```bash
python "$FAST/core_top_research/forest_audit.py" \
  --fast-dir "$FAST" --subdivisions 8 \
  --output "$REPRO_DIR/forest-exchange-audit.json"
```

With Regina available, this regenerates all 114 cases and the eight raw
source packets. Without Regina, its output explicitly records that fresh
subdivisions were unavailable; it will contain only the 106 corpus cases.
To request just the native corpus deliberately, use `--subdivisions 0`.
Neither mode automatically places its output at the kernel audit's fixed
input path. To use a freshly generated full source file in the unmodified
kernel script, copy that file to the same required location before invoking
the kernel audit.

## Recommended minimal portability improvement for root's packaged copy

The cleanest way to make the article's temporary-output sequence work is to
add `--subdivision-source` to the packaged `residual_kernel_audit.py`, matching
the chain audit. The needed change is small and does not affect producer
logic:

```python
parser.add_argument('--subdivision-source', type=Path)
```

Replace the fixed input assignment with:

```python
subdivision_file = (
    args.subdivision_source
    if args.subdivision_source is not None
    else args.fast_dir / 'core_top_research/forest_exchange_audit.json'
)
```

Then the article can use an explicit retained input without writing into the
checkout:

```bash
python "$FAST/core_top_research/residual_kernel_audit.py" \
  --fast-dir "$FAST" \
  --subdivision-source "$PACK/evidence/forest_exchange_audit.json" \
  --output "$REPRO_DIR/residual-kernel-audit.json"
```

Alternatively the source argument can name the newly generated forest JSON.
If exact reproduction of eight cases is intended, validate the selected
source records or state that expectation in the README. Do not silently
omit a missing input while describing the result as the complete 114-case
audit.

No code change is necessary for portable abstract replay. For clearer
input/output semantics in a packaged runner, root may optionally add a
separate `--evidence-input` path used only by `--replay-only`, leaving
`--output` as a directory. If this is done, make the actual replay path
`args.evidence_input or args.output / 'forest_exchange_evidence.json'`.
Do not introduce a default pointing back to the original scratch workspace.
The simplest current solution is to document `--output "$PACK/evidence"`.

## Suggested replacement for the inaccurate article sentence

If the script is left unchanged:

> The residual-kernel audit recreates its finite matrix tests and the native
> corpus, then reads subdivision source packets from
> `FAST/core_top_research/forest_exchange_audit.json`. Copy the retained
> `evidence/forest_exchange_audit.json` to that location before running the
> full audit, or use `--skip-native` for the finite matrix checks alone.

If the recommended input argument is added:

> The residual-kernel audit recreates its finite matrix tests and the native
> corpus. Pass `--subdivision-source` the retained forest audit JSON to use
> the eight recorded triangulations without regenerating them.

## Checks actually performed for this review

Read the article's reproduction appendix, both forest research scripts,
the full kernel audit, the relevant chain-audit argument handling, and the
forest unit-test imports. Confirmed the native corpus and fixture generator
are tracked by the pinned repository. Ran only the existing four-example
graph replay and 120-case kernel replay from an external current directory
with explicit absolute paths; both succeeded and reported the expected
counts. No production file or article file was edited.
