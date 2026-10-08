# Connected causal kernels for RIII unlocking

Research contribution prepared for Vladimir Reshetnikov's ProveIt project, 8 October 2026.

## Main result and scope

The accompanying article proves a deterministic `poly(N,k) * 2^O(k)` algorithm,
with polynomial workspace, for this exact subproblem:

> Can at most `k` Reidemeister-III moves expose a crossing-decreasing RI or RII
> move in the given classical one-component `N`-crossing diagram?

The core arguments are dynamic commuting layers, a bounded-slot forest count,
and a terminal causal-cone theorem: a successful bounded episode has a retained
witness whose move cores and terminal core form a connected set of at most
`3k+2` crossings in the INITIAL projection graph. The full read/write footprint
is NOT replaced by this core. Each RIII footprint has at most 18 darts / nine
crossing vertices; at most 36 next-layer candidates meet one parent footprint.
The union of a terminal cone's full supports is the initial closed neighborhood
of its core union and has at most `7k+6` crossing vertices.

A conservative explicit search bound is `poly(N,k) * 2^(23k+11)`.
The older birth-constrained search bound is sharpened from
`N^(b+O(1)) * (C*k)^k` to `N^(b+O(1)) * 2^O(k)`.

This is NOT a general quasi-polynomial unknot recognizer. With a deterministic
reduction policy, unlocking budget `g`, residual crossing count `r`, and an
exact exponential fallback, the article proves
`poly(N,g) * 2^O(g) + 2^O(r)`. The actual-run conditions
`g,r = O(log(N)^2)` suffice for `N^O(log N)` recognition; no uniform bounds
of that kind are claimed.

The arguments are self-contained but have not been externally peer reviewed or
formalized in a proof assistant. Priority over all existing local-rewrite
literature has not been established. Classical heap/Cartier--Foata machinery
is attributed, not claimed as new.

## Files

- `article.tex`, `article.pdf`: self-contained article, proofs, measured results,
  13 further research questions, references, and proof-dependency ledger.
- `src/`: standard-library Python research kernels, command-line query, verifier,
  and opt-in production snapshot/commit adapter.
- `tests/test_kernels.py`: 27 unit tests, including transaction safety.
- `data/audit.json`, `data/benchmark.json`: complete audit summary and all paired
  kernel timing samples. `data/benchmark.csv` is a convenient summary.
- `artifacts/witness_00.json` ... `witness_09.json`: ten positive nonempty
  RIII-unlocking certificates, independently replayable without searching.
- `INTEGRATION.md`: exact integration boundaries and required production checks.
- `SOURCES.json`: repository provenance, pinned source reads, literature.
- `MANIFEST.sha256`: checksums of shipped files.

## Quick start

Python 3.10 or later; tested here on CPython 3.13.5. No third-party Python
packages are required. From this directory:

```sh
export PYTHONPATH=src
python -m unittest discover -s tests -v
python src/verify_certificate.py artifacts/witness_00.json
python src/unlock.py artifacts/witness_00.json --depth 4 \
  --max-trials 100000 --certificate /tmp/unlock.json
```

Query inputs can be `{"pd": [[...], ...]}` or
`{"braid": {"strands": 3, "word": [1, 2, 1, 2]}}` (only one-component closures
are accepted). The example braid is a knot; other braid words may be links and
are rejected by this package. A certificate includes a PD field and can also
serve as a fresh query input.

On Windows PowerShell, set `$env:PYTHONPATH = "src"` before the Python commands.

API example:

```python
from connected_kernel import kernel_unlock
from dart_kernel import from_braid
from layered_search import SearchExhausted, Stats

state = from_braid(3, [1, 2] * 4)
stats = Stats()
try:
    witness, tested_regions = kernel_unlock(
        state, 4, max_trials=100_000, max_regions=10_000, stats=stats
    )
except SearchExhausted:
    # UNKNOWN for the bounded query. Continue the exact recognition pipeline.
    witness = None
else:
    if witness is None:
        # Complete NO_BOUNDED_UNLOCK, not a KNOTTED verdict.
        pass
```

Use `region_mode="support"` for the alternative complete full-support search
with bound `7*k+6`; the default uses connected cores with bound `3*k+2`.
Both use full footprints for commutation and retain all ambient pairings.

A `None` cap disables that cap; a zero cap allows zero trials or regions.
Caps interrupt with `SearchExhausted`. An initially legal reduction needs no
search and can be returned immediately. The crossing-free diagram has no
crossing-decreasing move: the outer recognizer, not this local query, handles
its unknot verdict.

## Reproduce the research runs

```sh
export PYTHONPATH=src
python src/audit.py
python src/benchmark.py --rounds 5
sh run_checks.sh
sh build.sh
```

The audit and benchmark scripts overwrite their JSON outputs with the new run.
Wall-clock values will vary. `run_checks.sh` runs unit tests and replays all
shipped witnesses; it does not rerun benchmarks. `build.sh` needs `pdflatex`
and standard LaTeX packages and writes its temporary files to `.build/`.
The `.tex` article embeds its bibliography and tables, requiring no network.

## Completed validation

27 unit tests pass. Exhaustive Boolean comparisons cover 3,303 guarded-toggle
systems, all eight initial states, and birth bounds one through three at depth
four: 79,272 comparisons, with zero discrepancies. An independent convolution
checks 651 forest coefficients.

The actual-diagram audit attempts 1,200 seeded random braids, obtains 248 valid
knot closures, checks 821 local actions, 543 disjoint pairs, 180 bounded endpoint
comparisons, and 1,000 nonempty terminal cones. The latter include initial core
connectivity and the initial-star identity. All recorded checks pass. These
finite checks are not substitutes for the proofs or for an independent topology
implementation. The verifier shares the dart kernel but not the search code.

## Performance result, including the negative finding

The paired experiment exhausts trace prefixes, comparing a PURE-STATE
reimplementation of the prior birth-front normal form with the layered kernel.
It is NOT a benchmark of the production mutable engine or complete recognition.

The measured genuine-diagram cases have paired baseline/new ratios between
0.896 and 0.980: no wall-clock improvement is established on those knot kernels.
Some trace counts decrease by about 19--21%, but layer construction overhead
removes that benefit. The abstract six-bit depth-eight case improves by 2.261x.
That abstract ratio is not a knot-recognition speedup. No default switch is
recommended, and the connected-core region mode has not had a large end-to-end
performance study.

## Integration and source scope

Source reads were made through the GitHub connector; a complete checkout was
not available in the execution environment. Selected production operations
were adapted into an independently packaged reference module. These are not
byte-identical copies of the full production files. The adapter was locally
tested against compatible mutable objects; the full ProveIt regression suite
was NOT run with it. The online repository has not been changed.

Suggested destination for review is a new self-contained directory such as
`Topology/UnknotRecognition/proposals/causal_kernels/`; let the maintainer assign
any numbered report destination. Preserve the opt-in status until actual
production replay, budget, regression, and performance checks have completed.
