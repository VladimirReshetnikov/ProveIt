# Polynomial raw epochs for exact unknot recognition

**Research continuation dated 8 October 2026.** This bundle contains the 23-page
article *Saturated-Lattice Bounds and Source-Anchored Primitive Projections:
Polynomial Raw Epochs in Exact Unknot Recognition*, its LaTeX source, a standalone
exact Python kernel, independent arithmetic replay, tests, completed audits,
paired maintenance measurements, and integration notes.

## Main result

Freeze an initial presentation with `r` generators, fixed relator slots, and a
binary word circuit. During a raw epoch, allow only verified primitive-pair
quotients (including disjoint batches and unit-coordinate forest batches),
retaining each unselected source slot. If a block has `t` original generators
and the maximum initial relator length is `L`, its cumulative monomial exponents
satisfy

    |k_i| <= (t-1)^((t-1)/2) L^(t-1)    (t >= 2),
    |k_i| = 1                          (t = 1).

Thus the exponent bit length is `O(r (B + log(r+1)))` throughout the epoch, not
exponential in the number of raw phases. The proof uses the saturated integer
kernel of selected **original** exponent-sum rows. A separate reachable-node
argument gives polynomial total raw-epoch cost for the existing updater too.
The old exponential recurrences were loose upper bounds, not established lower
bounds contradicted by these experiments.

The new source-anchored implementation reduces representation maintenance by
evaluating on one immutable source circuit and updating a monomial image table.
It does **not** establish general quasi-polynomial unknot recognition. Exposure,
normalization, new-source size, search completeness, and the number of source
resets remain separate obligations.

## Safety and scope

This is an **algebraic research kernel, not a knot-verdict API**. Its source is a
presentation circuit, not a validated planar diagram or a complete verified
presentation prefix. For a proper-power donor, `replay` explicitly reports
`needs_torsion_freeness=True`; source-established torsion-freeness must be supplied
by the existing topological host before concluding group preservation. There
is no caller flag that turns an arbitrary presentation into an unknot proof.

The main theorem covers forests; the delivered v1 producer and verifier expose
**disjoint pair batches only**. A direct source-anchored forest API is proposed,
not implemented. The native adapter is a protocol seam, not a completed native
integration. No repository files, defaults, or existing certificate versions
were changed.

See `CLAIMS.md` and `integration/REVIEW.md` before integration.

## Reproduce

Python 3.10+ syntax; executed here with CPython 3.13.5 on Linux x86-64.
Only the Python standard library is needed. From this directory:

```sh
PYTHONPATH=src python -B -m unittest discover -s tests -v
python -B experiments/audit.py --output data/audit-rerun.json
python -B experiments/benchmark.py --output data/benchmark-rerun.json --rounds 5
python -B experiments/demo.py
python -B experiments/make_tables.py
```

On PowerShell, set `$env:PYTHONPATH = "src"` before the unit-test command. The
experiment scripts add the local `src` directory to their import path themselves.
No package installation is necessary. An optional `pyproject.toml` is supplied.
Write reruns to new files to preserve the recorded historical measurements.

Rebuild the article with a standard LaTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The bibliography is embedded in `article.tex`; no BibTeX run is needed. The three
generated table files under `data/` must accompany the TeX source. `build.sh`
runs three passes for stable references.

## Completed validation

The final unit suite has **38 passing tests** (`data/unit-tests.txt`, 0.651 s).
The completed exact audit (`data/audit.json`, seed 2026100801, 13.353 s) includes:

- 600 signed-tree presentations and 3,393 checked prefixes;
- 26,037 exact raw-root word comparisons using run-length lists;
- 8,166 binary positive words / 32,664 signed profile cases;
- 2,728 independent replays and 324 additional nonunit primitive fixtures;
- a cumulative exponent with 64,513 bits, without expanding the represented word.

The last capacity case uses only the new producer and independent source replay;
it is not a completed comparison with the chained updater. An earlier larger
chained audit exceeded its process cap; `data/exploratory-timeout.txt` records
that limitation explicitly.

## What the benchmark measures

`data/benchmark.json` contains all samples of a five-arm randomized paired test:
lazy source maintenance, its A/A control, the copied upstream updater, its A/A
control, and source maintenance with eager circuit export after every batch.
It has 175 measured calls and 35 warm-ups, all completed.

**The timed workload is maintenance of a supplied preverified schedule**, including
initialization and the rank-one exponent endpoint. It excludes schedule discovery
and independent replay. The copied updater runs on the standalone compatible
`Arena`, not the complete native implementation. All families are abstract
presentations, not knot diagrams.

The retained paired chained/lazy ratios are 3.44–4.49 on stars and 22.41–53.23
on chains. These are not whole-recognizer speedups. A/A ratios show appreciable
noise, particularly in the small cases. Eager export is slower than chained
maintenance in every measured case; preserving laziness across an epoch is
necessary for the proposed implementation benefit.

## Contents

- `article.tex`, `article.pdf`: full proofs, scope, results, and 12 research questions.
- `src/anchored_unknot/grammar.py`: exact binary circuits and frozen source validation.
- `kernel.py`: source-anchored producer and monomial updates.
- `verify.py`: independent strict source-bound arithmetic replay.
- `linear_audit.py`: independent integer/rational kernel and cofactor checks.
- `reference_update.py`: attributed verbatim upstream raw updater plus audit adapters.
- `native_adapter.py`: snapshot/export seam for later native integration.
- `fixtures.py`, `tests/`, `experiments/`: reproducible exact fixtures and experiments.
- `data/`: completed raw measurements, logs, generated tables, and a small demo proof.
- `integration/`: review instructions and a source-blob/AST comparison helper.
- `PROVENANCE.json`, `SHA256SUMS`: source provenance and artifact integrity.

The source pin is commit `7518823550fbc8c217bc8be0113fe52002e77465` of
`VladimirReshetnikov/ProveIt`. The complete native test suite and Rust port were
**not run**. The integration hash helper is supplied but was not executed against
a full native checkout. Upstream test-count reports are not this bundle's results.

The new code and reproduced MIT-0 fragment are supplied under MIT-0. Third-party
papers and font files are not redistributed.
