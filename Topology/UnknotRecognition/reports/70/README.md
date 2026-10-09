# Interval-weighted affine orbit profiles and sparse attachment replay

Research delivery for ProveIt, 9 October 2026. The article is in
`article/article.pdf` (25 pages), with its complete LaTeX source and generated
tables alongside it. This package does not modify the maintained recognizer.

## Main results

For an explicitly represented base graph with binary-sized uniform fibres and
full-fibre maps `x -> ±x+a (mod W)`, assign `K` signed vector interval weights.
For one connected base block, the complete orbit-weight histogram has at most
**2K+3 distinct entries**, with binary multiplicities. This bound is **sharp for
every K >= 1 even for nonnegative scalar weights**. For `b` base blocks and `h`
additional pointwise attachments with additive payloads, the bound becomes
**2K+3b+h**. Exact coordinates are retained; histogram equality is never used to
identify distinct attachment positions.

A fixed-base insertion-only epoch has at most
`sum_i(floor(log2(d_i_initial)) + first_reflection_allowed_i)` effective subgroup
changes. Redundant maps require no profile rebuild. The implementation rebases
pointwise attachments from their original coordinates after a bulk change,
rather than using stale residue labels.

The package includes a full-fibre guard, a separate arithmetic certificate
checker, an explicit small-instance oracle, and source-bound reproducible tests.

## Scope

This is a supplied-model component-query kernel, **not an unknot recognizer**.
It does not extract a fibre model from a knot exterior, verify a surface's
embedding or boundary slope, compute all the existing native cover topology,
or prove a general quasi-polynomial recognition bound. Those are explicit
integration and research obligations in the article.

The general weighted orbit problem already has the polynomial
Agol–Hass–Thurston algorithm. Gcd monodromy classification also already appears
in the maintained ProveIt cover work. The contribution here is the sharp support
bound, sparse attachment interface, fixed-base amortization, and tested replay
implementation—not a claim to have discovered the general polynomial orbit
algorithm. Full comparison with the pending incoming ZIP contents remains an
intake task; their catalogue metadata, but not their full contents, was inspected.

## Run

Python 3.10 or newer; only the standard library is needed. Tested on CPython
3.13.5. From this directory on a POSIX shell:

```sh
export PYTHONPATH="$PWD/src"
python -m unittest discover -s tests -v
python scripts/audit.py
python scripts/benchmark.py
python -m affine_orbits examples/sharp-nine-profiles.json --output result.json
python -m affine_orbits examples/sharp-nine-profiles.json --verify result.json
```

On PowerShell, replace the `export` line with:

```powershell
$env:PYTHONPATH = "$PWD/src"
```

`python scripts/run_checks.py` also runs the unit suite, recorded finite audit,
and CLI replay without manually setting `PYTHONPATH`. Benchmarks are separate
because rerunning them changes the machine-specific raw data. After a new
benchmark run, `python scripts/make_tables.py` regenerates the article tables;
the prose measurements must also be reviewed before rebuilding the PDF.

Build the article with a standard TeX installation:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Python interface

```python
from affine_orbits import BulkIndex, SparseOverlay
from affine_orbits.certificate import make_certificate
from affine_orbits.checker import verify

model = {
    "vertices": 1, "sheets": 80, "dimension": 1,
    "edges": [{"u": 0, "v": 0, "sign": 1, "shift": 16},
              {"u": 0, "v": 0, "sign": -1, "shift": 0}],
    "weights": [{"v": 0, "start": 15, "stop": 69, "value": [1]},
                {"v": 0, "start": 14, "stop": 70, "value": [1]},
                {"v": 0, "start": 13, "stop": 71, "value": [1]}],
}
index = BulkIndex(model)
assert len(index.histogram) == 9  # the sharp 2K+3 example
point = index.representative((12,))
assert index.weight(*point) == (12,)
overlay = SparseOverlay(index)
overlay.add({"u": 0, "x": 0, "v": 0, "y": 1, "payload": [-1]})
certificate = make_certificate(index, overlay)
assert verify(model, overlay.defects, certificate)

changed = index.add_root_map(0, 1, 8)
if changed:
    overlay.rebase()  # otherwise queries deliberately reject stale labels
assert verify(index.snapshot(), overlay.defects,
              make_certificate(index, overlay))
```

The producer returns `Counter` objects keyed by integer tuples. Numeric JSON
fields accept actual integers or signed hexadecimal strings, not booleans or
decimal strings. CLI output uses hexadecimal integers and always has
`knot_verdict: null`. A CLI error exits with status 2 and is not a topology answer.
The deadline is cooperative, not a hard interrupt of each integer operation or
certificate-checking step. Explicit base vertices are allocated individually;
complexity is polynomial in their count, not in its logarithm alone.

## Completed validation

The final unit suite passes **34 tests**, including exhaustive inner loops and
30 sharp-support constructions. A separate **2,000-model** audit passes with
179,684 point-weight comparisons, 100,000 connectivity comparisons, 7,760
representative checks, and 2,000 independent certificate replays. The suite also
checks signed weights, reflection fixed residues, invalid guards, payloads on
loops and repeated attachments, cancellation, stale-state rejection, source
mutation, and `W = 2^24000`.

Recorded performance experiments compare this kernel with explicit expansion
or with explicitly specified fresh-rebuild strategies, **not** with a previous
maintained recognizer or AHT. The sparse and epoch median paired ratios were
about 17.6 and 9.65 in this run. Identical-arm controls span about 0.68–1.20;
these noisy controls prohibit interpreting the ratios as precise or universal
speed factors. Every raw sample is retained in `results/benchmarks.json`.

No native ProveIt suite or knot-corpus benchmark was run. The optional
`integration/check_native_cover.py` cross-check is included but unexecuted.

## Layout

- `article/`: full manuscript, PDF, and generated timing tables.
- `src/affine_orbits/`: producer, independent checker, guard, CLI.
- `tests/`: unit suite and finite expanded oracle.
- `scripts/`: audit, benchmarks, examples, table generation, check runner.
- `examples/`: exact inputs and checked certificates, including the sharp family.
- `results/`: completed raw tests, audit, timings, CLI replay, and build log.
- `integration/`: optional native comparison and an explicit NOT_RUN status.

`INTEGRATION.md`, `PROOF_AUDIT.md`, `SOURCE_AUDIT.md`, and `RESULTS.md` describe
acceptance criteria, proof boundaries, source-review limits, and experiments.
The MIT-0 license applies to the newly authored files. Third-party papers,
source archives, font files, and native repository code are not redistributed.
