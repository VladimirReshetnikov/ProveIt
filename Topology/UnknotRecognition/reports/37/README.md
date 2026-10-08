# Closure-aware cut certificates and first-hit factorization

A research contribution for `VladimirReshetnikov/ProveIt`, prepared 8 October 2026.

**Read the article:** [`article/article.pdf`](article/article.pdf) (27 pages).
The complete LaTeX source, bibliography, exact reference implementation, tests,
raw measurements, and six replayable small-braid certificates are included.

## Results

For an exact typed acyclic transfer graph, split every source–target path at its
**first** visit to a vertex cut. This gives `D = B A` for arbitrary cuts, including
non-antichain cuts. After a verified fixed closure, the sum of closed dimensions
at the cut bounds `rank(D)`. A rank-only computation can work through these factors
without constructing the full endpoint matrix.

Given closed critical dimensions `c[h,j]` and differential rank upper bounds
`cap[h,j]`, maximize `sum(r)` subject to

```
0 <= r[h,j] <= cap[h,j]
r[h-1,j] + r[h,j] <= c[h,j].
```

The left-to-right greedy algorithm in the article is optimal. Therefore
`beta_cut = sum(c) - 2*max(sum(r))` is the strongest homology lower bound implied
by just these numerical data. For a certified reduced knot complex, `beta_cut > 1`
rejects the unknot without evaluating the remaining transferred maps. Otherwise
`sum(c) <= 2*max(sum(r)) + 1`, bounding the unresolved terminal dimension.

These are proved algebraic results, not a proof of general quasi-polynomial
recognition. In particular, the affordable construction of a suitable state and a
production cobordism-closure adapter are not supplied here. The conditional
complexity theorem charges those costs explicitly.

## Executed validation

- **36 unit tests passed**, including exhaustive small cuts, noncommuting typed
  matrices, square-zero dot coefficients, 500 brute-force rank-budget comparisons,
  mutation rejection, and a test proving that cut-only rejection skips transfer.
- **80 small braid diagrams**, **160 matching configurations**, and **1,070
  transferred maps** agreed with direct reduced binary Khovanov homology.
  These are diagrams, not 80 distinct knot types or a hard-knot corpus.
- **48 cut-only rejections**: all 24 nontrivial diagrams in both matching
  configurations. Earlier cube construction was still performed.
- **Six braid certificates verified** by an optimizer-independent dense-transfer
  replay. The producer and verifier share the cube constructor and binary-rank
  primitive; this is not a formally verified or independently implemented topology
  oracle.

Seven shuffled paired timing rounds include an identical forward/control arm.
The complete cut-factor rank stage includes minimum-cut discovery and verification.
It is **2.41–4.29 times slower** than forward on the three small actual knot stages
measured, but **4.80 times faster** on the largest constructed shared-bottleneck
complex. That synthetic case reduces propagation compositions from **790,912 to
12,421**. No classical-knot realization of the synthetic family is proved.

**No production `fastunknot` benchmark or upstream test suite was run.**
No repository commit or default-reducer change is included.

## Run

Python 3.10 or later is sufficient for the source syntax; the delivered run used
Python 3.13.5. No third-party Python packages are required. From this directory:

```sh
PYTHONPATH=code python -m unittest discover -s tests -v
PYTHONPATH=code python code/run_experiments.py
PYTHONPATH=code python -m separator_transfer verify examples/figure_eight.json
```

In PowerShell, set `$env:PYTHONPATH = "code"` and omit `PYTHONPATH=code` from the
subsequent commands.

Generate a new small-input certificate:

```sh
PYTHONPATH=code python -m separator_transfer braid \
  --strands 3 --word '[1,-2,1,-2]' \
  --certificate examples/my_figure_eight.json
```

The braid utility constructs the **full exponential reference cube**, with a
default eleven-crossing cap. It is not a replacement for the maintained scanner.
Resource-limit errors are not knot verdicts.

To regenerate tables after rerunning the timing driver:

```sh
python code/make_tables.py
./build.sh
```

`build.sh` needs pdfLaTeX and standard mathematical LaTeX packages. It uses BibTeX
when available; a generated `article.bbl` is included for environments lacking
BibTeX. `references.bib` remains the bibliography source. Timings in the shipped
PDF are frozen to the delivered run; rerunning changes local timings.

Before modifying any file, verify the archive manifest:

```sh
python code/check_manifest.py
```

## Integration and provenance

Suggested destination:
`Topology/UnknotRecognition/reports/closure_cut_transfer/`.
Use an available new directory name; no numeric report slot is presumed free.
See [`INTEGRATION.md`](INTEGRATION.md) for the typed graph, closure, grading,
transactional resource, and test obligations before production promotion.

The reviewed repository reference is
`bc5b913850f78155ccfddd808d4b11517dca252d`. Exact reviewed-source identifiers,
limitations, and environment information are recorded in `PROVENANCE.json`.
The package includes no third-party papers, copied production code, or font files.
Original package material is supplied under MIT-0; external cited works retain
their own licenses.
