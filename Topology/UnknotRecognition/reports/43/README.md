# Beyond Length Descent: Certified Whitehead Exposure

Research continuation for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.
Audited source commit: `04d799b69d388f75ce85539b26fca1585f9d2651`.

**Read `article/whitehead_exposure.pdf` for the theorems, proofs, experiments,
limitations, and eight further research directions.** Its adjacent TeX is
self-contained and rebuildable. This contribution is opt-in; no production
files or defaults are modified.

## Main results

A cyclic relation admits a one-Whitehead multiplier singleton exactly when
its weighted Whitehead graph has a capacity-one support bridge. Contracting
all other local edges turns complete exposure selection into pinned minimum
cuts. The same cuts minimize the exact raw allocation bound

`U = L - degree(a) + (target_length - target_degree(a)) * (total_cut - 2)`

for the ensuing Tietze elimination. This is not a claim to minimize the final
length after cancellations. Ordinary Whitehead minimum-cut optimization is
classical and already present upstream; the contribution is the constrained
objective and its complete implementation.

The explicit family `<a,b | u, v^m>`, with `u=a^2 b a b` and
`v=cycred([u,(a b^-1)^3])`, presents Z but defeats strict Whitehead descent.
For `m>=2`, every non-inner elementary Whitehead move increases total length.
One exposure and one elimination nevertheless finish. The least one-step
exposing increase is `2m-2`. Relator-overlap moves are excluded from this
barrier statement, so it does not establish a failure of the upstream pipeline.

For `m=2^k`, graph selection and fused quotient replay take polynomial bit
time in k on a grammar with k+51 nodes. The supplied experiment reaches
k=4096 with a literal image cap of 100, without expanding the relators.
These are algebraic presentations, not exponentially large knot diagrams.

The explicit rank-first stage has at most r-1 rank drops. A quasipolynomial
stored-letter cap gives a quasipolynomial-bounded **possibly inconclusive
positive search**, not a complete general quasipolynomial unknot recognizer.

## Run locally

Python 3.10+; standard library only. Tested here on CPython 3.13.5.
From this directory:

```sh
PYTHONPATH=src python -m unittest discover -s tests -v
python experiments/audit.py
python experiments/benchmark.py
python experiments/replay_supplied.py
python experiments/gordian_residual.py
PYTHONPATH=src python -m whitehead_exposure compressed-barrier --bits 1000
PYTHONPATH=src python -m whitehead_exposure braid --strands 3 --word=1,-2
sh article/build.sh
```

The last command needs a normal LaTeX installation with pdflatex, AMS packages,
lmodern, microtype, booktabs, enumitem, listings, TikZ, hyperref, and fancyhdr.
The shell syntax shown is POSIX; on Windows set `PYTHONPATH` to `src` using
the shell's environment-variable syntax, or install this package normally.

For an explicit presentation, use a JSON object with `alive` (distinct positive
generator names) and `words` (lists of signed integers). Every input word must
already be freely and cyclically reduced. Empty relation slots are allowed.

```sh
PYTHONPATH=src python -m whitehead_exposure presentation input.json
```

`FREE_RANK_ONE` is an algebraic result. `UNKNOT` is emitted only by a validated
classical topological frontend with a replayed input-bound certificate.
`INCONCLUSIVE` never means knotted. Malformed evidence is rejected; resource
exhaustion and external cancellation are not silently converted into proofs.

## Completed validation and measured scope

- 49 unit tests passed.
- 17,664 exhaustive occurrence/length checks on 1,104 cyclic words; all 1,104
  bridge-existence decisions matched exhaustive exposure search.
- 640 allocation/length selector comparisons against literal enumeration,
  468 returned witnesses checked, 500 independent flow comparisons, and 500
  tampered-flow capacity records rejected.
- Both isolated policies accepted 40 constructed unknot braid closures and
  accepted none of 20 nontrivial controls. **No exposure was needed on the
  positive braid corpus; there was no demonstrated coverage or speed gain.**
- Both policies stalled on the source-derived 141-crossing Gordian fixture.
  Rank-first exposed once, then reached rank 11 with 97,684 letters and no
  remaining unit bridges. The exact residual and provenance are supplied.
- The constrained cut selector beat explicit characteristic-shore enumeration
  by approximately 1.01x to 279.77x in the small paired component experiment.
  That comparison is NOT against the maintained minimum-cut producer and is
  NOT an end-to-end recognizer speedup.

Raw timings, seeds, traces, and metadata are in `data/`; rerunning measurements
will change times. The printed article records the shipped run.

## Layout and integration

`src/whitehead_exposure/` contains the implementation and separate replay code.
`tests/` and `experiments/` contain runnable checks and reproducible workloads.
`certificates/` contains two algebraic certificates and one native braid
certificate. `integration/` contains an opt-in upstream adapter and a fail-loud
smoke script. `INTEGRATION.md` describes the exact interface and outstanding
checks; `SOURCE_AUDIT.md` records source provenance.

The adapter was source-audited but **not run against a complete upstream
checkout** here. No full upstream suite or complete-maintained-recognizer
benchmark is claimed. The native braid frontend and the source-derived PD
experiment do not substitute for that integration run.
