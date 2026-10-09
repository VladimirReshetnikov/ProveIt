# Certified sparse component incidence

**From Dense Port Tables to Polynomial Sparse Incidence**  
Research contribution for `VladimirReshetnikov/ProveIt`, 8 October 2026.

The article is `paper/article.pdf` (25 pages); its editable source is
`paper/article.tex`, with bibliography and generated tables in the same directory.

This package computes the complete sparse histogram of component/port signatures
for a supplied binary-encoded interval relation. It removes the `2^r` dense table
from this observer. It is **not an unknot recognizer**, and it does not construct
or certify the geometric provenance of a knot exterior or a complete hierarchy.

## Mathematical result

With `s` nonempty signatures on `r` ports, positive sparse-zeta extraction takes
`O(sr)` oracle queries. Balanced block deletion improves the support-sensitive
bound to `O(1+s+sum_T |T| log(1+r/|T|))`. A sparse answer is independently certified
using its immediate-subset equations and total mass, rather than a dense forward
transform. Binary orientation-character covers preserve signature support, so
cover multiplicities can be recovered without a second support search.

For interval-union ports, polynomial support size follows from the classical
**weighted Agol–Hass–Thurston theorem**. Combining that fact with the reduction
proves polynomial bit complexity for the supplied incidence query. This is an
unweighted-query, independently replayable realization of a classical weighted
orbit consequence, not a new general theorem that weighted orbits are polynomial.
No first-in-literature priority claim is made for sparse query learning.

## Run locally

Python 3.10+ is intended; the recorded run used CPython 3.13.5. No third-party
Python packages or network connection are needed.

```sh
export PYTHONPATH="$PWD/src${PYTHONPATH:+:$PYTHONPATH}"
python -m unittest discover -s tests -v
python experiments/validate.py
python experiments/benchmark.py --rounds 7
python experiments/make_tables.py
python -m sparse_incidence analyze examples/mixed.json \
  --output results/mixed.json --certificate
python -m sparse_incidence verify examples/mixed.json results/mixed.json
cd paper && sh build.sh
```

LaTeX rebuilding needs the packages in the preamble and `bibtex` or `bibtex8`.
The supplied `.bbl` is retained for convenient direct PDF rebuilding. Running
the full build script regenerates it from `references.bib`.

## Input and output

Pairings are **inclusive** rows `[a,b,c,d,sign]`, with equal widths and
`sign` either `1` (translation) or `-1` (reflection). Ports are lists of
**half-open** intervals `[lo,hi)`. Ports may overlap, coincide, or be empty.

```python
from sparse_incidence.api import analyze
from sparse_incidence.verify import verify

size = 10
pairs = [[0, 4, 5, 9, 1]]
ports = [[(0, 2)], [(6, 9)], [(0, 1), (9, 10)]]
result = analyze(size, pairs, ports, record_certificate=True)
assert result["status"] == "COMPLETE"
assert verify(size, pairs, ports, result["certificate"])
# histogram: [[2,2], [4,1], [3,1], [5,1]]
# Bit 0 means port 1; masks are sorted by cardinality, then numerical value.
```

An absent sparse row means zero. Mask zero is retained when unmarked components
have positive multiplicity. `COMPLETE` refers only to the incidence query.
`max_cycles`, `max_queries`, and `max_entries` are optional allowances.
Exhaustion returns `INCONCLUSIVE`, no histogram, and no certificate; baseline,
discovery, and additional proof queries share the allowances. Callbacks provide
cooperative cancellation, and callback exceptions propagate.

For typed incidence, `sparse_incidence.signed.analyze_signed` accepts rows
`[a,b,c,d,sign,parity]` and returns `[mask,consistent,inconsistent]`. **Parity is
not interval order reversal.** Interpret consistency as orientability only when
the supplied bits have the required geometric provenance.

## Validation and measured scope

The delivered suite passed **33 tests**, including all **6,561** three-port
histograms with weights 0, 1, or 2, both recovery strategies, malformed proof
mutations, callback behavior, budget sharing, and huge-integer transport.
The separate audit completed **1,000 interval-graph comparisons and 1,000
binary-character comparisons**, including independent proof replay.

The nine paired benchmark workloads use the same unchanged upstream AHT kernel
in **classical** periodic-merger mode for every arm. The dense arm is a controlled
research ablation, not the full production observer or recognizer. Seven measured
rounds and one warmup use shuffled order and a dense A/A control. Disjoint sparse
families show substantial gains; several small/dense cases have overhead.
See the article and `results/benchmark.json` for every sample and exact scope.
No native normal-surface, Regina, full upstream suite, or whole-knot timing was
performed in this delivery. An exploratory 32-block benchmark was stopped before
completion and is excluded from the delivered measurements; the completed
benchmark uses the named 16-block workload.

## Integration

The archive is additive: no repository commit or production source modification
was performed. A proposed destination is
`Topology/UnknotRecognition/research/sparse_incidence_20261008/`.
Read `INTEGRATION.md` before introducing a production caller. In particular,
incidence equality is **not** sufficient for arbitrary future attachments:
the four-point counterexample is both proved and tested.

`PROVENANCE.json`, `vendor/README.md`, `CLAIMS.md`, and `SHA256SUMS` identify the
sources, licensing boundary, claims, and delivered file integrity.
