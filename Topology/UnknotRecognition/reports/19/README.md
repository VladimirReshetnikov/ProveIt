# Optimal rank-two braid kernels and survivor growth

A research contribution for `ProveIt/Topology/UnknotRecognition`, 7 October 2026.

The article is **`paper/article.pdf`**, with its complete source in
**`paper/article.tex`**. The implementation is standard-library Python.

## What is proved and implemented

For an explicit braid word of length `n` on `s` strands, one pass chooses an
**optimal set of disjoint two-index subwords** to replace by an equal empty
word or single Artin letter. Adjacent indices use an exact, noncyclic `B3`
prefix representation; distant indices use two exponent counts. This is
context-safe braid equality, not equality of closed knots.

The deterministic AVL implementation takes `O(n log(n+2))` word-RAM time and
`O(n)` words of memory. Conservative bit time is `O(n log²(n+s+2))`.
The optional hash backend has expected, not deterministic, linear dictionary
work. Repeated passes have a conservative quadratic total bound.

The separate verifier uses a central normal form and stable live-node IDs.
Across all passes its transcript removes at most `3n/2` nodes and introduces
at most `n/2`, so verification is linear in word-RAM operations.

The article proves a quasi-polynomial recognition bound for **flat rank-two
inflations of `O(log² n)`-crossing cores**, without receiving the decomposition.
It also proves an exponential lower bound on explicit matching summands at
constant boundary width, and an infinite family of unknot words that cannot
be shortened by *any* strictly shortening rank-two substitution.

**This is not a universal quasi-polynomial unknot algorithm.** “Optimal” means
optimal among the explicitly defined disjoint replacements in one pass, not
a shortest braid or a globally optimal sequence of Markov moves.

## Quick start without installation

From this directory:

```sh
export PYTHONPATH="$PWD/src${PYTHONPATH:+:$PYTHONPATH}"
python -m unittest discover -s tests -v
python -m ranktwo compress examples/sleeved_unknot_4_16.json \
  --passes 1 --output results/example_compressed.json
python -m ranktwo verify examples/sleeved_unknot_4_16.json \
  results/example_compressed.json
```

The first example has 155 letters and compresses to `[1, 2, 3]`. The CLI
replays the certificate before publishing its output. Omitting `--passes`
saturates under the selected rule radius. `--radius 0` allows only identity
deletions; the default radius 1 also allows one-letter targets.

Python API:

```python
from ranktwo import compress, verify

result = compress(4, word, radius=1, max_passes=1, dictionary="avl")
reduced, replay = verify(4, word, result["certificate"])
```

A guarded reference recognizer is available as
`ranktwo.reference.recognize_reference`. It is restricted to knot closures.
It uses a signed-Coxeter certificate when applicable and otherwise an
**exponential expanded reduced Khovanov cube**, capped by default at 12
crossings and 100,000 basis vectors. Resource exhaustion returns
`INCONCLUSIVE`. Setting both cube caps to `None` gives the uncapped
exponential reference backend; it is not intended to replace the production
scanner. The default CLI is a compressor/verifier, not a general recognizer.

## Completed checks and data

`results/` records completed runs on CPython 3.13.5, x86-64 Linux:

- 33 unit tests passed, including three adapter contract tests using a fake
  gateway, **not the real upstream implementation**.
- 87,381 three-braid words of length at most eight were cross-checked using
  the persistent quotient/exponent, central normal form, and matrix/exponent.
- 62,352 optimization instances matched exhaustive interval enumeration;
  both dictionaries ran on every instance, for 124,704 optimized runs.
- 1,000 random Artin-action comparisons and 100 small Khovanov-invariance
  comparisons passed. Both cubes in each homology comparison checked `d²=0`.

The 32,795-letter four-strand sleeve example compressed to three letters in
0.759 seconds with AVL and replayed in 0.040 seconds (three-run medians on
this environment). Timing is not a portable performance guarantee.
The paired speed ratios in the article are against our slow independent
interval oracle, **not against the full `fastunknot` recognizer**.

Run `sh reproduce.sh` to regenerate the checks and benchmarks. Raw timing
samples, seeds, exact operation counts, and environment metadata are included.

## Integration status

The inspected repository commit is
`0090314cfcc21e1f28ecbc6e8ce4d3f2d99ee743`.
Its existing closed-three-braid gateway is not a new contribution here.
`integration/fastunknot_adapter.py` supplies an opt-in raw-braid wrapper.
`integration/upstream_check.py` is a real-checkout smoke test that **was not
run in the artifact-building environment**. The full upstream suite and Rust
port were not run or modified. No repository writes were performed.

See `INTEGRATION.md` for the intended insertion point, certificate propagation,
and required production checks. `CLAIMS.md` is the explicit status ledger.

## Article build

```sh
cd paper
sh build.sh
```

Requires `pdflatex` and the packages in the TeX preamble. The bibliography is
embedded in the TeX file; no BibTeX database or network access is required.
The delivered PDF was compiled, rendered, and visually inspected.

## Layout

`src/ranktwo/` contains preprocessing, independent verification, exact test
oracles, family generators, and the guarded reference cube. `tests/` contains
the unit suite. `experiments/` contains deterministic sweeps and benchmarks.
`examples/` contains positive and negative examples with replayable results.
`provenance/` records the inspected snapshot and outside mathematical sources.
`paper/` contains the article and build script. `SHA256SUMS` covers the package
files at release; reproduction changes timing/result files and therefore
changes their checksums.

All newly supplied material is under MIT-0. No third-party manuscript PDFs,
font files, or upstream source snapshots are redistributed in this package.
No proof-assistant verification or universal asymptotic breakthrough is claimed.
