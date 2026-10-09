# Native compressed braid certificates

Research continuation for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

**Article:** [paper/article.pdf](paper/article.pdf).  
**Complete, self-contained LaTeX source:** [paper/article.tex](paper/article.tex).

This package implements exact recognition directly on a binary straight-line
program (SLP) for a three-braid, together with independently structured certificate
replay. It also preserves compressed factors under singleton-generator
connected-sum decomposition on arbitrary strand counts.

## Results and exact scope

For `s` nonempty input rules and `B` bits of represented-length metadata, the
three-braid producer allocates `O(s²(B+1))` string rules and uses `O(s(B+1))`
exact string-equality queries. Since `B = O(s+1)`, the uncapped algorithm is
polynomial in the actual compressed input size. The allocation estimate is
**not** a cubic running-time claim: the exact equality primitive has its own
polynomial cost. Replay checks the source-bound certificate without running
the producer or any longest-common-prefix search.

The arbitrary-strand forest is complete when every singleton-separated leaf
has at most three strands. A knotted supported leaf, or a wider leaf violating
its local Bennequin bound, certifies nontriviality. Unsupported wider leaves
remain `INCONCLUSIVE`; they are never discarded as unknots.

The article proves a stronger hybrid bound with a complete exact fallback:

`poly(g) + sum_{i in E} 2^O(kappa_i)`.

Here `g` is input bit size, `E` contains only unresolved wider leaves, and
`kappa_i` is their minority-sign count. Every solved compressed three-braid is
excluded from the exponential term, even when it represents exponentially many
crossings. A quasi-polynomial bound follows when the largest exceptional count
is `O(log² g)`. The full fallback composition is proved, but **not wired into
this research package**. A uniform efficient reduction of arbitrary knot
diagrams to this favorable regime is not established.

The article also proves that full ordinary Burau matrices can require
exponentially many bits on compact three-braid conjugate inputs with constant
trace. This is a matrix-materialization obstruction, not a lower bound against
all matrix circuits or modular algorithms.

## What is inherited

The project already decides explicit three-braid closures in linear time.
Polynomial compressed conjugacy in fixed hyperbolic groups, exact SLP equality,
singleton connected-sum topology, and the explicit local minority estimate are
prior results. This package supplies a direct certificate-oriented compressed
specialization and its decomposition/accounting extension; it does not claim
priority for the general compressed conjugacy theorem.

`compressed_b3/strings.py` is an attributed source-derived adaptation of the
project's exact string kernel, not an actual imported upstream checkout. Replay
is independent of producer reduction and prefix discovery, but shares the exact
string primitives and imported topology. No proof-assistant verification is
claimed. See [CLAIMS.md](CLAIMS.md) and [provenance/SOURCES.md](provenance/SOURCES.md).

## Run from the extracted directory

All algorithm and test code uses the Python standard library. The recorded
execution used CPython 3.13.5 on Linux x86-64. No installation is necessary:

```sh
python -m unittest discover -s tests -v
python -m compressed_b3 recognize examples/sleeve_256.json
python -m compressed_b3 verify examples/sleeve_256.json \
  --certificate examples/sleeve_256.result.json
python -m compressed_b3 forest examples/singleton_forest_12.json
python -m compressed_b3 verify-forest examples/singleton_forest_12.json \
  --certificate examples/singleton_forest_12.result.json
```

The input is a validated grammar, not an expanded braid list or a general
fundamental-group presentation. The three-braid API requires exactly three
strands; the forest API supports arbitrary strand counts.

```python
from compressed_b3 import Builder, recognize, verify

builder = Builder()
source = builder.data(builder.word([1, 2]))
result = recognize(source)
assert verify(source, result["certificate"]) == result["status"]
```

The CLI independently replays before publishing. The library producer returns
a certificate; callers should replay it before using the result as trusted
evidence. Resource exceptions must remain inconclusive. The CLI has finite
node/work limits; mathematical completeness refers to the uncapped procedure,
or increasing allowances until discovery and replay both complete. Budgets are
cooperative and per arena, not hard wall-clock or service-level limits.

## Completed validation and measurements

The final saved local suite has **42 passing unittest methods**. The separate
exhaustive audit checks **87,381 words through length eight**, including 46,376
one-component closures, against the source-derived explicit stack and a
separately coded exact Burau control, with certificate replay and zero
mismatches. These are word instances, not distinct knot types. The audit also
checks **400 random shared grammars** and forced-fallback quotient reductions
on those same 400 cases.

Expansion-forbidden capacity tests include an unknot word with
`4 * 2^4096 + 2` represented letters, 8,201 nonempty input rules, 8,205 producer
string rules, and a 349,628-byte compact JSON certificate. A 96-strand native
forest with 32 compressed three-braid leaves also completes with replay.
Negative sleeves and an unsupported four-strand example test knottedness and
honest nondecision.

The paired local benchmark uses the **same native grammar input** on both
sides. The new side includes discovery and independent replay; the baseline
expands and uses a source-derived explicit three-braid stack. At 1,048,578
represented crossings the seven-round medians were 0.880 ms and 599.129 ms.
Tiny inputs instead favor expansion. This structured positive sleeve family
favors grammar sharing; negative and reassociated controls expose higher costs.
**These are not production-pipeline speedups, hard-knot corpus results, or
sublinear reading of explicit diagrams.** Raw samples, timing inclusions, seeds,
capacity limits, and an exploratory stopped-sweep disclosure are in `results/`.

## Reproduction and article build

```sh
python experiments/verify_manifest.py
sh reproduce.sh
```

`reproduce.sh` reruns the unit suite, exhaustive audit, paired benchmark, example
generation, table generation, and LaTeX build. It needs `pdflatex` with the
standard packages named in the preamble. The bibliography is embedded; no
BibTeX or network access is needed. To rebuild only the article:

```sh
sh paper/build.sh
```

Reproduction changes timings, possibly the PDF, and therefore checksums. Keep
the original ZIP for comparison. `SHA256SUMS` covers delivered files other than
the manifest itself; `experiments/verify_manifest.py` checks their contents.

## Integration status

The inspected project reference is
`47002f64b9a97f64edc8e8b8f793b83983b719f9`.
No remote repository files were changed. Suggested additive location:
`Topology/UnknotRecognition/research/compressed-braid-certificates/`.

The full upstream checkout/regression suite, actual injected upstream
`WordArena`, Rust port, and whole-production benchmark were **not run**.
`integration/upstream_check.py` is an opt-in real-checkout compatibility check,
not a recorded successful integration result. Keep the current explicit route
as default and promote the compressed route only after the checks in
[INTEGRATION.md](INTEGRATION.md). Production integration of exceptional fallbacks
must preserve exact source projections, child certificates, and global budgets.

## Package map

`compressed_b3/` contains the grammar semantics, exact string layer, discovery,
replay, singleton forest, and CLI. `tests/` contains unit tests.
`experiments/` contains independent controls, generators, reproducible audits,
benchmarks, table generation, and manifest checking. `results/` contains completed
run records; `examples/` contains inputs and replayable certificates.
`paper/` contains the article and build script. `provenance/` records inspected
sources and imported mathematics. [RESEARCH_QUESTIONS.md](RESEARCH_QUESTIONS.md)
collects the article's thirteen next research problems.

All supplied material is under MIT-0, with explicit source attribution retained.
No third-party manuscript PDFs or font files are redistributed.
