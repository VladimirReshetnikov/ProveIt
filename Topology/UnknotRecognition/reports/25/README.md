# Support-unrestricted cyclic braid kernels

Research contribution for `ProveIt/Topology/UnknotRecognition`, 7 October 2026.
The main article is `docs/article.pdf`; its complete LaTeX/build sources are
beside it. No public repository files were modified.

## Results

The package implements exact, independently replayable braid compression.
It shares one doubled-word Garside prefix table across all cyclic cuts and
uses a second trie to share finite-target queries. For each fixed target
radius it optimizes disjoint one-pass substitutions in polynomial time.
The article includes explicit word/bit complexity and prefix-height bounds.

Two proved families identify important limits:

* In B4, with a=sigma_1, b=sigma_2, c=sigma_3,
  `W_m = a^(-m) c^m a^(m+1) c^(-(m-1)) b`, m>=2, is an unknot braid.
  Its radius-one cyclic kernel retains all 4m+1 letters; radius two retains
  exactly three. A cheaper whole-word normal-form shortcut also exposes
  the short braid, and the practical portfolio uses it first.
* In B3, `G_m = a^(m+1) b a^(-m)` is an unknot braid whose minimum equal-braid
  word length is exactly 2m+2. A cyclic cut reduces its radius-one kernel to
  two. This excludes a universal small-core argument preserving the original
  braid element. Existing free cyclic cleanup already handles this family.

The uncapped composition with a conventional exact Khovanov fallback is
quasi-polynomial when the certified kernel is O(log^2 n), including the
proved conjugated flat multi-letter inflation classes. **No universal
small-kernel theorem or general quasi-polynomial recognizer is claimed.**
The code here is preprocessing plus verification, not a complete recognizer.
Classical Garside theory and an existing repository DP are credited; global
historical novelty is not asserted.

## Quick start

Standard-library Python 3.10+; tested on CPython 3.13.5. Installation is not
needed when running from this directory.

```sh
python -m unittest discover -s tests -v
python -m cyclic_garside compress certificates/rectangle_m2.json --radius 2 -o result.json
python -m cyclic_garside verify certificates/rectangle_m2.json result.json
```

The CLI always replays a candidate before exporting it. A failed allowance
or invalid certificate is an error, never a knot verdict. The `--linear`
flag forbids a cyclic cut; `--all-rotations` disables only the *exact*
lower-bound early exit. JSON inputs are capped at 64 MiB by the CLI.

```python
from cyclic_garside import preprocess, compress, compress_radius
from cyclic_garside import verify, verify_radius

word = (-1, -1, 3, 3, 1, 1, 1, -3, 2)
result = compress_radius(4, word, radius=2)
assert verify_radius(4, word, result["certificate"]) == tuple(result["word"])

# Practical candidate portfolio: a verified whole-word normal-form candidate
# first, followed by an exact cyclic kernel only when necessary.
result = preprocess(4, word, radius=2)
# This result is NOT mislabeled as a radius-specific kernel optimum.
```

`compress` specializes radius one. `compress_radius` uses the finite target
trie (default radius two and maximum 100000 targets). `max_targets=None`
removes that local cap. The target dictionary is exponential in radius;
fixed-radius polynomial complexity does not mean arbitrary-radius polynomial
complexity. `Budget(max_ticks=...)` is an optional cooperative allowance,
not a wall-clock or process-memory guarantee.

## What is checked

The retained run passes **47 tests**. It includes 7,016 exhaustive short-word
normal-form comparisons with a faithful Artin-action oracle and 1,512
independent interval-optimizer comparisons. Additional tests cover all
872 simple permutations on 2--6 strands, random relations and inverses,
transfer counts, rotations, portfolio dominance, proof corruption, and
resource limits. These are not 7,016 distinct knots, and finite tests do not
replace the article's all-input proofs. Python semantics have not been
formally verified in Lean.

The complete upstream suite was **not** executed. `integration/` contains
an optional adapter and a clearly marked, unexecuted Diagram/provenance
smoke script. No Rust port, production integration, or complete-recognizer
speedup is claimed.

## Experiments

```sh
python scripts/benchmark.py --rounds 7
python scripts/radius_experiment.py
```

`data/benchmarks.json` retains seven shuffled paired rounds, with an A/A
control, comparing shared algebra against a fair reference that recomputes
prefix algebra at each cut. Both generate and replay only the winning
certificate. Imports are excluded. All-cut lower-bound pruning is disabled
in both arms. The six multi-crossing fixtures show about 4.3--20.6x median
paired compressor speedups; one crossing is slower. These are not complete
recognizer benchmarks and not a broad hard-knot distribution.

`data/radius_experiment.json` retains output-size and timing comparisons for
the proved rectangular family. Radius two is more expensive than radius one
but returns a smaller kernel. The practical normal-form shortcut is cheaper
on this family. Its seven-round timing run is separate, not a paired ratio.
All experimental failures/limits described in the article are distinguished
from knot verdicts. The `prefix_height` counter is measured only when an
input-prefix query table is constructed; it is omitted from shortcut stats.

## Files and rebuilding

`cyclic_garside/` contains algorithms, independent replay, and bounded
reference oracles. `tests/` contains the executed suite. `data/` holds logs
and raw measurements. `certificates/` contains inputs and replayable examples.
`source_manifest.json` records inspected repository blobs and primary papers.
`CLAIMS.md` separates theorem, test, measurement, and integration status.

```sh
cd docs
sh build.sh
```

The article uses ordinary pdfLaTeX packages. No bibliography download or
network access is required. The archive includes generated table fragments.
Results are offered for mathematical and implementation review under MIT-0.
