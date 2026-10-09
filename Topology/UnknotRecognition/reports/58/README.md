# Compressed topology spectra for normal surfaces

**Research continuation for ProveIt — 9 October 2026**

This package contains the article, implementation, proofs, experiments and
integration patch for a compressed census of the connected component types
of a supplied normal surface. The output records Euler characteristic,
actual boundary-circle count, orientability, genus or crosscap number, and
an integer multiplicity for each distinct type.

The construction uses a boundary-orbit transversal and two weighted surface
queries, each with weight dimension two. An optional quadrilateral-content
core removes vertex links and common multiplicities before the expensive
orbit operations, then restores the complete original spectrum with the
correct one-sided scaling rules. Every completed result can carry a
source-bound certificate checked by an independently implemented replay.

The existing full unknot recognizer and its default pipeline are unchanged.
This contribution improves a supplied-vector topology operation needed by
future surface-discovery and hierarchy algorithms. Polynomial encoded
component-topology computation is classical; the contribution is a precise
constant-dimensional, core-sensitive refinement of AHT primitives and its
integration-ready implementation. It does not establish a general
quasi-polynomial unknot-recognition bound. [CLAIMS.md](CLAIMS.md) states the
claims and their limits explicitly.

## Start here

- Read the [article PDF](article/article.pdf) for the mathematical argument,
  measured tradeoffs, and proposed research programme.
- Read [INTEGRATION.md](INTEGRATION.md) to apply the additive repository patch
  and call the new API.
- Read [CLAIMS.md](CLAIMS.md) for the domain, trust boundary, prior-art
  relationship, and distinction between established results and future work.

The article's master source is [article/article.tex](article/article.tex).
Its sections, reference list, figures and data-driven tables are included.

## Package contents

| Location | Purpose |
|---|---|
| `article/` | PDF, master TeX, modular sections, references, figures, plotting script and benchmark tables |
| `code/fast/` | Runnable snapshot of the required ProveIt runtime, new modules, selected regression tests, fixtures and research drivers |
| `results/` | Recorded regression, independent Regina audit, final paired measurements, family-formula checks and retained benchmark certificates |
| `integration.patch` | Additive changes under `Topology/UnknotRecognition/fast` for integration into ProveIt |
| `reproduce.py` | Commands to verify the package and reproduce individual evidence gates |
| `MANIFEST.json` | Delivered-file SHA-256 manifest |
| `LICENSE` | Repository license accompanying the code snapshot |

The pinned upstream baseline is
[`eb368edf975695e3e16a8774dcb7846bda0c13a0`](https://github.com/VladimirReshetnikov/ProveIt/tree/eb368edf975695e3e16a8774dcb7846bda0c13a0/Topology/UnknotRecognition).
Inherited source bytes were checked against their pinned Git blob hashes;
the validation record is
[results/baseline_source_validation.json](results/baseline_source_validation.json).
The patch introduces six runtime modules and three test modules, plus the
focused research drivers and inputs. It does not replace historical modules.

## Reproduce the evidence

Run these commands from the unpacked package root. New outputs go to
`local_results/`, preserving the delivered measurements and certificates.

```sh
python reproduce.py verify
python reproduce.py tests
python reproduce.py audit
python reproduce.py formulas
python reproduce.py proofs
```

The commands have separate purposes:

| Command | Check performed |
|---|---|
| `verify` | Compare every listed delivered file with the SHA-256 manifest |
| `tests` | Run the focused 148-method geometry regression gate across 13 selected test modules |
| `audit` | Replay all frozen bounded Regina answers, compare both API modes and selected AHT controls, and verify every certificate |
| `audit --fresh` | Additionally recompute the external oracle in Regina from the frozen face pairings and vectors |
| `formulas` | Check the recorded spectra against independently stated formulas for the benchmark families |
| `proofs` | Independently replay the 52 retained benchmark certificates |
| `bench --quick --rounds 5` | Run the benchmark driver's smaller family selection |
| `bench --rounds 5` | Rerun the full paired benchmark; allow several minutes |
| `figures` | Recreate figures, tables and CSV from the published measurement file |
| `article` | Build a copy of the LaTeX article in `local_results/article-build/` |

For a fresh external check and a full timing run:

```sh
python reproduce.py audit --fresh
python reproduce.py bench --rounds 5
```

The full recorded configuration is reproduced by this explicit command
from `code/fast/`:

```sh
python3 topology_research/benchmark.py \
  --output ../../local_results/benchmark-rerun.json \
  --rounds 5 --seed 2026100919 --timeout 90 --save-proofs \
  --sizes 8 16 32 64 128 --bit-sizes 128 4096 16384 32768
```

Timing varies with hardware, Python, load, and arithmetic sizes. The article
uses the recorded paired measurements and includes cases where extra
preprocessing or query construction costs matter. A local rerun produces new
evidence; it does not silently replace the published interpretation.
The figure generator deliberately checks the hash of the published benchmark
file. Using different data requires reviewing the numerical narrative as well
as regenerating plots.

### Dependencies

The new runtime and its certificate checkers use Python's standard library
and the included existing `fastunknot` modules. The recorded runs used
Python 3.12.14. Regina 7.4 was used for the fresh geometric oracle and for
optional existing regression tests. Without Regina, the frozen audit remains
available, while Regina-dependent regression methods report skips; reproducing
the recorded zero-skip gate requires Regina.

Figure regeneration requires Matplotlib. Article compilation requires
`latexmk`, a PDF-producing LaTeX installation, and the packages declared in
`article/article.tex`, including TikZ, `cleveref`, `listings`, `microtype`,
and the standard AMS packages. Reading the delivered PDF needs none of these
dependencies.

## Recorded correctness evidence

The focused regression gate completed **148 test methods with zero failures,
errors or skips**. Its raw output and summary are included in `results/`.
The three new test modules cover least transversals, sparse cover inversion,
geometric integration, source/proof mutation, exact resource allowances,
and cancellation.

The independent Regina audit contains **664 cases** on **34 labeled
triangulations**, representing **26 triangulation isomorphism classes**.
Both direct and reduced APIs were checked on every case, with 67 additional
classical-AHT controls: **1,395 exact matches and 1,395 accepted certificates,
with no failures**. The final run recomputed the oracle afresh. The corpus
includes one-sided and disconnected surfaces, projective planes, Klein
bottles mixed with tori, multiple boundary circles, and higher-genus surfaces.
These are bounded external comparisons, separate from the large-integer
experiments. See [results/regina_audit.json](results/regina_audit.json).

The frozen corpus embeds the face pairings, coordinates and expected
histograms. Its generation-time fixture hashes precede a later correction of
an extra terminal newline in inherited source files; the final audit was
rerun against the corrected runtime bytes. This correction changed no fixture
data or Python semantics. Package hashes and final runtime hashes identify the
delivered, corrected files.

## Next research steps

The article proposes concrete work on faster transversal replay, reusable
weighted observers, componentwise essentiality, representative-to-type
association, general boundary topology, compressed slopes and attachment data,
larger geometric cores, certified diagram-to-exterior construction, controlled
surface discovery, compressed cutting, and global hierarchy accounting.
These are the remaining paths from an efficient certified local observer
toward the project's full quasi-polynomial recognition objective.
