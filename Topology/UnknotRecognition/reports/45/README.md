# Compressed Christoffel width and primitive-power elimination

Research contribution for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

## Read first

The article is `docs/article.pdf`; its source is `docs/article.tex` with three generated table files beside it. The contribution proves an exact compressed primitive-power test, a torsion-free elimination rule, and a normalization-free parallel round-depth bound. It **does not establish unrestricted quasi-polynomial unknot recognition**. No remote repository files were changed.

For a cyclically reduced binary word grammar with S nodes and B bits in its maximum expanded length, the kernel and independent replay use

    O(S (B + log(S+2)) + B^2)

bit operations. A successful d-round normalization-free contraction run has an explicit `poly(initial parameters) * 2^O(d)` bound. A controlled producer and a guarantee that the schedule reaches a decisive endpoint remain necessary. These hypotheses are not supplied for all knot diagrams.

Rank-two compressed primitivity being polynomial-time is prior work, including Kapovich's July 2026 preprint. The article distinguishes that result from the arithmetic, primitive-power, and presentation-composition contributions here. Priority beyond the examined sources is not claimed.

## Reproduce

Python 3.10 or later; standard library only. The recorded run used Python 3.13.5 on Linux. From this directory:

```sh
python tests/test_research.py
python code/verify_examples.py
python code/make_tables.py
sh build.sh
```

The test command reruns the 22 test methods and updates `data/test_summary.json`. The retained `data/test_log.txt` records the delivery run. Building the PDF requires `pdflatex` and the packages in the preamble. It does not require internet access.

A fresh timing run can be produced with:

```sh
python code/benchmark.py > data/benchmark_log.txt
python code/make_tables.py
sh build.sh
```

This overwrites the shipped timing JSON and CSV. Elapsed times are machine-specific; the article's narrative timing values refer to the shipped run and do not automatically update. The generated tables update from the JSON. Shuffle order is reproducible from the code and seed, not separately stored. Timing metadata corrects the exponent-2 bit length to two; the original timed samples are unchanged.

Verify archive contents before rerunning commands that change data:

```sh
python verify_manifest.py
```

## Exact kernel example

```python
import sys
sys.path.insert(0, 'code')
from christoffel import fibonacci_slp, classify
from checker import verify_power

arena, root = fibonacci_slp(64)
root = arena.power(root, (1 << 128) + 1)
answer = classify(arena.rules, root)
assert answer.certificate is not None
assert verify_power(arena.rules, answer.certificate)
print(answer.status, len(arena.rules), arena.lengths[root].bit_length())
```

This is a free-group assertion, **not a knot verdict**. `classify` rejects a root that is not freely and cyclically reduced. General compressed normalization belongs to a separate algorithm and has a separate cost.

## Source-bound knot demonstration

```python
import sys
sys.path.insert(0, 'code')
from braid_bridge import produce, verify_braid_certificate

braid = [1, 2]  # A stabilized circle, on three strands.
result = produce(3, braid)
assert result['status'] == 'UNKNOT'
assert verify_braid_certificate(3, braid, result['certificate'])
```

This small adapter derives a presentation from an actual single-component braid closure and replays its trace independently. Its Artin words and eliminations are literal and capped. It is not a quasi-polynomial braid-to-presentation producer. An unsuccessful search returns `INCONCLUSIVE`, never a negative knot verdict.

## Contents and trust boundaries

- `code/christoffel.py`: binary-SLP counts, reduction guards, prefix-height kernel, shared aligned scan, and test grammar builders.
- `code/checker.py`: independent local certificate checker; no imports from the query producer.
- `code/oracle.py`: literal word/root/Whitehead oracle used for independent finite cross-checks.
- `code/braid_bridge.py`: capped source-bound positive knot demonstration with independent presentation/trace replay.
- `code/contraction.py`: normalization-free disjoint-pair projection prototype. Its result is explicitly conditional on a torsion-free presentation; it does not establish that input provenance itself. A fully independent whole-round trace checker is not included.
- `code/wordarena_adapter.py`: read-only adapter for the inspected WordArena schema; tested against a schema-compatible stub, not a complete maintained checkout.
- `code/jones_oracle.py`: independent exponential small-braid bracket/Jones consistency checker. Jones identity is never an unknot certificate.
- `code/benchmark.py`, `code/make_tables.py`: reproducible timing and table generation.
- `tests/`, `data/`: exhaustive and randomized checks, raw timings, examples, provenance, and claim ledger.
- `integration/INTEGRATION.md`: required production wrapper, certificate-version, and replay changes; not an installed patch.

## Validation and performance scope

All 22 test methods pass. The exhaustive test includes 29,540 cyclically reduced words of lengths 1 through 9, with 844 primitive-power positives. Additional checks cover 4,496 signed/rotated Christoffel powers, 1,200 random parses, source-bound braid certificates, mutation/cancellation guards, a 6,940-bit expanded-length nonuniform word, and balanced contractions up to rank 256.

The largest displayed kernel ratio is about 1,160 against a **literal** baseline. It is not a ratio against the maintained compressed engine. Large unexpanded cases have no baseline completion time and no assigned speedup. The 48-case isolated braid comparison is close (ratio of summed case medians about 1.068) and does not establish a production speedup. Synthetic balanced presentations are not represented as knot diagrams.

The full maintained recognizer suite was not run, no production runtime improvement is asserted, and no Lean formalization is included. See the article and claim ledger for the exact proved, implemented, conditional, and unimplemented boundaries.
