# Weighted normal components and quadrilateral disc-count reduction

Research continuation for Vladimir Reshetnikov's ProveIt project, 9 October 2026.

**Read the 30-page `article/weighted_normal_components.pdf` first.** The complete LaTeX source,
proofs, tables, figures and bibliography are alongside it. This is a serious local
algorithmic improvement toward the project's quasi-polynomial recognition goal;
it is not a claim that the delivered pipeline recognizes every knot in
quasi-polynomial time.

## Results

For an admissible binary normal vector in a validated finite compact connected
orientable three-manifold with exactly one torus boundary, the new operation:

1. Computes component weights without expanding points or components.
2. Counts essential disc components from three statistics: Euler characteristic
   one and nonzero boundary class modulo two.
3. Removes vertex links, divides by quadrilateral content, and recovers the exact
   count using `D(x) = g D(P)`.
4. Produces evidence checked by an independent weighted arithmetic replay.

Weighted AHT counting and canonical Q-theory are established antecedents. The
article credits them and proves the specific implementation and count reductions.
A zero count rejects only the supplied vector. A positive count becomes an unknot
witness only after the triangulation is bound to the input knot exterior.

The article also proves a two-weight variant using ambient homology and gives
a compact cocycle certificate design. That variant is proposed for future
implementation and is not part of the code or reported measurements.

## Main measured results

All times include source validation, certificate production and independent replay.
The reported speedups are medians of within-round ratios over seven rounds.

| Supplied-vector case | Faster route | Comparison | Paired speedup |
|---|---:|---:|---:|
| 64-tetrahedron meridian | 203.93 ms, three weights | 1,728.48 ms, full coordinates | 9.21x |
| 128-tetrahedron meridian | 1,152.80 ms, three weights | 12,796.75 ms, full coordinates | 11.13x |
| 32,779-bit coordinates, 16 tetrahedra | 21.81 ms, reduced count | 169.70 ms, direct three-weight census | 7.64x |

These are normal-surface subroutine measurements, not whole-knot timings. The
full-coordinate route returns richer intermediate output. Both query families
have identical A/A controls; raw samples are retained. No timing fit is treated
as an asymptotic proof.

## Contents

- `article/`: PDF, main `.tex`, all included sections, references, figure source,
  vector PDF and PNG figures, generated TeX tables and summary CSV.
- `code/fast/`: runnable source snapshot, six new modules, two new test files,
  seven relevant baseline test files, four research drivers, required fixtures.
- `results/`: original audits and paired timings, frozen Regina corpus and two
  explicit aggregate-invariant counterexamples.
- `examples/`: native example runner and source-bound proof objects.
- `integration.patch`: additive patch for application at the ProveIt repository root.
- `INTEGRATION.md`: API contracts, dependency pin, integration guidance.
- `reproduce.py`: portable launcher; results of new runs go to `reproduced/`.
- `MANIFEST.json` and `MANIFEST.sha256`: baseline identities and payload integrity.

## Reproduce

Python 3.10+ is required. The mathematical kernel uses the standard library.
Regina is optional except for the external audit and Regina-specific tests.
The recorded environment used CPython 3.12.14, Regina Python package 7.4.1
(engine string 7.4), and Matplotlib 3.10.8 for figures.

```bash
python3 reproduce.py tests
python3 reproduce.py audit
python3 reproduce.py regina
python3 reproduce.py benchmark
python3 reproduce.py example
python3 reproduce.py figures
python3 reproduce.py paper
python3 reproduce.py verify-manifest
```

`tests` runs the 103 selected methods. `audit` runs the two independent abstract
finite audits. `regina` uses the saved corpus; it does not depend on reproducing
a vertex enumeration order. `benchmark` runs full recorded sizes serially and
can take several minutes. `paper` uses `latexmk` or three `pdflatex` passes.
Figure generation needs Matplotlib; paper compilation needs a working TeX Live
installation with the packages listed in the main source.

The frozen evidence records 10,000 abstract kernel cases, another 2,500 independent
checker cases and 366 certificate mutations; all pass. The external audit has
1,275 normal vectors on 45 triangulations, 5,100 output comparisons and 5,100
certificate replays; all pass. All 103 selected regression methods passed with
Regina available. Explicit expansion is limited to the small oracles.

## Repository pin

Baseline: `7518823550fbc8c217bc8be0113fe52002e77465`.

https://github.com/VladimirReshetnikov/ProveIt/tree/7518823550fbc8c217bc8be0113fe52002e77465/Topology/UnknotRecognition

Apply the additive patch after review; do not replace a newer checkout with the
bundled reproduction snapshot. No existing recognizer defaults were changed.
The MIT-0 project license and embedded attribution files are preserved.
