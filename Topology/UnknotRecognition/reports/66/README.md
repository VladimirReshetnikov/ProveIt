# Signed Continuation Bases and Euler-Optimal Disk Completion

Research continuation for `ProveIt/Topology/UnknotRecognition`, 9 October 2026.
Reviewed repository pin: `3a90fb34146c915328ab8eac6250cc2514f74ed0`.

The article is **`paper/main.pdf`**; its complete editable source is
`paper/main.tex` plus `paper/references.tex` and the generated table inputs.

## Results

The signed connectivity-and-consistency matrix on `r` live ports has binary
rank exactly `2^(r-1)`. A minimum-cost row basis retains at most that many
**original candidates** and preserves the optimum under every signed
completion. The article proves an exact finite-group determinant and rank
formula in every characteristic, and the operations that preserve the weighted
invariant. Rank-based weighted representative families are classical; the paper
credits Bodlaender–Cygan–Kratsch–Nederlof rather than claiming that general method
as new.

For compact surface fragments with certified seam maps, weight `-Euler` preserves
the maximum Euler characteristic of a connected orientable completion. With
certified nonempty boundary this preserves disk existence. The package goes
beyond the abstract kernel: `patchwork.py` is a **complete disk-selection
algorithm for a supplied finite system of triangulated patches**, fixed seam
pairings and one permanent unglued anchor. It runs in
`poly(N,B,b) * 2^(3b)` bit time with elementary elimination, where `b` counts
live ports between sites. Whole-site transitions are symbolic; their temporary
larger port sets do not get expanded cut vectors.

This is **not a general quasi-polynomial unknot recognizer**. No complete native
normal-patch producer, three-dimensional embedding adapter, essential-boundary
adapter, or global frontier-width theorem is supplied. Existing native exterior
provenance is acknowledged, not re-claimed as a missing feature. No upstream
runtime module has been modified and no maintained recognizer suite was run.

## Quick reproduction

Python 3.10+ and its standard library suffice for all runtime code and tests.
No network access is needed. From the extracted package root:

```sh
python reproduce.py test
python reproduce.py audit --out results/new-audit.json
python reproduce.py benchmark --out results/new-benchmark.json
python reproduce.py patches --out results/new-patches.json
python reproduce.py example
python reproduce.py pdf
```

The first command does not modify recorded data. Explicit `--out` paths preserve
the original audit and timing evidence. `pdf` rebuilds tables from the retained
records and runs `pdflatex` three times; it does **not** rerun benchmarks. Standard
LaTeX packages listed in the preamble are required. Equivalent Make targets are
provided. Optional package installation is possible with `pip install .`, but is
not needed for any reproduction command.

## A usable example

Run with `PYTHONPATH=src` (or after installing the package):

```python
from signed_continuations.core import Candidate, partitions, reduce_family
from signed_continuations.verify import verify_basis
from signed_continuations.patchwork import grid_system, solve, verify_witness

family = [Candidate(p, -p.blocks, str(i), "fixed-interface")
          for i, p in enumerate(partitions(4))]
result = reduce_family(family)
assert len(family) == 49
assert len(result.candidates) == 8
assert verify_basis(family, result.certificate)

# A genuine finite surface-patch problem; not patches in a knot exterior.
system = grid_system(3, 3)
answer = solve(system)
assert answer.disk_exists
assert verify_witness(system, answer)
```

`verify_witness` checks the **selected assembly's geometry**, not optimality or a
negative answer. A non-disk witness never certifies that no other choice yields
a disk. `solve` is complete for its explicit finite input by the paper's theorem;
certifying its negative answer independently requires replay of the entire
finite computation, not this single-witness routine.

## Validation retained in this delivery

The final audit reports **55 passing test methods**, all **68,581** ordered
signed compatibility cases through width five, **320** randomized families with
**6,400** independently checked optimum queries, **442** triangulated seam
gluings, and independent mesh enumeration of all **297** assignments of a small
patch system. It also checks integer factorization and modular ranks for the
trivial group, `C2`, `C3`, and noncommutative `S3`. Binary costs with 20,001-bit
magnitudes survive codec round trips without changing Python's decimal limits.

Paired finite patch benchmarks include mesh validation in both routes. On the
largest supplied grid, peak retained states fall from 257 to 16, with about
7.90x solver speedup. These are **abstract finite patch systems**, not whole-knot
benchmarks. Static one-query examples get slower after basis construction;
that negative result is retained alongside repeated-query gains. Raw results,
seeds, route timings, and independent mesh replay times are in `results/`.

## Integration

See `integration/INTEGRATION.md`, `integration/PROVENANCE.json`, and `CLAIMS.md`.
The package is additive. Place it in the next appropriate report directory under
`Topology/UnknotRecognition/reports/`, following current intake conventions.
Do not overwrite maintained modules or treat an opaque geometry key as a proof.
A future opt-in native stage should retain source-bound positive replay and the
existing exact fallback until completeness and all geometry obligations are met.
