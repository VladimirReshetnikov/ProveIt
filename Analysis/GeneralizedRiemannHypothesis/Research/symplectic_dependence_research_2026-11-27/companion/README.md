# Universal critical profiles for many prescribed symplectic frames

This companion proves a universal critical total variation profile for the complete cross-pairing experiment of many independent prescribed frames in a finite symplectic space. All finite fields are included, and every prescribed form may be degenerate.

If the total frame dimension is `2n + c`, the integer `c` is fixed, and the largest frame dimension is negligible compared with the total, the limiting distance from independent uniform cross-pairings depends only on `q` and `c`. The manuscript gives the exact product/sum formula and asymptotically optimal rank/nullity tests. Every fixed number of frames has asymptotically independent pairings even while the complete collection retains a positive statistical signal.

## Files

- `critical_profile.tex`: complete self-contained manuscript.
- `critical_profile.pdf`: compiled seven-page paper.
- `code/verify.py`: exact finite-field and rational verification, requiring only Python's standard library.
- `results/verification.json`: detailed output of the checked run.
- `results/summary.json`: aggregate check counts.

## Reproduction

From this directory:

```sh
python3 code/verify.py
pdflatex critical_profile.tex
pdflatex critical_profile.tex
```

The verification writes to `results/verification.json` and `results/summary.json`.

## Status and comparison

The theorem has a complete mathematical proof and independent mathematical review of its coupling, Gram-density, and conditioning steps. It is not Lean-formalized or externally peer-reviewed.

The even scalar profile for two nondegenerate frames was already present in the inspected ProveIt source. Rank universality with some deterministic entries has antecedents, particularly Koenig and Nguyen's *Rank of Near Uniform Matrices*. The claimed extension is the full experiment for arbitrarily many small prescribed frames with arbitrary internal alternating forms, with a uniform profile and tests in every characteristic. Worldwide priority has not been established.

Source snapshot: `VladimirReshetnikov/ProveIt` commit `00cadb961bbe77c74e5d082c4948f8884d58a970`, 27 November 2026. Exact source paths and literature citations appear in the paper.
