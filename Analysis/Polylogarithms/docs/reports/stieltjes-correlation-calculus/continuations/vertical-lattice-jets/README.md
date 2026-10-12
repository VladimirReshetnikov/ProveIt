# Discrete Vertical Hurwitz Calculus

**Stieltjes jets, polylogarithmic sampling, and resonant contact terms**  
Research continuation for Vladimir Reshetnikov's ProveIt project, 11 October 2026.

## Read

`article.pdf` is the complete article. `article.tex` is its self-contained LaTeX
source, including the bibliography. No external section files, figures, or
bibliography database are required.

The central results are a compensated spectral sampling theorem, all-index
Stieltjes lattice identities, finite polylogarithmic horizontal differences,
normalized primitives, an all-negative-integer parity contact law, a
harmonic-number compiler for higher jets, finite Hurwitz–Lerch polygamma images,
and all-index Stieltjes-difference pairings with an explicit four-shift formula.

The Gamma/q-Pochhammer specialization is already published by Arabi Ardehali and
Rosengren (2026), and is explicitly credited. This package does not claim
exhaustive historical priority. It does not settle S6, revised S8, or the general
unequal harmonic-tail prefix conjecture.

## Reproduce

```sh
python -m pip install -r requirements.txt
python verification/run_checks.py
python build.py
```

The recorded run used Python 3.13.5, mpmath 1.3.0 and SymPy 1.14.0.
It passed **268 exact algebraic assertions and 38 numerical comparisons**, with
two corruption controls. Numerical work used 65 decimal working digits; the
largest recorded scaled residual was approximately 3.55e-43. These are
floating-point diagnostics, not interval enclosures or substitutes for proofs.
The results include independent lattice/image comparisons and explicitly
identified same-master cross-route checks.

The LaTeX build requires `pdflatex` and the standard packages listed in the
preamble. Three passes are used. Build auxiliaries are placed in a temporary
directory, not included in the delivery. The distributed PDF additionally
received rendered visual review.

## Files

- `verification/lattice.py`: reusable numerical evaluators and independent tails.
- `verification/run_checks.py`: complete exact and numerical replay.
- `results/verification.json`, `results/verification.log`: recorded checks.
- `results/build.log`, `results/layout_review.json`: build and layout records.
- `provenance/SOURCE_AUDIT.md`, `provenance/sources.json`: source scope and identifiers.
- `integration/INTEGRATION.md`: theorem map and preservation cautions.
- `integration/remove_duplicate_readme.py`: guarded editorial correction proposal.
- `SHA256SUMS`: delivery hashes, excluding the manifest itself.

No repository write was performed. The five then-listed incoming ZIP archives
were inventoried by name, but their interiors were not inspected. The source
map records moving-main reads separately from a pinned continuous-vertical
report read; it is not a complete repository snapshot.
