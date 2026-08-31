# Rvachev up-function Fourier decay

This group has one canonical human-readable document:

- [`Rvachev_Up_Fourier_Decay.tex`](Rvachev_Up_Fourier_Decay/Rvachev_Up_Fourier_Decay.tex) — editable source;
- [`Rvachev_Up_Fourier_Decay.pdf`](Rvachev_Up_Fourier_Decay/Rvachev_Up_Fourier_Decay.pdf) — synchronized rendered article.

The article is an editorial consolidation of the original 2018 question,
eight successive reports, the comparative and second-wave audits, the Gentle
Guide, and their useful computational evidence. It is not a mechanical
concatenation: repeated derivations are stated once, notation is unified,
missing arguments are supplied, contradictory claims are adjudicated, and the
strongest correct versions are retained. Its source concordance and correction
ledger record exactly what was taken from each predecessor.

The principal additions include a corrected Gamma–Pochhammer tail, detailed
proofs of the dyadic shell and fluctuation laws, the finite-*q* pressure
spectrum, exact RMS and energy identities, the sharp Gelfond envelope,
Lambert-*W* annular asymptotics, two valley regimes, the bounded-distortion
obstruction, and an affirmative shell-adaptive analytic Cesaro gauge. The
integer-ratio chapter strengthens the corpus with a global spectral
*q*-Pochhammer factorization, arbitrary-radius zero extraction, exact *b*-adic
ray laws, and the variance formula
`σ_b² = (π²/12)(b + 1)/(b - 1)`.

## Evidence and formalization status

The document deliberately distinguishes:

- self-contained exact proofs;
- named classical analytic inputs whose hypotheses are exposed;
- rigorous finite certificates and enclosures;
- high-precision numerical evidence that is **not** an interval proof;
- conjectural or still-unformalized frontier statements;
- exact declarations present in the current Lean source tree.

The appendix gives the human-readable/Lean parity ledger. A declaration named
there is a source-level cross-reference, not by itself a claim that a fresh
aggregate Lean build was run for this documentation change.

## Historical sources

The independent reports remain permanently recoverable at the immutable
pre-consolidation commit
[`2e3567feb14947ee3ebcdab11adca64e746ad26f`](https://github.com/VladimirReshetnikov/ProveIt/tree/2e3567feb14947ee3ebcdab11adca64e746ad26f/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/rvachev_up_fourier_decay).
The canonical article cites those immutable source paths. Their former live
directories were retired after consolidation so readers cannot mistake a
superseded report for the current result; Git history is the archive and still
preserves the independence used by the audits.

Useful audit programs and captured numerical data are retained under
[`verification_scripts/`](verification_scripts/). Read its README before
running anything: the scripts provide reproducible supporting evidence, but
they do not convert floating-point output into a proof.

## Building

From `Rvachev_Up_Fourier_Decay/`, run exactly three passes:

```text
pdflatex -interaction=nonstopmode -halt-on-error Rvachev_Up_Fourier_Decay.tex
pdflatex -interaction=nonstopmode -halt-on-error Rvachev_Up_Fourier_Decay.tex
pdflatex -interaction=nonstopmode -halt-on-error Rvachev_Up_Fourier_Decay.tex
```

Only the `.tex` and synchronized `.pdf` are committed; LaTeX auxiliary files
remain untracked.

See [`../MANIFEST.md`](../MANIFEST.md) for the thematic draft inventory.
