# Rvachev up-function Fourier decay

This group has one canonical synthesis, a separately supplied rewrite awaiting
reconciliation, and two arrivals: one addressing a gap the synthesis states,
and one answering that arrival's finite-smoothness question. The canonical
document is:

- [`Rvachev_Up_Fourier_Decay.tex`](Rvachev_Up_Fourier_Decay/Rvachev_Up_Fourier_Decay.tex) — editable source;
- [`Rvachev_Up_Fourier_Decay.pdf`](Rvachev_Up_Fourier_Decay/Rvachev_Up_Fourier_Decay.pdf) — retained rendered checkpoint.

The current live TeX has 4,185 lines, 172,728 bytes, and SHA-256
`a1e5f815daddef85a022fec07a7c2b01379a8bd9e76e8045a16e63087208df76`;
it now uses `\TwoAdicValuation` for its dyadic valuation.  The retained
55-page A4 PDF has 1,049,155 bytes and SHA-256
`df65cbf5223e48cb393fb7cb2af7467a1837371b061f67f7995dcd507e7e3677`.
No PDF was regenerated after the notation-only source edit, so these are
distinct live-source and historical-artifact identities, not a synchronized
publication pair.

## Separately supplied rewrite

[`Rvachev_Up_Fourier_Decay-2.tex`](Rvachev_Up_Fourier_Decay-2/Rvachev_Up_Fourier_Decay-2.tex)
and its [PDF](Rvachev_Up_Fourier_Decay-2/Rvachev_Up_Fourier_Decay-2.pdf) contain
*Fourier Decay of Rvachev's Up-Function: A guided and rigorous account of exact
products, decay spectra, fluctuations, Cesàro gauges, peaks, and valleys*,
dated 3 September 2026. The pair was added in commit
`aabd126c8a18c6c09ec5ea266788d64cc56b3462` and is retained separately pending
claim-by-claim reconciliation with the canonical synthesis. Its filename is
not a declaration that it supersedes that synthesis, nor is this addition a
restoration of the older donor with the same directory name at the
pre-consolidation pin below. Manuscript proof labels do not establish Lean
coverage.

## Arrivals on the spectral/RMS gap

[`Spectral_Collapse_Alternating_RMS/`](Spectral_Collapse_Alternating_RMS/)
holds *Spectral Collapse and Alternating RMS Asymptotics for the Rvachev
Up-Function* (23-page A4 PDF, 1,566-line source), filed on 2026-09-28 by a
quick archival intake.  It addresses the gap the canonical synthesis states
after its RMS transfer eigenfunctions: that `−1/4` has not been shown to be
the second eigenvalue on a specified space, and that the alternating
`(−1/2)^n` relative RMS rate is numerical evidence only.  On the Hardy disk
spaces `H²({|z−1/2| < R})`, `R > 1/2`, it claims the complete spectrum
`{0, 1/2, −1/4}` and the RMS law `R_n² = M/2 + (B/6)(−1/2)^n + ε_n`,
with `B` and `M` enclosed by an exact-rational interval certificate
(`certify_integer.py`, standard library only) and an independent `mpmath.iv`
cross-check.  The claims are unreviewed, the synthesis still states the gap,
and no Lean statement exists.

[`Sobolev_Spectral_Disks_Rvachev_Thue_Morse/`](Sobolev_Spectral_Disks_Rvachev_Thue_Morse/)
holds *From Analytic Spectral Collapse to Sobolev Spectral Disks*
(24-page A4 PDF, 1,773-line source, a standard-library exact check
program), filed on 2026-09-29 by a quick archival intake.  It answers
the Sobolev part of the arrival's question "Spectra at finite
smoothness": on periodic Sobolev spaces `H^s` (with logarithmic
refinements) the same operator has a whole disk of essential
spectrum, of radius `2^{−s}√(1+√17)/4`, plus the eigenvalues `1/2` and
`−1/4`, which are isolated only above `s_0 ≈ 0.1785` and `s_0 + 1`
respectively; the same holds on interval spaces of integer order.  So
`−1/4` is the second spectral value only on smooth enough spaces, not
on `L²` or `H¹`.  At the critical order a logarithmic weight still
gives a two-term moment law, although no operator-norm law of that
order exists.  Its Thue–Morse/Stern cutoff identity and energy
formulas are already in
[`../thue-morse/Thue_Morse_Frontier_Deductions/`](../thue-morse/Thue_Morse_Frontier_Deductions/),
Part I, which it does not cite.  Hölder spaces are not treated.
Unreviewed; no Lean statement.

## Canonical synthesis

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

Only the `.tex` and retained `.pdf` are committed; LaTeX auxiliary files
remain untracked.

See [`../MANIFEST.md`](../MANIFEST.md) for the thematic draft inventory.
