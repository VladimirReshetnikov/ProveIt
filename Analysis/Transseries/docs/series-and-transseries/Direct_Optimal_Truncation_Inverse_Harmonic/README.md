# Direct Optimal Truncation of Inverse Harmonic Transseries

**Reflection, positive tail densities, and eventual enveloping**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main result and scope

The article answers the explicitly stated `prob:direct` in ProveIt's
`Inverse_Harmonic_Stokes_Transport/inverse_harmonic_transseries.tex`.
For the inverse defined by psi(W(X)+1/2)=log(X), it establishes:

- An exact exterior dispersion representation with an eventually positive
  tail density and a retained convergent Laurent correction.
- A strict first-omitted-term bound, uniform for X >= X0 and N >= N0.
  The threshold constants are existential; a sufficient criterion in
  analytic constants is given, but no global numerical threshold is claimed.
- The full first exponential block for direct partial sums at N-pi*X bounded,
  including explicit B1 and B2, a half-next-term law, wider truncation profiles,
  and the first difference from inversion of a forward truncation.

The proofs are mathematical arguments, not Lean-checked proofs. Global
publication priority has not been established. Classical reflection,
Stirling asymptotics, and the inherited coefficient formula are credited.
Nine further research questions are included.

## Contents

- `direct_inverse_harmonic.tex`: self-contained editable article.
- `direct_inverse_harmonic.pdf`: compiled 24-page A4 article.
- `verification/verify.py`: exact coefficient/sign checks and numerical tests.
- `verification/derive_amplitudes.py`: finite symbolic amplitude algorithm.
- `verification/results.json`: actual 190-digit run; 76 numerical parameter cases.
- `verification/certificates.json`: six exact-rational forward residual enclosures
  proving inverse orderings for three consecutive-partial-sum pairs.
- `verification/amplitudes.json`: symbolic density and error coefficients through
  degree three, including checks of the displayed B1 and B2.
- `verification/precision_audit.json`: comparison with a 230-digit rerun;
  all stored numerical strings agree. This is not interval validation.
- `verification/pdf_audit.json`: compilation and rendering audit.
- `verification/numeric_table.tex`: table generated from the numerical run.
- `figures/truncation_window.pdf` and `.png`: stored numerical illustration.
- `provenance.json`: pinned source and scope metadata.

## Rebuild

The LaTeX source has no repository-relative style dependencies. A normal TeX
installation must include the packages in its preamble, notably `newtxtext`,
`newtxmath`, `aliascnt`, and `cleveref`. The figure and numeric table are stored,
so rebuilding the PDF does not require rerunning Python.

```sh
make pdf
make verify
```

Equivalent commands:

```sh
python verification/verify.py
python verification/derive_amplitudes.py
pdflatex -interaction=nonstopmode -halt-on-error direct_inverse_harmonic.tex
pdflatex -interaction=nonstopmode -halt-on-error direct_inverse_harmonic.tex
pdflatex -interaction=nonstopmode -halt-on-error direct_inverse_harmonic.tex
```

For a higher-precision diagnostic run:

```sh
python verification/verify.py --dps 230 --no-figure
```

That command overwrites `results.json` and the generated table with the new run.
Run the default command again to restore the 190-digit baseline. It does not
regenerate the supplied historical cross-precision audit automatically.

The exact sign checks use the proved forward Fermi-integral remainder and a
rational logarithm enclosure after a finite digamma recurrence shift. They do
not use floating-point digamma evaluations as premises. They are nonetheless
ordinary exact-arithmetic program checks, not proof-assistant kernel certificates.

## Pinned repository

`a795fcffa4b3ece22761d81fbed3c43be8b81795`

Base path:
`Analysis/Transseries/docs/series-and-transseries/`

Primary predecessor:
`Inverse_Harmonic_Stokes_Transport/inverse_harmonic_transseries.tex`

The article distinguishes the direct sum S_N from the root u_N of a truncated
forward equation. Its direct correction is -pi/12 plus the universal gamma
shift correction; the predecessor's forward correction has +pi/12. The exact
contour correction E_T must not be omitted when reusing the representation.
