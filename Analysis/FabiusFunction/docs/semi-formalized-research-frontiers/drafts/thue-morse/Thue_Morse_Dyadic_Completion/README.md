# A Dyadic Completion of the Thue–Morse Product

**Lognormal moments, horizontal Dirichlet zero strings, and certified all-orders asymptotics**

Research article prepared for Vladimir Reshetnikov, dated 4 September 2026.

## Contents

- `Thue_Morse_Dyadic_Completion.tex`: the complete, standalone LaTeX source.
- `Thue_Morse_Dyadic_Completion.pdf`: the rendered article.
- `figures/`: the two included vector PDF figures.
- `code/verify.py`: exact coefficient/moment checks and high-precision numerical experiments.
- `code/check_original_mellin.py`: a separate numerical check of a stored zero using the original Mellin numerator, without the completing factor.
- `code/requirements.txt`: the exact package versions used for the stored experiments.
- `data/verification_60dps.json`: coefficients, consistency checks, ratios, and selected Dirichlet zeros.
- `data/verification_80dps.json`: independent higher-precision consistency checks.
- `data/direct_original_mellin_check.json`: the original-integral check at both shifts 1/2 and 1.

## Build the article

Use a recent TeX Live or equivalent installation. From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Dyadic_Completion.tex
pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Dyadic_Completion.tex
pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Dyadic_Completion.tex
```

Alternatively run `latexmk -pdf Thue_Morse_Dyadic_Completion.tex`.
The bibliography is embedded. No BibTeX invocation or repository checkout is
required. The source uses Libertinus if installed and otherwise Latin Modern;
no font files are included. Prebuilt figures are included, so Python is not
needed merely to compile the paper.

## Reproduce the experiments

The pinned numerical environment requires Python 3.11 or later.
A virtual environment is recommended to avoid changing other projects.

```sh
python -m venv .venv
# Activate the environment using the command appropriate to your shell.
python -m pip install -r code/requirements.txt
python code/verify.py --dps 60 --roots --figures
python code/verify.py --dps 80
python code/check_original_mellin.py
```

The root-solving run takes longer than the basic consistency checks.
The scripts make no network requests. Generated data paths are resolved
relative to the scripts, rather than to the current working directory.

The low-frequency Mellin representation uses zeta at exact dyadic resonances.
The script explicitly selects Euler–Maclaurin evaluation to avoid numerical
cancellation in an eta-quotient implementation. A direct product calculation
provides an independent check of the Fourier formula.

## Mathematical and numerical status

The paper supplies analytic proofs of the completion, the existence and
localization of nonreal Dirichlet zero strings, the full coefficient formulas,
and the signed remainder inequalities. The main existence theorem does not
rely on the numerical location of a particular zero.

The numerical roots are floating-point approximations, not interval-certified
enclosures. A small residual is not claimed to bound the root error. The
separate original-integral check uses the rounded root stored in JSON, so its
residual also reflects that rounding. Exact rational coefficient and Hankel
checks use symbolic integer/rational arithmetic.

The paper distinguishes established ingredients from results derived in this
investigation. Bibliographical priority is not established. In particular, a
relevant 2001 Alkauskas preprint was located bibliographically but could not be
retrieved, so its contents are not represented as checked. No new Lean
formalization is included or claimed.

## Source provenance

The requested source was the `Thue_Morse_Atlas_and_Frontiers` document in
`VladimirReshetnikov/ProveIt`. The native repository read returned source blob
SHA `7be75f3bc86f9c6712eec6d7550eaea53716434a`. The investigation focused on its
Laplace/Mellin/Dirichlet sections, with targeted searches elsewhere in the
repository, not an exhaustive review of every file in the research tree.
See the article's bibliography and provenance section for the literature audit.
