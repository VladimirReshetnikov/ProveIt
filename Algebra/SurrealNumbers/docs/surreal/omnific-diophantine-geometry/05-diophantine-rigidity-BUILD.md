# Build and verification

## Compile the article

Use a TeX Live or MiKTeX installation with the packages named in the source,
including `newtx`, `microtype`, `tcolorbox`, `hyperref`, `cleveref`, `xurl`,
`needspace`, and the standard AMS packages.

From the directory containing `article.tex`, run:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex article.tex` three times, continuing until the
table of contents, citations, and cross-references are stable. The bibliography
is embedded; neither BibTeX nor Biber is needed.

The delivered PDF was compiled with pdfLaTeX and visually checked after
rendering. The final build had no undefined references or overfull boxes.
There are no separate fonts to install from this package: use the fonts
supplied by the TeX distribution.

## Run the exact finite checks

Python 3.9 or newer is required. On Windows, `py` may be substituted for
`python`.

```text
python -m pip install -r requirements.txt
python verify_examples.py
```

The default run verifies explicit ordinary witnesses for every input from
-40 through 40 to the quartic standard-integer definition. Change the finite
interval with:

```text
python verify_examples.py --standard-radius 80
```

A radius from 0 to 200 is accepted to keep the elementary pair-sum search
within a reasonable range. The program prints an error and exits unsuccessfully
on a failed check. It does not rely on Python `assert` statements that could
be disabled by optimization.

To record a new check log:

```text
python verify_examples.py > verification.txt
```

## What was and was not checked

The checked identities include the Pell recurrence, the Pythagorean
parametrization and Bezout witness, the separated-power differential identity,
Fermat Wronskian identities, finite geometric telescoping, and finite formal
binomial expansions. Their universal uses in the article are justified by
mathematical proofs, not by extrapolating these finite checks.

No Lean compiler was run. No complete symbolic implementation of the surreal
numbers is included. The PDF production checks concern rendering and document
integrity, not independent mathematical verification.
