# Build and check

The manuscript is a single UTF-8 LaTeX source with an internal bibliography.
It uses pdfLaTeX and common TeX Live packages. No external figures, font files,
BibTeX database, or shell-escape commands are required.

## PDF

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error critical_phase_removal.tex
```

Without latexmk, run the following command three times to settle references and
the table of contents:

```sh
pdflatex -interaction=nonstopmode -halt-on-error critical_phase_removal.tex
```

The delivered PDF was built with pdfTeX 1.40.26 (TeX Live 2025/dev/Debian).

## Exact finite regression checks

```sh
python -m pip install -r requirements.txt
python code/verify.py --output data/verification.json
```

All random cases use a fixed seed. Reports differ in elapsed time and may differ
in recorded dependency-version strings; mathematical outputs should agree.
Failure raises an exception and returns a nonzero process exit code. Python's
optimization switch does not disable the checks.

## Make targets

`make pdf` builds the PDF, `make check` runs the checker, and `make all` does both.
`make clean` removes only conventional LaTeX auxiliary files. It does not remove
the TeX, PDF, or verification report.
