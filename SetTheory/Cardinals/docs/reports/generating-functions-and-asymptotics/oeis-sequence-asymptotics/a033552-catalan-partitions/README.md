# Partitions into Catalan Numbers
## All-Orders Asymptotics, Periodic Corrections, and Inverse Growth

Research report dated October 1, 2026, focused on OEIS A033552.

`article.pdf` is the typeset paper; `article.tex` is its self-contained LaTeX
source. The paper develops conventional proofs of an all-orders saddle
expansion, an explicit periodic asymptotic with its first correction, an
inverse threshold expansion, a largest-part-index limit law, and a general
exponential–polynomial part-growth proposition. It includes eight further
research directions and a provenance discussion.

## Scope and status

The inspected OEIS entry contains no asymptotic formula, but does not state
an explicit asymptotic conjecture. The article does not claim an exhaustive
literature-priority search, a resolution of Pak's exact counting-complexity
question, or novelty of classical saddle-point and periodic-partition methods.
The sequence-specific formulas and their proofs are the results developed here.
There is no Lean formalization in this package. Floating-point checks are not
interval certificates; the mathematical remainder arguments are in the paper.

## Package contents

- `article.tex`, `article.pdf`: manuscript and compiled article.
- `code/catalan_partitions.py`: exact coefficients and numerical asymptotics.
- `code/verify.py`: exact-integer cross-checks, Gaussian coefficient generator,
  independent phase evaluations, coefficient, inverse, and largest-index tests.
- `code/symbolic_audit.py`: exact SymPy audits of the normalization, first
  periodic correction, summatory coefficients, and inverse coefficient.
- `data/verification.json`, `data/symbolic_audit.json`: recorded executed checks.
- `data/*.csv`: numerical tables in a convenient machine-readable format.
- `data/a033552_0_300.txt`: independently generated initial coefficients.
- `SOURCE_NOTES.md`: source and repository provenance.
- `requirements.txt`, `build.sh`: reproducibility aids.

## Reproduce the calculations

Use Python 3.10 or newer. The recorded run used Python 3.13.5, mpmath 1.3.0,
and SymPy 1.14.0. Install the pinned numerical dependencies, then run from the
package directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py --max-n 1000000 --dps 60
python code/symbolic_audit.py
```

The code itself makes no network requests. The default exact computation
stores a million Python integers and therefore needs substantially more memory
than the short text output. A smaller diagnostic run is available with
`--max-n 10000`; only the applicable sample rows will be written.

`verify.py` overwrites its generated tables and verification JSON in `data/`.
Use `--output /some/other/directory` to preserve the supplied numerical run.
The symbolic audit writes `data/symbolic_audit.json`.

## Rebuild the PDF

A normal TeX Live installation with pdfLaTeX, newtx, tcolorbox, hyperref, and
cleveref is sufficient. The bibliography is included in the source; no BibTeX
run, remote files, or external figures are needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

On a fresh build, a third pass may be needed for the table of contents and
cross-references to settle. The supplied `build.sh` performs three passes.
The TeX uses standard installed fonts; no font files are included.

## Interpreting the numerical output

The exact-cumulant approximation is more accurate at moderate arguments than
the fully explicit logarithmic-size expansion. At n = 1,000,000, the relative
error after the second saddle correction is about 4.66e-5. The explicit first-
correction formula has about -1.06e-2 relative error at that same argument.
The corrected inverse has about 2.91e-2 relative error at y = p(1,000,000).
These different error scales are reported rather than hidden: the asymptotic
parameter is only about 1/11 at that argument.

The Fourier implementation explicitly requests Euler–Maclaurin zeta
calculation to avoid an ill-conditioned eta quotient at some Fourier
frequencies. An independent real-lattice phase implementation checks both
the phase value and its partial alpha derivative.

## Integration into ProveIt

This package is standalone and does not alter the repository. A natural
placement is a new article directory associated with sparse-partition
asymptotics or the transseries companion. The relevant transseries README
files were rechecked at commit e6190a94552f119e9a2140e5fea8450a045a0837.
Their distinctions between continuous inversion, integer thresholds, and
formalization status are retained in the paper.
