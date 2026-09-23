# Omnific integers and omnific–Diophantine geometry

[Read the article](article.pdf) · [LaTeX source](article.tex) ·
[Source reconciliation](RECONCILIATION.md)

The article studies the normal-form ring `Oz = ℤ ⊕ J`, ordinary residues,
common monomial divisors and denominator clearing, followed by equational
transfer, binary and norm-form rigidity, quadratic levels, and a quartic
definition of ordinary integer tuples with five auxiliary variables.

The current text starts from manuscript 01. Sections 1–4 have been reviewed
and compared with the elementary algebra in manuscripts 02 and 05, adding
a common Hahn workspace, mixed gcds with ordinary integers, common multiples
of all ordinary powers in a set-sized family, and a nilpotent-image test.
The later Diophantine and differential material is not yet fully reconciled.
See the reconciliation for the precise boundary and archive provenance.
No Lean coverage or independent referee review is claimed by this update.
The [coverage ledger](../../FORMALIZATION.md) records formalization separately.

## Build

From this directory, with a standard TeX Live or MiKTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The bibliography is included in the source; no bibliography processor or
external figures are needed. The preserved `code/01-diophantine-geometry-build.*`
scripts use delivery filenames and are historical artifacts; use the command
above for the maintained article.

## Finite checks

Use Python 3.9 or newer and SymPy 1.14.0. From this directory:

```sh
python -m pip install -r data/01-diophantine-geometry-requirements.txt
python code/01-diophantine-geometry-verification.py --output /tmp/omnific-checks.json
python code/02-diophantine-verify_examples.py
python code/05-diophantine-rigidity-verify_examples.py --standard-radius 40
```

Choose a writable output path on your platform. The scripts check ordinary
polynomial identities and finite examples. Source 01 checks 20 quadratic
isometry matrices, 31 Pell pairs, and 256 quartic-guard witnesses. Source 02
checks symbolic identities and finite supported products. Source 05 checks
separated-power products, Fermat Wronskians, geometric telescoping, truncated
binomial roots, quartic witnesses for integers from −40 to 40, and five
Mordell-curve points. Its guard uses four squares, whereas source 01's
stronger five-auxiliary-variable guard uses three squares.

These programs do not implement arbitrary surreal normal forms, certify
support bounds for all surreal exponents, or establish completeness of
Diophantine solution sets. Passing them does not verify the article in Lean.
The delivered output files under `data/` retain their historical contents.

## Provenance

Commit `be06fc8` placed three manuscripts from the archives preserved in
`f0b7f43`; only source 01 was initially installed as `article.tex`. The
[reconciliation](RECONCILIATION.md) records the present partial integration.
The manuscript's original repository snapshot and dated source audit remain
historical records, not an inspection of the current Lean implementation.
The delivery [provenance](02-diophantine-PROVENANCE.md) and
[build note](05-diophantine-rigidity-BUILD.md) describe their original packages
and filenames. Current build and verification paths are those above.
