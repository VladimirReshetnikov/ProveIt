# Surquaternions
## Algebra, Geometry, Valuation, and Controlled Analysis

A standalone research exposition prepared in response to Vladimir Reshetnikov's request,
dated September 21, 2026. The PDF has 34 pages, including the title page, contents,
appendices, and references. It contains 27 numbered theorem/proposition/lemma/corollary
statements with proofs, as well as worked examples and implementation guidance.

## Files

- `article.pdf` — the typeset article, with clickable contents and references.
- `article.tex` — standalone LaTeX source, with its bibliography included inline.
- `code/verify.py` — exact finite symbolic checks, using SymPy.
- `data/verification.json` — recorded results: 69 of 69 check groups passed,
  comprising 252 scalar identities.
- `data/source_manifest.json` — repository snapshot and principal research sources.
- `data/build_and_validation.json` — build, PDF, and check metadata.
- `requirements.txt` — the version of SymPy used for the recorded run.
- `SHA256SUMS.txt` — checksums of the deliverable files other than itself.

The source needs no external bibliography database or illustration files. Standard
LaTeX packages and fonts are required; no font files are distributed in this archive.

## Main content

The article develops the Hamilton division algebra over the surreal numbers, complex
slices and conjugacy spheres, quaternion-valued Hahn normal forms, valuation and
standard part, exact rotation geometry, one-sided polynomial roots and multiplicity,
Hermitian spectral theory, and a quantitative multiscale spectral-projector estimate.

The analytic development separates infinitesimal Hahn exponentials and logarithms,
canonical finite angles, the global Ehrlich–Kaplan normalization, the componentwise
Berarducci–Mantova derivation, and common-domain coefficientwise slice/Fueter analysis.
In particular, it proves a no-oscillation result for that derivation and the resulting
obstruction to a global commuting exponential chain rule.

## Build the article

With a standard TeX Live or MiKTeX installation and latexmk:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run the following command twice, and a third time if LaTeX requests a
rerun for cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The final supplied build had no LaTeX errors, undefined references or citations,
overfull boxes, or underfull boxes. The PDF was rendered and inspected.

## Run the symbolic checks

Python 3.9 or newer is required.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

An alternate output path can be supplied:

```sh
python code/verify.py --output data/verification-rerun.json
```

The script exits with a nonzero status if any check fails. All arithmetic is exact;
there is no floating-point simulation of an infinitesimal in the checks.

## Mathematical and verification status

This is not a refereed article or a claim of bibliographic priority. Classical algebra,
surreal foundational inputs, and classical slice/Fueter results are attributed. Derived
results are proved in the article; the general theorems have not been formally checked.

The symbolic suite checks algebraic identities and finite formal expansions. It does
not construct the surreal numbers, prove the Hahn support lemma, verify the entire
Berarducci–Mantova construction, or establish every analytic or spectral theorem.
No Lean verification or successful build of newly added Lean modules is claimed.

The distinction between the topology of the full surreal class and the intrinsic
topology of a set-sized Hahn workspace is essential. The article's summations are
strong Hahn sums unless an ordinary coefficient operation is explicitly specified.
The different exponentials and derivatives are intentionally not identified.

## Repository baseline

Repository: `https://github.com/VladimirReshetnikov/Surreal`

Inspected snapshot: `39f2be6667ade51bca2b45daa47e289d69c09764`.

The article is a new companion to that snapshot. No repository changes were made.
The repository's prior AI-assisted reports are treated as context, not as independent
verification of all their claims. Primary literature is listed in the article.
