# Dilation Rigidity of Surreal Numbers and Omnific Integers

**Research article, 23 September 2026.** Prepared with ChatGPT for Vladimir Reshetnikov.

## Repository placement

Placed in `21375f8`. Independent proof review and formalization are pending.

The current source is [article.tex](article.tex); the delivered PDF and
checksum list named below are not installed here. The verifier is
[code/verify.py](code/verify.py), with its recorded output and requirements
under [data/](data/). Build the current source as `article.tex` in a scratch
directory. To rerun the verifier, copy it to scratch first: it writes its
JSON output beside the script. The delivery description below retains the
original filenames and describes the author-side checks, not a new review.

## Contents

- `dilation_rigidity.pdf`: the 24-page article, with complete written arguments, examples, 12 further research questions, a dependency ledger, and references.
- `dilation_rigidity.tex`: self-contained LaTeX source; bibliography is embedded.
- `verify.py`: finite exact-arithmetic checks, not a proof of the infinite theorems.
- `verification_results.json`: the recorded successful verification run.
- `SOURCE_AUDIT.md`: repository snapshot, source scope, and novelty/verification boundaries.
- `requirements.txt`: exact version of the optional Python dependency used in the recorded run.
- `SHA256SUMS.txt`: checksums of these deliverables, excluding this checksum file itself.

## Main content

For an integer d >= 2, exponent dilation S_d fixes coefficients and multiplies normal-form exponents by d. It is NOT the operation y -> y^d.

Theorem 6.1 proves that a nonconstant characteristic-zero Hahn series y satisfying a nonzero constant-coefficient relation F(y,S_d y)=0 lies in a single cyclic Laurent-series subfield. It gives a ramification bound of deg_Y F, without assuming a divisible or Archimedean original value group.

Theorem 8.1 classifies negative-support solutions as polynomials in one monomial. Theorem 9.2 gives the sharp minimal relation degree and recovers the primitive monomial field. Theorem 10.1 specializes these conclusions to omnific integers and Gaussian omnific integers. In particular, infinite-support omnific integers are algebraically independent from each of their nonidentity integer dilates over the ordinary constant field.

Sections 7, 11, and 15 give finite profiles, coefficient descent, a Newton-weight existence test, rational-map classifications, and a decision procedure for nonconstant omnific solvability with exact algebraic-number input. The complete decision procedure is proved but NOT implemented by verify.py.

Section 13 shows the sharp change at order two and constructs elements of every finite autonomous algebraic order. Section 16 proposes twelve next research problems.

## Build the PDF

Install a reasonably complete TeX Live or MiKTeX distribution. Then run, in this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error dilation_rigidity.tex
```

Alternatively run `pdflatex dilation_rigidity.tex` repeatedly until references stabilize. No BibTeX run, shell escape, external image, or downloaded font file is needed. The required TeX packages are listed in the preamble; they are standard distribution packages, including newtx, amsmath, amsthm, mathtools, aliascnt, cleveref, tcolorbox, and hyperref.

The supplied PDF was compiled with pdfTeX 1.40.26 / TeX Live 2025-dev. Its final compilation had no LaTeX warnings or overfull/underfull boxes. All pages were rendered with Poppler for layout inspection; mathematical pages and references were also inspected at higher resolution. PDF text was checked for unresolved references and out-of-page text.

## Reproduce the finite checks

The script is written for Python 3.9+; the recorded run used Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify.py
```

It overwrites `verification_results.json` beside the script and prints the same report. All arithmetic is exact. The successful run includes:

- 6 inverse Böttcher expansions through degree 32;
- 20 resultant cases and 10 Jacobian instances;
- 45 finite telescoping identities, 4 Frobenius examples, and 6 Newton-weight tests.

Do not run Python with optimization flags that disable assertions when using this script for verification.

## Research status

This is an AI-assisted, unrefereed research draft. Complete written proofs are supplied, with classical dependencies explicitly identified. Novelty is proposed, not certified by an exhaustive literature review. No named published conjecture is claimed solved. The full Nishioka–Nishioka article could not be retrieved by the route used; its abstract-level scope is acknowledged. No proof in this package depends on an uninspected theorem from it.

No new Lean formalization is supplied, and no repository Lean build was performed. Finite computations are evidence about the checked examples, not formal verification of the infinite results. Independent mathematical review remains necessary.

## Repository relationship

Reviewed snapshot: `VladimirReshetnikov/Surreal` at
`b895e8672990e8b5a56f97dd7246f9dd5f86c771`.

The article credits the repository's existing monomial recognizer, difference-field framework, and formalization boundaries. Selected reports and the inventory were inspected; this is not a claim of line-by-line review of the whole repository. No repository files were changed.
