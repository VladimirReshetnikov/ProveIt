# The Universal Set-Sized Quotient of the Omnific Integers

**Cardinal thresholds, surcomplex representations, and homological obstructions**  
Research article prepared for Vladimir Reshetnikov, 22 September 2026.  
Author: OpenAI ChatGPT. The compiled article has 25 PDF pages.

## Main results

Let `Oz` be the omnific integers, `I` the ideal of normal forms supported
at strictly positive exponents, and `c0 : Oz -> Z` the constant-coefficient
map. The principal theorem proves that every unital ring map from `Oz`
to a set-sized ring `S` is exactly `x |-> c0(x) 1_S`. Every set-sized
unital `Oz`-module is consequently an ordinary abelian group with this
forced scalar action. The Gaussian variant has universal quotient `Z[i]`.
No preservation of infinite sums is assumed of the homomorphism.

For every uncountable regular cardinal kappa, the article constructs an
explicit set-sized integer part `R_kappa = Z + I_kappa` inside a real-closed
surreal Hahn subfield. Targets with fewer than kappa elements cannot detect
`I_kappa`. Under the additional hypothesis `kappa^{<kappa} = kappa`, the
minimum cardinality of a ring or module detecting any specified nonzero
element of this ideal is exactly kappa.

The ideal `I_kappa` is flat and idempotent but nonprojective. With
`D = R_kappa / I_kappa = Z`, the quotient has flat dimension one and
projective dimension at least two. Extension groups between inflated
`D`-modules agree with their extension groups over `D`. Nevertheless,
explicit larger modules detect nonzero extensions from `D` in degrees
one and two; under the same cardinal-arithmetic hypothesis, the exact
minimum size of such a coefficient module is kappa in both degrees.
All tensor products, resolutions, Tor, and Ext in this argument are over
set-sized rings, not proper-class rings.

Applications include classification of all set-sized omnific quotient
rings, Gaussian matrix representations, and a nonzero prime quotient
with no nonzero set-sized unital representation. The primality of
`omega^(sqrt(2)) + omega + 1` used in the last application is an imported
theorem of L'Innocente and Mantova, not a new claim of this article.

## Files

- `article.tex`: standalone LaTeX source, including its bibliography.
- `article.pdf`: the compiled 25-page article.
- `verify.py`: exact finite checks using Python's standard library.
- `verification.json`: recorded output, with 17,586 assertions passing.
- `source_audit.md`: inputs, repository comparison, and novelty limitations.
- `build_audit.json`: build, rendering, and integrity record.
- `Makefile`: build, check, and auxiliary-file cleanup commands.

## Reproduction

Use a TeX distribution with `latexmk`, `pdflatex`, and the packages listed
in the source preamble. No external bibliography processor is required.

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
python3 verify.py
```

Alternatively, run `make` and `make check`. Run `make clean` to remove
auxiliary TeX files without removing the PDF. Without `latexmk`, run
`pdflatex -halt-on-error -interaction=nonstopmode article.tex` repeatedly
until references and contents stabilize. The check program requires
Python 3.10 or newer and no third-party packages.

## Evidence and status

Full mathematical proofs are provided for the proposed new results, with
standard inputs cited separately. The finite checks cover algebraic
identities and explicit matrix blocks, not class-size arguments, infinite
Hahn support existence, primality, or derived-functor statements. They
are not a Lean formalization or a substitute for the proofs.

This is an AI-assisted research draft, not a refereed or formally verified
paper. The main quotient theorem and the cardinal/homological package are
proposed original results: no identical statements were found in the
material inspected. The repository comparison and literature search were
targeted, not exhaustive, and do not establish priority. No named open
conjecture is claimed to be resolved. See the source audit and the article's
boundary section for exact qualifications.
