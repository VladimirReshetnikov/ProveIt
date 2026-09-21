# Hartogs Coherence, Finite Maps, and Residue Duality over the Surcomplex Numbers

A standalone research article extending the user-supplied
`surcomplex_analysis(3).tex`, prepared September 21, 2026.

## Files

- `surcomplex_research.pdf`: compiled article.
- `surcomplex_research.tex`: complete standalone LaTeX source, including bibliography.
- `verify_examples.py`: exact symbolic checks of the worked examples.
- `verification_report.txt`: the actual successful run of all 55 checks.
- `Makefile`: convenience build and verification commands.

## Principal results

Theorem 4.2 gives automatic joint Hahn coherence from separate coherence, using
an automatic common-support lemma and classical Hartogs separate holomorphy.

Theorem 5.2 gives matrix division on one fixed ordinary domain with explicit
Hahn support bounds. Theorem 5.3 and Corollary 5.4 give parameter preparation.

Theorem 6.1 treats coupled positive-Hahn perturbations of coordinate powers.
The quotient is finite free with the rectangular monomial basis, of rank equal
to the product of the coordinate degrees. All normal-form coefficients and
quotient witnesses have explicitly controlled supports on the original domain.

Theorem 7.3 identifies fiber factors with the formal local algebras of actual
infinitesimal roots and proves conservation of their total intersection
multiplicity.

Theorems 8.1 and 8.2 construct the coefficientwise multidimensional residue
functional and prove a perfect pairing through collisions. Proposition 8.3
constructs the trace element. Section 9 treats one-variable collision invariants
and lifted ordinary monodromy.

## Mathematical status

The article contains proofs, not just proposed statements. The exact
formulations were not located in the targeted literature search, but priority
has not been certified and the proofs have not been independently refereed or
formally verified. Classical ingredients and related published frameworks are
identified in the article. No independently documented classical open
conjecture is claimed solved.

The leading coupled systems covered in full detail are coordinate powers
(up to ordinary zero-free units), not arbitrary isolated complete intersections.
The residue duality is proved for the explicitly defined coefficientwise
functional; a universal comparison with other multidimensional residue
formalisms is not assumed. The results do not assert fine-topological properness
or construct a global transcendental theory on all surreal scales.

## Build

With a usual TeX Live installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_research.tex

Alternatively, run `pdflatex surcomplex_research.tex` repeatedly until the
references and table of contents stabilize. No BibTeX run or external image
files are needed. The original user-supplied manuscript is not required for
compilation.

## Reproduce the finite checks

Requires Python 3.10 or later and SymPy:

    python verify_examples.py

The script rewrites `verification_report.txt` only after all checks pass.
It checks exact finite identities, sine expansions to the reported orders,
and a finite Taylor-jet instance of matrix division. It does not verify the
general support theorems, transfinite recursion, or novelty claims.
