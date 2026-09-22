# Differential Algebra of Surreal and Surcomplex Numbers

**Differential Hahn workspaces, bounded phases, logarithmic derivatives, and
oscillation obstructions**

A standalone 25-page article prepared for the documentation of
VladimirReshetnikov/Surreal, at commit
`e260237db9b71da8b74a0c13c8e6355119091100`.

## The gap

The existing trigonometry report explicitly leaves scalar-field derivations
outside its scope; the foundations report requires those derivations to be
separated from analytic and pointwise derivatives. This article connects the
Berarducci–Mantova derivation to the repository's finite phases and common-domain
Hahn coefficient calculus. The review is targeted, not an exhaustive absence
search. Details and pinned source links appear in `REPOSITORY_AUDIT.md`.

## Main mathematical content

Writing O for the finite real surreal numbers, D for the chosen derivation,
and SC = No[i], the central identity is

    { D(y)/y : y in SC, y != 0 } = No + i D(O).

Thus `D(y) = (a+i*b)y` has a nonzero solution precisely when b has a **finite**
primitive. The purely infinite part of a primitive gives a canonical obstruction
and a complete multiplicative-gauge classification of rank-one equations.
For nonzero rational b=P/Q, the criterion is simply `deg(Q)-deg(P) >= 2`.

The article also proves a countable-stage construction of differentially stable
set-sized full Hahn workspaces; finite-phase derivative compatibility; the
convexity and other structure of the finite-primitive subgroup; complete
constant-coefficient solution-space and constant-matrix classifications; an
explicit oscillatory Picard–Vessiot extension with no new constants; and the
commutation and total-chain-rule interfaces for common-domain analytic Hahn
families.

In particular, `D(y)=i*y` and `D(D(y))+y=0` have only the zero solution inside
SC with this derivation, despite algebraic closedness and surjectivity of D.
No globally compatible complex exponential can remove this obstruction.

## Contents

- `article.tex` — standalone LaTeX source with internal bibliography.
- `article.pdf` — 25 pages, including title, contents, 14 sections, 2 appendices,
  and references; 32 numbered theorem/proposition/lemma/corollary statements
  (one is the explicitly imported Berarducci–Mantova theorem).
- `REPOSITORY_AUDIT.md` — scope of the gap review, pinned sources, and attribution.
- `code/verify_examples.py` — restricted rational-phase classifier and exact
  finite symbolic checks.
- `data/verification.json` — individual results and software versions.
- `data/build_report.json` — build, pagination, warning, and layout record.
- `requirements.txt` — SymPy version used for the recorded checks.
- `build.sh` — optional PDF build script.

## Rebuild and reproduce

The PDF requires a LaTeX installation with pdfLaTeX and the packages listed in
the source preamble. No external bibliography, graphics, or shell escape is
needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `sh build.sh`; if latexmk is unavailable, it uses three
pdfLaTeX passes. On Windows the latexmk command can be run directly.

The verification script was executed under Python 3.13.5 with SymPy
1.14.0 and passed **149/149 checks**. Its report records the exact run time.
The article is dated September 21 in Pacific time; the execution timestamp is
in UTC and may therefore show September 22.

```sh
python -m pip install -r requirements.txt
python code/verify_examples.py
```

A nonzero process exit code means at least one finite check failed. The script
writes `data/verification.json`; an alternative path can be supplied using
`--output`. It can also be imported to call
`classify_rational_phase(expr, variable)`. Inputs are trusted SymPy expressions
in Q(variable); nonrational coefficients and unsupported functions raise an
exception rather than being classified as mathematical nonexistence.

## Attribution and verification boundaries

The existence, strong additivity, exponential compatibility, constant field,
normalization, and surjectivity of the selected derivation are imported from
Berarducci and Mantova. Standard Hahn-field and positive-support summability
facts are likewise attributed. The article gives full human-readable arguments
for the ensuing constructions and classifications; no claim of novelty or
priority is made.

The 149 checks establish only the displayed finite algebraic and differential
identities and the behavior of the restricted routine. They do not construct
surreal numbers, verify strong summability, or formally prove any general
proper-class theorem. No Lean implementation or kernel-checked proof is
claimed. The repository itself was not modified.

The final PDF builds with no LaTeX errors, unresolved references or citations,
PDF destination warnings, or overfull/underfull boxes. Every page was rendered
for layout review, and the appendix heading was kept with its table.
