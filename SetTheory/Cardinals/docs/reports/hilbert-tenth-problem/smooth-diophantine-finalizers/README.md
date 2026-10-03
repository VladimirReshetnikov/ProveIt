# Smooth Everywhere, Universal on the Integers

**Canonical quartic certificates with five extra variables, no local obstruction,
and explicit Jacobian identities.** Research prepared for Vladimir Reshetnikov's
ProveIt program, 2 October 2026.

## Main result

For integer polynomials f_i(x) of degree at most two, let q_i(x,t) be their
homogeneous quadratic lifts and put H = sum_i q_i^2. The compiler produces

    F = H + (t*u - 1)^2
          + (2*z1^2 - z1) + (2*z2^2 - z2) + 2*(2*z3^2 - z3).

This is an exact quartic with five additional variables. Its natural zeros are
in bijection with the source natural zeros; its integer zeros are two
sign-related copies of the source integer zeros. Its affine scheme is smooth
over Z, with geometrically integral fibres. An integral identity of degree at
most seven certifies smoothness. Every instance has a constructible nonnegative
dyadic point, integral points at every prime, and rational points dense in its
real locus. The real locus has exactly two path components.

The paper also proves a sharp auxiliary-count result within the positive
weight-four guard family. The smaller weighting (1,3) remains smooth but can
have no dyadic point. The successful weighting (1,1,2) uses the unit residual as
one coordinate of the universal quadratic form with weights (1,1,2,2).

General smooth-variety undecidability is known, and is credited to Poonen. The
proposed contribution is this explicit combined normal form and its proofs.
Publication priority for the exact combination has not been established.

## Contents

- `article.pdf`: 28-page research article, including proofs and ten research questions.
- `article.tex`: self-contained LaTeX source with an inline bibliography.
- `code/smooth_compiler.py`: validated quadratic finalizer, Jacobian identities,
  dyadic point constructor, and compatible 2-adic residues.
- `code/counter_frontend.py`: bounded natural-number counter-machine frontend.
- `code/verify.py`: exact symbolic, exhaustive, and seeded checks; regenerates examples.
- `examples/countdown_T3.json`: a 29-variable, 97-monomial quartic; 24 source
  variables, 28 residuals, input counter 2, horizon 3, and exact witnesses.
- `examples/inconsistent.json`: constant inconsistent source with one unused
  source coordinate, plus its dyadic and local data.
- `verification/results.json`: full breakdown of **21,128 successful assertions**.
- `verification/run.log`: captured successful test output.
- `RESEARCH_STATUS.md`: proved claims, known background, and scope limits.
- `SOURCE_AUDIT.md`: repository and literature provenance.
- `SHA256SUMS`: hashes of the package files, excluding the checksum file itself.

## Reproduce

Python 3.10 or later is required. The recorded run used Python 3.13.5 and SymPy
1.14.0. The compiler has no network requirements.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

For the PDF, use a normal TeX Live installation with pdfLaTeX and the packages
listed in the source. Either `make pdf` or:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The three passes resolve the table of contents and references from a clean
build. `latexmk -pdf article.tex` is another option.

## Important contracts

All frontend witnesses are natural numbers, including zero. Residuals are
integer polynomials. Changing a natural domain to unrestricted integers can
invalidate the frontend's semantics even though the algebraic finalizer's
integer correspondence remains valid.

The bounded counter frontend has an externally chosen horizon. It does not
compress a variable-length execution into a fixed number of witnesses. The
unbounded undecidability corollary separately uses established MRDP and unique
arithmetic-circuit lifting.

The dyadic constructor's four-square search is capped at one million by default
to avoid unanticipated allocations. The existence theorem has no such cap.
The caller can supply a four-square decomposition for exact checking.

The source is a research reference implementation, not a general Diophantine
solver. No Lean/Coq formalization, repository-wide build, peer review, or
universal operation-count improvement is claimed.
