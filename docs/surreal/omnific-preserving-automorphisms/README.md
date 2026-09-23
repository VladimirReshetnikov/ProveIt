# Omnific-Preserving Automorphisms

## Article

**Convex-scale stabilizers, definable constants, and nondefinable monomials**  
Research draft prepared for the Surreal project, September 23, 2026.

The self-contained LaTeX source and its compiled PDF are included. The article
contains complete written proofs of the proposed additional results, while
explicitly attributing imported normal-form, summability, exponential-logarithm,
and Pell-rigidity ingredients. The bibliography and provenance ledger are in
the article.

### Main results

* An exact convex-subgroup criterion for a contracting strong Hahn derivation
  to preserve the nonpositive-support ring, equivalently for its exponential
  to preserve the omnific-type integer part.
* Triviality of the coefficient-fixing strong 1-automorphism stabilizer exactly
  in Archimedean rank one. In finite ordered rank r, a sharp derived-length
  bound r-1, including a separate proof of sharpness for the abstract group.
* Parameter-free recovery of the ordinary real constants and zero-cut
  truncation from the pair (No, Oz), with a set-sized real Hahn-field analogue.
* Failure of definability of Conway monomials after naming any set of
  parameters; more strongly, no definable rule can select a representative
  of each natural-valuation class.
* Common fixed field R; faithful parameter-fixing actions of R^kappa for
  every set cardinal kappa; nonsolvable pointwise stabilizers of every set.
* Surcomplex extensions preserving conjugation and Gaussian omnific integers,
  with a parameter-free definition of the ordinary complex constants.

### Scope

The logarithmic classification requires strongness and coefficient fixing;
for the real pair, coefficient fixing follows from a separate definability
argument. It does not classify all nonstrong pair automorphisms. The explicit
shears are plain-field automorphisms, not exponential-field automorphisms.

For full surreal classes, actions are encoded by individual class relations;
no set or NBG class of all class-function graphs is asserted. Each series and
each parameter-support construction uses set-sized supports.

This is an unrefereed research draft. No exhaustive historical priority claim,
newly settled named longstanding conjecture, or Lean verification is asserted.
The paper identifies the results proposed as additional contributions and
provides the arguments so that they can be independently reviewed.

## Files

- `omnific_automorphisms.tex`: complete source, with bibliography embedded.
- `omnific_automorphisms.pdf`: compiled 25-page article.
- `verify_finite_identities.py`: exact finite checks, Python standard library.
- `verification_output.txt`: output from the included program's actual run.
- `Makefile`: optional build, check, and cleanup targets.
- `README.md`: this file.

## Rebuild

Use a standard LaTeX installation with pdfLaTeX and the usual mathematical
packages, including `lmodern`, `microtype`, `amsmath`, `amsthm`, `aliascnt`,
`hyperref`, and `cleveref`. There are no external figures, font files, or
bibliography databases to download.

```sh
pdflatex -interaction=nonstopmode -halt-on-error omnific_automorphisms.tex
pdflatex -interaction=nonstopmode -halt-on-error omnific_automorphisms.tex
pdflatex -interaction=nonstopmode -halt-on-error omnific_automorphisms.tex
```

The first pass creates reference data; subsequent passes resolve the table of
contents, cross-references, and citations. Alternatively, run `make` where
GNU Make or a compatible implementation is available.

## Run the finite verification

Python 3.10 or later is sufficient; no third-party Python modules are needed.

```sh
python3 verify_finite_identities.py
```

The program exits unsuccessfully if any assertion fails. It uses exact rational
arithmetic to test the product rule and bracket identity, balanced derived-series
recursions, independent-parameter group-commutator coefficients, shear iterates,
finite exponential identities, the rank-one support escape, and Pell solutions.
These finite tests are not proofs of arbitrary Hahn summability, class-theoretic
claims, or the whole article.

## Repository comparison

The targeted review is pinned to Surreal commit:

`fb5c4b530e3ec04b5661347d51d5382526d5aa02`

The reviewed material includes the project catalogue, the omnific Diophantine
manuscript's scope and results, and the surcomplex field automorphism
manuscript's structural conventions and literature discussion. It is not a
line-by-line audit of the entire repository. The article's main external
operator reference is arXiv:2403.05827v2; the surreal class extension is cited
to arXiv:2509.22374v3 (April 23, 2026).
