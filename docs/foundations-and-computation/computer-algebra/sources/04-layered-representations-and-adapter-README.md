# Surreal and Surcomplex Numbers in Symbolic Computer Algebra

A 40-page mathematical and software-design article, prepared September 21,
2026, with standalone LaTeX source, a compiled PDF, and a small executed
Wolfram Language demonstration.

## Main files

- `surreal_surcomplex_cas.pdf`: the article.
- `surreal_surcomplex_cas.tex`: complete source, including bibliography.
- `SurrealCASCore.wl`: exact sparse arithmetic and rational-expression prototype.
- `TestCore.wls`: executable Wolfram Language test harness.
- `wolfram_test_report.txt`: provenance and result of the actual kernel run.
- `verify_examples.py`: exact finite checks of the mathematical examples.
- `python_verification_report.txt`: the generated Python/SymPy check report.
- `requirements.txt`: the SymPy version used for those checks.

## Scope of the article

The article distinguishes finite exact denotation, effective coefficient access,
decidable equality and order, and certified approximation. It develops an
ordered rational-monomial core and a mathematically effective real-algebraic
closure, then considers certified Hahn series, formal germs, ordinary analytic
lifts, Hahn-coherent functions, and explicitly selected transserial extensions.

Topics include computability obstructions, well-ordered supports, finite grid
coefficient extraction, high-rank precision, algebraic root selectors, Newton
profiles, Hensel lifting, root-error bounds, finite quotient algebras, residues,
composition, differentiation, integration, and global exponential/logarithmic
semantics. Wolfram Language's documented representations and the proposed
extension architecture are kept distinct.

The three supplied manuscripts are cited as research sources, not treated as
independently refereed or formally verified publications. The fourth global
manuscript mentioned inside one input was not supplied and is not used as an
independently inspected source. No input manuscript is needed to compile the
article.

## What the prototype actually supports

`SurrealCASCore.wl` handles finite sums with exact Gaussian-rational coefficients
and rational exponent vectors of one fixed positive rank, ordered
lexicographically. The interpretation of a vector (q1,...,qr) is the surreal
exponent q1*omega^(r-1) + ... + qr. The Hahn monomial at exponent gamma is
omega^(-gamma), in the Conway omega-map convention.

Implemented operations are construction/normalization, addition, negation,
multiplication, nonnegative integer powers, conjugation, valuation, leading
coefficient, and real comparison. Fraction wrappers add exact fraction
arithmetic, inversion, valuation, and equality by cross multiplication.

The finite-sum representation is canonical within this small domain. Fraction
wrappers are not gcd-normalized: use `REqual`, rather than structural wrapper
equality, to compare their values. Constructors reject inexact coefficients,
invalid exponent data, and zero denominators. Real comparison rejects nonreal
inputs.

The package does NOT implement arbitrary surreal cuts, algebraic coefficient
extensions, algebraic root isolation, infinite series generators, general
Hahn-coherent functions, or transseries. Most interfaces in the architecture
section of the article are proposals, not functions exported by this package.
There are no modifications to System`Plus, System`Times, System`Power,
System`Infinity, or the host's numerical predicates.

## Run the checks

With Wolfram Language available:

```text
wolframscript -file TestCore.wls
```

The harness loads the package from its own directory. Its recorded execution
used Wolfram Language 15.0.1 for Linux x86 (64-bit), dated July 2, 2026.
All 110 checks passed: 20 deterministic checks and 90 seeded property checks.
The actual package and harness files were loaded, not merely transcribed into
separate pseudocode. See `wolfram_test_report.txt` for execution provenance.
Other Wolfram versions and Mathics were not tested.

With Python and SymPy available:

```text
python -m pip install -r requirements.txt
python verify_examples.py
```

The recorded run used Python 3.13.5 and SymPy 1.14.0. All 69 checks passed.
The script regenerates `python_verification_report.txt` beside itself and fails
if an assertion fails. It checks finite algebraic formulas and specified
truncation orders; it does not decide arbitrary infinite-support questions.

These runs are reproducible example and implementation checks, not formal
proofs of the general mathematical theorems.

## Build the article

```text
latexmk -pdf surreal_surcomplex_cas.tex
```

Alternatively, run `pdflatex` repeatedly until references stabilize. The source
uses standard TeX Live packages, an internal bibliography, and no external
images. The delivered PDF was compiled from this source. The final compilation
had no unresolved citations/references or overfull/underfull box warnings.
All pages were visually surveyed; selected pages were additionally rendered
with Poppler for inspection.

## Important semantic boundaries

Exact infinite values need not have finite explicit cutoff expansions. Strong
Hahn summability is not ordinary real-parameter convergence or convergence in
the full surreal fine topology. A mathematical existence theorem need not be
an algorithm on unrestricted finite program input. Conway monomials are not
generic exponential powers at arbitrary surreal exponents. Global surcomplex
transcendental functions require declared extension and branch conventions.
The article makes these distinctions part of the proposed interfaces.
