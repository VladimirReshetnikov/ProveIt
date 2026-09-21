# Surcomplex Analysis
## Hahn Summation, Analytic Germs, and a Residue Calculus

21 September 2026

This archive contains a 30-page mathematical article developing a specified
analytic framework over the surcomplex class field **S = No[i]**. It includes
proofs, counterexamples, worked expansions, an explicit dependency audit, and
a bibliography of foundational and related work.

## Files

- `surcomplex_analysis.pdf`: the compiled article, with linked contents and references.
- `surcomplex_analysis.tex`: the complete, editable LaTeX source. The bibliography
  is included in the source; no separate BibTeX file is needed.
- `verify_examples.py`: four groups of exact finite symbolic checks.
- `verification_output.txt`: the output of an executed, successful verification run.
- `build.py`: a cross-platform PDF build helper, with optional example verification.
- `requirements.txt`: the Python dependency for the example checks.
- `README.md`: this guide.

No external illustrations, proprietary fonts, or downloaded research papers are
needed to build the article.

## The analytic framework

The construction has two levels. Local formal series with surcomplex
coefficients become analytic germs through Hahn summation at increments small
enough relative to their coefficient field. To obtain global continuation and
zero-counting results, the article then uses well-ordered Hahn families of
ordinary holomorphic coefficient functions on a connected complex domain.

For a set-sized divisible ordered subgroup Gamma of No, the coefficient field
is C((t^Gamma)). A family

    F(z) = sum_gamma f_gamma(z) t^gamma

is evaluated by Taylor expansion on the finite tube U^sharp: the surcomplex
points with standard part in the ordinary domain U. Every support is a set,
and the proofs control both well-ordering and the number of contributions at
each exponent. Arbitrary ordered rank is allowed.

The notation t^gamma means the Conway monomial omega^(-gamma). It is not
silently identified with the value of a different surreal exponentiation
convention. A Hahn sum is not a limit of its partial sums in the full surreal
topology.

## Main results

The central sequence of results is support-controlled Weierstrass preparation
(Theorem 9.1), division (Theorem 9.3), exact specialization of zeros
(Theorem 10.1), and a residue theorem for actual surcomplex poles
(Theorem 11.2).

If the leading holomorphic coefficient has a zero of multiplicity m at an
ordinary point a, the evaluated family has exactly m zeros in the infinitesimal
neighborhood of a, counted with multiplicity. Those zeros may split and move
through multiple surreal scales. Their standard-part pushforward recovers
exactly the zero divisor of the leading function.

Coefficientwise contour integration is then proved to recover the residues
at the actual displaced poles. This yields Cauchy's integral formula, the
argument principle, and two Rouché comparisons. Other sections establish
identity, open-mapping, maximum-modulus, primitive, Morera, and linear-system
results under explicit hypotheses; formal residue invariance and Lagrange
inversion; and exact Schwarz–Pick inequalities for canonical classical lifts.

The paper also proves a finite-angle description of the surcomplex unit
circle, an obstruction to a global exponential with exactly the classical
kernel, and the existence of distinct globally defined, locally Hahn-analytic
exponentials agreeing on the real-surreal axis and on all finite complex
arguments. Scale charts carry the zero and contour theorems to infinite
centers and infinitesimal or infinite radii.

## Important scope distinctions

The full fine topology, coefficientwise holomorphic coherence, and classical
complex topology are different structures. A bounded locally analytic
function on the whole class field need not be constant. Even a coherent
family bounded by one surreal constant on the finite plane need not be
constant: t*z is an example. The Liouville result therefore uses boundedness
of each ordinary coefficient function instead.

The tube D^sharp is not the whole surcomplex unit ball. Arbitrary
infinitesimal deformations of disk maps do not satisfy the canonical-lift
Schwarz–Pick theorem. Contours are classical coefficientwise contours and
specified admissible pullbacks, not unspecified order-topological Riemann
integrals.

The article develops one explicit framework; it does not claim a uniquely
forced global analytic geometry, priority for its constructions, or formal
machine verification. Imported foundational theorems are identified in the
appendix. The surcomplex statements are proved from those inputs.

## Rebuilding the PDF

Install a TeX distribution providing `pdflatex` and the standard packages used
in the preamble. `latexmk` is preferred but not required. In the extracted
archive directory, run:

    python build.py

The helper uses `latexmk` when available; otherwise it runs `pdflatex` three
times to resolve the contents and cross-references. Direct compilation is also
possible:

    latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_analysis.tex

The build does not require Python packages beyond the standard library. It
creates the usual TeX intermediate files locally.

## Reproducing the exact checks

With Python 3.9 or later:

    python -m pip install -r requirements.txt
    python verify_examples.py

Or rebuild and check together:

    python build.py --verify

The four groups check:

1. The inverse series rho(s) exp(-rho(s)/2) = s through degree ten,
   along with the original equation rho(s)^2 = s^2 exp(rho(s)).
2. The prepared quadratic for z^2 - t exp(z) through t^3, independently
   from its roots and from the preparation recursion.
3. Zero residues of the positive-order logarithmic-derivative coefficients
   through t^8.
4. The two displayed corrections for z^2 - t - q exp(z), with q = t^omega,
   as symbolic coefficient identities modulo q^3.

All four groups passed. Rational polynomial computations use exact fractions;
SymPy expressions are exact as well. No floating-point tolerances or numerical
root finding are used. These are finite consistency checks, not a surreal
number implementation or a formal verification of the general proofs.
