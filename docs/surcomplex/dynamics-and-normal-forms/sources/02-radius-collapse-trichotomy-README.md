# Small Divisors in Surcomplex Dynamics

**A sharp common-domain linearization trichotomy**  
Research article prepared for Vladimir Reshetnikov, 21 September 2026.

## Contents

- `article.tex`: standalone LaTeX source, including its bibliography.
- `article.pdf`: compiled article.
- `code/verify.py`: standard-library-only exact algebraic verification.
- `data/verification.txt`: recorded output: 1,109 successful exact assertions.

## Main results

For an irrational unit multiplier lambda, let

    sigma(lambda) = limsup_n log^+(1 / |lambda^n - lambda|) / n.

Theorem 4.1 proves support-controlled nonlinear linearization for positive
Hahn perturbations of a rotation, allowing an infinitesimal change of the
multiplier. It preserves the original common ordinary disk when sigma = 0;
coefficient germs and entire coefficients when sigma is finite; and
polynomial coefficients for every nonresonant multiplier.

Theorem 5.2 is the exact obstruction. Work in the ordered value group
Gamma_* = Q + sqrt(2) Q and set u = t, v = t^sqrt(2). For

    F(z) = (lambda + u) z + v z^2 / (1 - z/R),

the coefficient of u^k v in the normalized formal linearizer has radius

    R exp(-(k+1) sigma(lambda)),  when sigma(lambda) > 0.

Thus positive finite sigma gives individually convergent coefficient germs
but no common neighborhood whatsoever. Infinite sigma can destroy even
coefficient-germ analyticity. Theorem 6.1 gives the resulting sharp universal
trichotomy. Theorem 10.3 extends the exact collapse and thresholds to
nonresonant diagonal unitary reductions in several variables.

The article also treats actual surcomplex halo evaluation, monad evaluation
without arithmetic hypotheses, simultaneous linearization of commuting
perturbations, and a quadratic critical-scale obstruction.

## Interpretation and limitations

These are Hahn-supported ordinary holomorphic coefficient functions, not
ordinary holomorphic families in complex parameters. Hahn summation is
coefficientwise and support-controlled, not a limit of partial sums.

The negative common-domain example uses two rationally independent positive
exponents and multiplier drift. The article does not claim to classify the
narrower fixed-multiplier problem or the some-common-neighborhood problem
for a fixed cyclic value group. It does not claim a global conjugacy on all
of No[i] at every spatial scale.

The exact radius-collapse statements and the category-sensitive nonlinear
trichotomy are proposed as new results. Priority is not independently
verified. Classical support lemmas, homological equations, formal
linearization, and known ordinary dynamical theorems are identified and
cited as such. No named published conjecture is claimed solved.

This is an AI-assisted, unrefereed research draft, not a proof-assistant
formalization. The exact finite checks test algebraic identities; they are
not proofs of the infinite theorems or the novelty claim.

## Build

With a standard TeX Live installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively run `pdflatex article.tex` until cross-references stabilize.
No external bibliography file, graphics, or custom font files are needed.

## Reproduce the finite checks

Requires Python 3.10 or later, with no third-party packages:

    python code/verify.py

The recorded run used Python 3.13.5. Arithmetic is exact in Q(i), implemented
using `fractions.Fraction`. The tests compare reciprocal-jet formulas,
reciprocal product identities, quadratic Schroeder identities, a nonlinear
mixed-forcing recursion, and several-variable reciprocal jets. They abort
on the first failed assertion.

## Repository provenance

The repository material consulted was pinned to:

    VladimirReshetnikov/Surreal
    commit 39f2be6667ade51bca2b45daa47e289d69c09764

The catalogue, the surcomplex analysis README, and the opening foundation
definitions were inspected. This does not represent a line-by-line audit
of every manuscript or every Lean file. No repository files were modified.
