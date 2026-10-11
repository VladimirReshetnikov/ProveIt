# Scope and antecedents of the harmonic Laurent section

The source audit uses the ProveIt commit
`e0d9463bdee9685dfb1dddb819059cc738540c57`. It is a targeted audit, not a claim
to have checked every historical repository artifact or all literature.

## Repository antecedents inspected

- `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex` already
  develops elementary symmetric harmonic coefficients, a shifted
  **alternating** harmonic family, incomplete-beta reflection and
  cyclotomic realizations. These mechanisms are established background.
- The full archived
  `Analysis/Polylogarithms/docs/reports/alternating-harmonic-polylogarithms/article.tex`
  was additionally retrieved at the pinned commit and its Git blob hash
  checked as `48b47e1e6800cfd0d6062f62745b3f70c98484d5`. Its exact reflection
  compiler and rational residue filters cover the same classical mechanisms
  used as background in the positive-value part of the present section.
- The archived
  `Analysis/Polylogarithms/docs/reports/lerch-global-phase/continuations/harmonic-order-geometry/sections/harmonic_order.tex`
  was retrieved and its Git blob hash checked as
  `6e8df6ec065e775a63d9865b89444b25ce93e104`. In particular,
  `sorder:prop:entire` and `sorder:cor:negative-values` already use Mellin
  Taylor subtraction and reciprocal-Gamma zeros to evaluate an alternating
  depth-one odd-denominator harmonic interpolation at negative integers.
  Its kernel is analytic at the origin, and the continued function is entire.
- The manuscript's `08-differentiation.tex` already identifies its all-order
  Stieltjes derivative ladder as Coffey's result in elementary harmonic
  coordinates. Replacing the Hurwitz zeta factor by the shifted harmonic
  family gives the extended spectral ladder in the present section, with
  that mechanism retained as background.
- The pending archive extracted as
  `polylogarithm_stieltjes_continuation` was inspected for harmonic, Gamma,
  Laurent, and finite-part overlap. Its critical-cutoff finite parts concern
  a different Lerch/Lambert asymptotic problem. They are not spectral Laurent
  finite parts of the nonalternating harmonic family studied here.

The new continuation proposed for repository integration is specifically
the nonalternating outer-shift family

\[
 E_r(s;a)=\sum_{n\ge1}\frac{e_r(n-1)}{(n+a)^s},
\]

with all depths retained, all principal coefficients and finite parts at
every nonpositive integer, and the finite-part shift calculus. Its local
Mellin kernel has logarithmic singularities; the reciprocal-Gamma zero
reduces their pole order rather than cancelling every singularity. This
full outer-shift Laurent statement was not located in the inspected
repository sources. The mathematical proof is independent of that
negative search result.

## Literature boundary

The positive-integer beta-derivative evaluations are included in Paul
Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
Integers 26 (2026), A81, DOI `10.5281/zenodo.20931235`. They are explicitly
treated as an established baseline, not a new theorem of this package.

Young's *Series of Height One Multiple Zeta Functions*, Integers 24 (2024),
A43, DOI `10.5281/zenodo.11221606`, supplies the complex Barnes-order
framework. His earlier *Global series for height 1 multiple zeta functions*,
European Journal of Mathematics 9 (2023), article 99,
DOI `10.1007/s40879-023-00695-0`, explicitly treats unshifted Laurent
expansions and singular parts. The latter publisher abstract and metadata
were verified; its subscription full text was not obtained in this audit.
Consequently no global priority claim is made for the unshifted or shifted
Laurent formulas.

The harmonic Hurwitz functions in Kargin, Dil, Cenkci and Can,
*On the Stieltjes constants with respect to harmonic zeta functions*,
J. Math. Anal. Appl. 525 (2023), 127302,
DOI `10.1016/j.jmaa.2023.127302`, include shifts of inner harmonic
denominators. The present outer-denominator shift must not silently be
identified with that different convention.

## What the verification establishes

`harmonic_coefficients.py` checks the finite coefficient rules exactly over
a polynomial ring containing formal Euler and zeta constants. Its checks
include defining-series coefficients, Bernoulli values, differentiation,
reflection, antiderivatives, multiplication at two moduli, and the displayed
nonlinear odd-denominator sums.

`harmonic_mellin_numeric.py` evaluates the continued function through a
separate scalar local logarithmic expansion and global quadrature. It tests
three unshifted negative Laurent points and one nonzero shift. The observed
linear remainder after subtracting the principal and constant terms is a
floating-point diagnostic, not a certified error bound. The independent
analytic review checks that the subtracted holomorphic remainder cannot
contribute through the constant coefficient at a nonpositive integer.

The residue term in differentiating finite parts is a necessary mathematical
correction to a tempting general manipulation. The section does **not**
allege that any inspected repository source actually makes that mistake.
