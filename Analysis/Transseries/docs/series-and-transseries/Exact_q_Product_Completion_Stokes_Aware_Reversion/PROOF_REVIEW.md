# Internal proof review

Date: 4 October 2026.

This is an internal mathematical and computational audit, not an independent
referee report, a Lean proof certificate, or a priority determination.

## 1. Exact completion rather than asymptotic matching

The original shifted product is represented by a Mellin integral on a line to
the right of 1. Moving the contour to `-c`, with `1 < c < 2`, extracts exactly
the elementary core. The Riemann and Hurwitz functional equations split the
remaining integral into a cosine term and a sine-cotangent term. The cosine
term is the convergent dual product. The sine-cotangent term is the Borel
median. Thus the exponentially small term is proved by an exact equality; it
is not guessed from numerical errors or from pole residues alone.

The principal-value scalar kernel is treated by subtracting the numerator at
the pole. The infinite kernel sum is first integrated on a nonreal ray, where
absolute convergence is available, and only then deformed term by term. This
avoids an invalid unqualified use of Tonelli's theorem for principal values.

## 2. Signs, branches, and endpoints

The upper lateral path passes above a pole and contributes a clockwise
semicircle. Consequently the upper-minus-lower jump has a minus sign. The
upper Borel sum pairs with the negative-phase dual product; the lower sum
pairs with the positive-phase product. An appendix records this convention.

The dual products begin at the factor involving Q, not at the factor involving
Q^0. Removing the zero-th factor gives the logarithmic constants needed for the
comparison with Conjecture 5 in the cited version. The indices `1 <= k < N`
are distinguished from the degenerate endpoint, where `log(1-1)` must not be
used. The eta endpoint is handled separately.

All initial exact identities use real shifts and Re(t)>0. Complex parameter
extension near the q-gamma critical point is justified by a different,
parameter-holomorphic Borel kernel; the real Fourier sine series is not
silently applied to nonreal shifts.

## 3. Reflection and cancellation

The two classifications use divisor inversion followed by a finite Vandermonde
system on distinct nonzero phases. The self-reflecting shift 1/2 is included.
Weights may be complex; reflection is not complex conjugation. The finite-phase
bounds are not claimed for unrestricted infinite sets of shifts.

The flat eta combination cancels the entire finite elementary core, not only
the divergent tail. It therefore gives a genuine example with zero full
power-logarithmic expansion and a nonzero exact value.

## 4. Inverse domains and convergence

The formal contraction lemma explicitly assumes completeness, separation, and
a filtration-raising operation. It does not automatically apply to every
possible Hahn or complex transseries construction.

The analytic inverse theorem assumes a selected univalent chart and a target
disk with a boundary separation bound. Rouche's theorem counts one zero with
multiplicity, which ensures simplicity as well as existence. Cauchy bounds
supply a convergent amplitude series and a quantitative tail estimate.

The expansion in exponential amplitudes can converge even when the
power-series expansion of its coefficient functions diverges. These two
notions of convergence are not conflated. General resurgent closure is a
credited established input, not a newly proved universal theorem.

The inverse Stokes map is a compositional inverse cocycle. It is not obtained
by negating the forward jump. Arithmetic averaging of two inverse branches
is not identified with inversion of the arithmetic-average carrier.

## 5. Regular q-cusp scales

The target action 24 is the ratio `(4*pi^2)/(pi^2/6)` for the specified single
shifted product. Its power-logarithmic dressing is obtained from the exact
carrier inverse. Weighted products with a different leading slope need their
own action conversion. An odd quotient cancels that slope and raises the
transseries height; its natural complex target charts are horizontal strips,
not unrestricted angular sectors.

The two-exponential coefficient includes both the derivative of the
exponential correction and the curvature of the carrier. Omitting the former
would give an incorrect coefficient.

## 6. q-Gamma critical point and inverse layer

The true q-gamma logarithm is strictly convex on positive real shifts, as
shown by an absolutely convergent positive second-derivative sum. Its unique
critical point lies between 1 and 2. The asymptotic construction near the
ordinary gamma minimum therefore selects the actual critical point for small
positive t.

The completion variable Q is promoted to an independent z before applying
analytic implicit-function theorems. Uniform bounds on common parameter disks
then justify the critical-point and critical-value expansions. In particular,
the second-order critical-value coefficient includes the displacement term
`-e'(alpha_0)^2/(2*kappa)`.

For the critical inverse layer, set `z=s^2` and `a=alpha_0+s*u`. The rescaled
initial equation has two simple roots away from its scaled discriminant.
This gives a genuinely convergent expansion in s with uniform local bounds.
The stated layer theorem excludes the moving branch point; the separate
completed quadratic normal form covers that point. The exponential action is
halved because of this ramification, not because a Borel singularity has moved.

## 7. Higher multiplicity and exclusions

The finite-multiplicity action rule assumes that all lower completion
coefficient functions vanish identically and that the initial rescaled
polynomial has simple roots. An explicit counterexample shows why checking
only the correction at the unperturbed critical point is insufficient.
Arbitrary higher-critical-point unfoldings and arbitrary phased root-of-unity
products are left as research problems.

## 8. Computation and presentation

The verification script passed 19 exact symbolic assertions and numerical
tests at 150 decimal working digits. The product/Borel comparison is
independent: it does not define the Borel sum by subtracting the proposed
completion. Critical-point tests subsequently use that checked identity and
are described as such. Their finite numerical success does not prove the
uniform analytic theorems or provide interval enclosures.

The final PDF has 32 pages. The last LaTeX pass had no unresolved references or
layout warnings. All pages were rendered for visual inspection. The editable
source and the PDF were generated from the same final version.

## 9. Literature and proof status

The article proves a precisely identified scalar formula presented as
Conjecture 5 in Fantini-Rella, arXiv:2506.08265v2, and its finite-weight
reconstruction consequences. It does not claim that no equivalent formula
exists in older transformation-formula literature. It also does not claim to
settle broader vector-valued or character-phase conjectures merely because
they involve related q-products. Independent expert review and comparison
with the older modular-transform literature remain appropriate.
