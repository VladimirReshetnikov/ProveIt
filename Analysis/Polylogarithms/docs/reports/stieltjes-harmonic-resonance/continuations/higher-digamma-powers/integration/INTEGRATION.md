# Proposed integration into ProveIt

Baseline: b7667ae40a2957eed9a53d8559d53a3ee20dd1c1, inspected 2026-10-11.

## Recommended placement

1. Preserve the complete ZIP under docs/incoming as a reviewable research
   continuation. The single-file TeX and PDF contain the complete article.
2. Integrate the arbitrary-power material after the current quartic
   digamma-to-harmonic bridge. Its dependencies are the classical digamma
   recurrence/reflection/asymptotics and finite stuffle products; the article
   includes all new normalization and finite-part arguments.
3. Integrate the ordered-generator section after the relative harmonic
   interpolation and independent-order material. Retain the attribution to
   Ihara–Nakamura–Yamamoto and the Gamma-generator antecedents.
4. Treat the source corrections as a separate audit note. The Bailey–Borwein
   correction is limited to the inspected author-hosted 5 May 2014 version.
   The Mező correction concerns wording of a reduction target, not the
   invalidity of its subsequent theorems.
5. Keep the bounded Gaussian experiment in a research-status appendix or
   supporting data directory. Do not change S6 or revised S8 to proved.

## Principal labels

| Label | Result |
| --- | --- |
| thm:ML | Normalized all-power Mittag–Leffler formula |
| prop:difference | Exact finite coefficient-difference recurrence |
| thm:contour | Universal full logarithmic boundary polynomial |
| thm:all-power | Q_k = C_k + J_k + [s]D_k(s) |
| powers:lem:closed-residue | Closed asymptotic residue polynomial |
| cor:ordinary-all | All-power ordinary Stieltjes-subtracted series |
| thm:algorithm | Terminating strict harmonic-word reduction |
| thm:q5 | Complete fifth-power finite part |
| prop:heightkernel | Explicit normalized height-one Mellin coefficients |
| powers:cor:canonical-fifth | Fifth-degree cancellation with mixed coordinate retained |
| thm:primitive | Primitive with zero local Laurent–log constant |
| cor:derivatives | All differentiated polygamma identities |
| ord:two | Two-marker relative Gamma generator and convergence |
| ord:gap | Integer-gap finite reduction |
| ord:stieltjes | Generalized Stieltjes derivative identities |
| ord:gamma | Log-Gamma depth identity |
| ord:staircase | Finite-interval formula with several tagged exponents |
| ord:polylog | Polylogarithmic depth generator and finite reductions |
| powers:audit:BB-correction | Corrected sign/order of the two Tornheim integrals |
| app:s6 | Bounded S6 attempt and unchanged conjecture status |

## Preserve these conventions

- The finite part is the constant of the original x-coordinate cutoff integral
  on [0,1]. It is not an unspecified analytic regularization.
- kappa_k is the local Laurent constant of psi(z)^k at zero. C_k is the
  constant term of the combined large-circle boundary polynomial. They differ.
- [s] means the coefficient of s in a Laurent series. At a pole it is not
  evaluation of a derivative at zero.
- Strict zeta words have decreasing indices. The unshifted digamma sections
  sum over positive integers; the common-shift relative sections start at
  n=0 with denominator n+c.
- eta, theta, and chi are the first regular Laurent coefficients of the
  respective height-one functions. The article does not claim to reduce them
  to ordinary zeta derivatives or Stieltjes constants.
- D_(1,3), D_(2,2), and D_(3,1) are separately specified coefficients.
  Omega_4 = 2 D_(1,3) + D_(2,2) + 2 D_(3,1). They can be changed to another
  exact presentation using stuffle and Tornheim identities. Formal coefficient
  persistence is not arithmetic independence.
- The two-marker theorem gives normal convergence in a stated bidisc, and the
  one-marker specialization has the larger disc |x|<a. Outside the stated
  domains an asserted identity is one of meromorphic continuations, unless a
  separate convergence argument is supplied.
- The several-tag staircase is proved here only for a=b+N, N a nonnegative
  integer. Do not silently extend it to independent endpoints.
- The polylogarithm generator in the main section has a single argument on
  the largest index. The Gaussian appendix explicitly introduces its colored
  two-argument notation.

## Source questions resolved or advanced

The incoming Quartic Tails report's further-research Question 1, “The fifth
power with all finite corrections,” is answered by the full fifth formula,
its proof, and the ordinary convergent alternative.

Its Question 2, concerning canonical scalar polynomials, is advanced by an
explicit fifth-degree polynomial and a precise description of the mixed
coordinate that remains. The stronger all-order one-coordinate assertion is
not established.

The all-power formula resolves the analytic-normalization and finite
harmonic-reduction part of the higher-power program. It does not establish
ordinary-zeta reduction of arbitrary multiple-zeta derivatives.

The independent-order program is extended by arbitrary complex tagged
exponents in convergent depth generators, exact integer marker gaps, and
all tagged-order derivatives.

## Files and symbols

The article's modular fragments have only the listed common AMS macros.
If labels collide with existing manuscript labels, prefix the generic
thm:, eq:, sec:, prop:, and cor: labels during integration and update their
references together. Labels beginning ord: and powers: are already scoped.

The main TeX is assembled from tex_parts by code/build_article.py. All
mathematical content is present in the assembled TeX; no hidden inputs,
remote resources, or image assets are needed to compile it.

The Python coefficient table uses h_r=H_(n-1)^(r) and v=1/n; the stored pole
coefficient entries are explicitly at n-1. J_words and D_words use strict
outer index n. Coefficients are exact SymPy-readable algebraic strings.
