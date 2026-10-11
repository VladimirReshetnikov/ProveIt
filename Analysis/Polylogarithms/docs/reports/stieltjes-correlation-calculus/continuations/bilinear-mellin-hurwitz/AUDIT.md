# Analytic status and audit notes

## Proved in this article

1. Constructive finite-alphabet closure for positive integer orders, any
   positive scales, all admissible integer Mellin parameters, all integer
   denominator orders, and fixed logarithmic moments. The residue law
   identifies a representation-weight drop.
2. Finite connected double-Hurwitz transform for unit scales and -2<Re(a)<1.
   The leading-index-one cases are defined by explicit convergent formulas.
3. An all-weight compact double-zeta formula at a=0, and all logarithmic
   moments there and at a=-1.
4. Terminating Laurent-kernel reduction for all admissible integer a,N;
   Gamma/Bell/generalized-harmonic base moments.
5. Explicit binary-word primitives and a weighted MZV reduction.
6. Bilinear inversion reciprocity and the complete odd central parity sector.
7. Bilinear Stieltjes order-derivative identities, a connected discrete
   Stieltjes primitive, and a continuous adjacent-index primitive combination.

The proofs use ordinary analysis, finite combinatorics, and exact algebra.
No equality is inferred from a numerical residual.

## Important limitations

The finite-MPL closure theorem assumes positive integer polylogarithm orders.
A complex spectral-order extension is a further research question. Neither
this theorem nor the equal-scale double-zeta formula proves arithmetic
minimal depth, independence, or completeness of a motivic relation system.
Products of an even zeta value and a double zeta value are not automatically
additive depth two. The article states a depth-three upper bound for the
specific logarithmic formulas it produces.

The existing Gaussian S4 theorem is an input/status item, not a new result.
S6 and S8 remain unchanged. No new false equation was found in the sampled
source statements used as inputs. The recommended source change is a
carefully limited update of research question Q10, not an invented erratum.

## Endpoint and normalization safeguards

- Product convergence is -2<Re(a)<N, not the one-factor -1<Re(a)<N.
- Do not separate divergent leading-one double zeta terms.
- The compact zero-order value is Li_0(-t/(1-t))=-t.
- At a=0,-1 and s=1 evaluate combined analytic germs before specializing.
- Distinguish Hurwitz zeta(s;q) from comma-separated MZV indices.
- The connected shift identity is discrete; the adjacent-index integral and
  the word formula are continuous anchored primitives.
- The stable logarithm in the numerical evaluator avoids cancellation in
  the small-x tail at negative Mellin parameters.

## Source and verification coverage

The key prior report and selected canonical sections were read through the
GitHub connector. Its Q10 source blob was rechecked at the delivery pin.
The incoming directory and instructions were inspected, but the binary
contents of its eight listed archives were not analytically audited.
No claim of exhaustive nonduplication against those archives is made.

The exact suite tests 8,849 finite instances. The numerical suite tests 67
cases at 45 digits; its Euler--Maclaurin truncations are checked by refinement
but are not certified enclosures. Direct Stieltjes spectral quadratures and
continuous-primitive numerical tests are not included in that count.
The proofs of those extensions are explicit in Section 8.

No proof assistant, external peer review, or worldwide priority certification
is claimed. The PDF was built and visually inspected; this checks delivery
quality, not the mathematical truth of its theorems.
