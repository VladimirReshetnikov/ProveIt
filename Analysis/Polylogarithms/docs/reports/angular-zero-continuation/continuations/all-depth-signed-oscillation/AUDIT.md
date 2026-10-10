# Mathematical and source audit

## Concrete source findings

In the pinned `chapters/05-real-positive-kernel.tex`, the proof beginning at line
101 specializes the Hurwitz identity using `q=n` and invokes boundedness of `h`.
The referenced identity in `05-real-orders.tex`, label `subunit:eq:hurwitz`, uses
`x` as its argument. Its regularized bounded kernel is `q(t)`. The proposed patch
changes exactly those two symbols. The theorem and its numerical constants are
unaffected. Both the referring passage and the defining passage were read at the
pinned commit through the GitHub connector.

No substantive counterexample to the reviewed depth-two kernel and zero theorems
was found. The entire canonical manuscript was not audited line by line.

## Proof risks explicitly addressed

1. B uses two individually convergent integrals at each interior point. Norm and
   Fubini justifications precede all signed rearrangements.
2. Exact oscillation needs both bounds: vanishing moments force sign changes;
   derivative allocation and the endpoint value of A prevent extra or multiple zeros.
3. Minimality uses uniqueness of finite moment measures, not merely a sign pattern
   in one arbitrarily chosen representation.
4. The Cauchy variation argument includes repeated poles and hence multiplicities.
   Its base factor kappa/u need not be integrable alone; all complete kernels are.
5. At rho=1 the initial phase is bounded below pi, not assigned the value zero at
   the singular cut endpoint.
6. Strict radial motion uses finite positive-transform pole/zero interlacing and
   weak approximation. No global monotonicity of the angular phase is assumed.
7. The code accepts only integer indices. Positive real terminal orders belong to
   the analytic theorem, not the exact implementation.
8. A positive generalized order-four Stieltjes kernel can have a nonzero disk zero.
   The exact example is checked symbolically and is not attributed as an error in
   the manuscript.
9. The angular count is not extended to arbitrary rho>1: L_(1,1) has no upper-arc
   imaginary-part zero when rho>2.
10. No finite small residual is promoted to an arithmetic identity, and the
    compensation degree is not called minimal period depth.

## Verification boundaries

The exact suite checks finite coefficients, transforms, symbolic formulas,
interval enclosures, and signs. The infinite-dimensional and all-parameter
claims are justified by the written proofs. The package is not Lean-checked.
The canonical manuscript was not rebuilt; the standalone article and the
integration synopsis were compiled separately. Repository writes were not made.

The final visual/build review is recorded in `data/build_review.json`.
