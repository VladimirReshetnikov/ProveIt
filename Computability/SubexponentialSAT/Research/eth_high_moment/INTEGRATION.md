# Integration map

This package proposes mathematical changes to the OpenAI quantitative
contraction appendix. It does not patch or replace the source's formalization.

## New mathematical components

1. Replace the global quadratic-potential load estimate in
   `quantitative-contraction.tex`, subsection `tensor-packing`, with the
   higher-even-moment potential and exact conditional-expectation algorithm
   of report Lemma 3.1. Keep the orientation-compatible packet construction.
2. Use the exact integer `r=54`, decay `9`, cubic-reserve schedule in Section 7.
   The precision gap is `nu^2` per depth, not a second copy of `u_d`.
3. Retain the prior exact Hermite taper and sufficient precision
   `p_i = p + 6*tau*D_i + tau*u*(a+1)`.
4. Retain the prior factorial Cauchy modes, including the integral source
   features and creation-time canonical entry representatives.
5. Replace the cost proof with the complete uniform argument in Section 8.
   Explicitly charge `2^O((log s)^2)` labeling work at each call; its exponent
   is lower order and its space is polynomial.
6. Optionally use the revised dense-query grouping
   `J = ceil(sqrt(n) / ceil(log2(n))^2)` and the degree-sensitive schedule.

## Independent polynomial-time alternative

`orbit_packing.py` implements orbit-specific rounding with the original
quadratic potential. The article proves its exact padded-slot bound. It is
not required for the stronger higher-moment theorem and is included as a
simpler alternative with a separately accounted constant.

## What the package does not establish

- A smaller logarithmic-order exponent for unrestricted SAT.
- The earlier conditional structured-mode or linear-wire compression interfaces.
- An end-to-end executable implementation of the preprint's counter.
- A proof-assistant certificate, transitive Lean axiom audit, or solver benchmark.
- A universal runtime ratio against existing algorithms.

The article relies on the unchanged deformation, interpolation, canonical-lift,
and SAT-reduction results of the source. Those dependencies are stated at the
point of use. The finite programs test the new packing and schedule primitives.

Suggested location for a research packet:
`Computability/SubexponentialSAT/Research/high_moment_packing_2026_10_26/`.
No placement was performed by this task.

