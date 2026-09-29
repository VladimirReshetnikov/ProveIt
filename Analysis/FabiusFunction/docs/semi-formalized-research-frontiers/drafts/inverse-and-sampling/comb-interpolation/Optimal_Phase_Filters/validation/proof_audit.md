# Proof and verification audit

## Analytic result dependencies

1. The Rvachev kernel is normalized by the law of
   Y=sum_{j>=1} 2^(-j) V_j, with V_j independent uniform[-1,1].
   Its Fourier transform starts at j=0, not j=1.
2. Poisson summation is in physical coordinates: spacing and weight are both
   1/M. The repository's lattice-coordinate monomial defect differs by M^(r+1).
3. The real zero set of H is Z minus zero, with multiplicity 1+v_2(n).
   The proof explicitly rules out extra zeros from a vanishing infinite tail.
4. For odd a,k, the first two sinc ratios each contribute exactly 1/k.
   Every subsequent ratio is at most one. The denominator H(a/2) is nonzero.
5. At the first threshold p=v_2(M)+1, the local derivative has sign minus:
   H^(p)(Mk)=-p!*H(ak/2)/(Mk)^p for odd k. Even aliases vanish.
6. Pairing opposite aliases retains i^p through cos(2*pi*k*theta+p*pi/2).
7. The tail estimate is relative to the reference harmonic, not merely an
   absolute sup-norm bound. This is what excludes zeros close to a known zero.
8. The derivative tail is absolutely summable, giving simple roots.
9. Uniform phase filtering is quantified over every translating phase with a
   single fixed filter. The Fourier criterion uses every derivative order
   through r, not only the top derivative.
10. Rational meshes are in lowest terms. Nonmultiples of the denominator force
    Fourier vanishing already at degree zero. Integer aliases are then controlled
    by their exact dyadic zero multiplicities.
11. Atomic counts are after coalescing coincident phases and deleting zero
    weights. Cyclic invariance forces whole orbits even for signed/complex weights.
12. For an at-most-N optimizer, its required orbit size L satisfies L<=N<2L;
    consequently there is exactly one orbit. This proves the uniqueness assertion.
13. The finite moment theorem uses conjugacy only for real signed measures.
    The complex case uses the longer nonnegative frequency window.
14. The synthesis operator uses triangular moment inversion on polynomials;
    no globally entire reciprocal moment-generating function is asserted.

## What was checked computationally

- 1,118 exact rational base-value, reflection, quadrature, and refinement checks.
- 1,026 exact rational orbit-invariance checks for finite filters.
- 992 numerical odd-multiplier inequalities and 32 numerical binary-sign checks.
- Truncated Fourier defects compared with exact dyadic quadratures, with the
  observed discrepancies recorded in results.json.
- The source was compiled successfully in three successive pdflatex passes.
- All PDF pages were rendered and visually inspected using contact sheets;
  selected pages were also rendered at higher resolution.

## Not claimed

- A new Lean or Rocq proof or an independent rebuild of the existing repository.
- Global bibliographic priority or peer review.
- General fixed-phase failure at degree v_2(M)+2.
- A phase-count lower bound for arbitrary quadrature nodes or phase-adaptive
  weights at one fixed translating phase.
- Interval-certified numerical output or a proof from finite testing.
