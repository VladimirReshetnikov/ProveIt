# Claim status — 20 September 2026

## Proved in this draft

1. For 3 <= n <= 10, all n! mu_(n,j)(1+x) have nonnegative integer ordinary
   coefficients, for every j. This implies the published conjecture for all
   positive integer parameters in those dimensions. The support is full through
   degree j for n >= 4. In n=3, only the constant of mu_(3,3) is absent.
   Dimension three is proved by complete printed formulas. The remaining
   dimensions use explicit exact computer-assisted certificates.
2. In every n >= 3, the first magic coefficient equals
   n(3n-7)/4 + n x_1 + sum_{r=1}^{n-1} r(1+H_n-H_r) x_(n-r+1).
   This has a sharp positive minimum at b=(1,...,1).
3. In every n >= 3, mu_(n,0)=1; the final coefficient counts interior lattice
   points and vanishes exactly for n=3,b=(1,1,1).
4. An exact cube-addition identity reduces the full conjecture to b_1=1,
   together with induction on dimension.
5. For 3 <= n <= 10, the h*-polynomials are real-rooted by the imported
   Brändén transformation theorem. Ordinary Ehrhart positivity and monotonicity
   properties of the magic coefficient polynomials follow as stated in the paper.

## Not claimed

- A proof or disproof of the conjecture for arbitrary dimension.
- Coefficientwise positivity or full support for dimensions >= 11.
- A counterexample beyond dimension ten.
- Magic-positivity preservation under arbitrary Minkowski sums.
- Intrinsic dimension-one failure at the single point b_1=1.
- Independent refereeing, formal proof-assistant checking, or established priority.

## Inputs credited to the literature

Bayer et al.: the rank/vertex description. Hill et al.: the slice recurrence,
polynomiality and dilation machinery, as well as the two-parameter positivity
classification and the open problem itself. The paper gives direct derivations
of the machinery for auditability; it does not claim it as new.
Ehrhart–Macdonald reciprocity identifies the endpoint coefficient.
Brändén's theorem supplies the real-rootedness consequence.

## Verification performed

Full exact regeneration and comparison of the certificates through n=10;
478,177 retained positive coefficients in the n=3..10 magic maps;
55 independent polynomial difference identities for summation kernels;
731 independent sorted-orbit geometric lattice counts, including 486 at
positive dilation and 245 at dilation zero. The first-coefficient polynomial
formula is separately compared in every stored dimension. The asymmetric
published example b=(2,3,1) also agrees. No floating-point arithmetic is used
in any mathematical check. Timing measurements use the system clock only.
