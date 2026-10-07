# Exact companion for Report 288

`exact_checks.py` is an offline bounded diagnostic using only Python's standard library. Integer and rational arithmetic is exact. It accepts no command-line options and prints a deterministic JSON record. It is not a substitute for the written proof.

## Fixed diagnostic inventory

- Small cyclic domains: all 12,488 normalized maps with a(0)=0, domain orders 1 through 6, and targets Z/2, Z/3, Z/4, (Z/2)^2 and Z/2 × Z/3. Exactly 12,428 of these maps are nonaffine; their full-indicator ratios are checked against 3/4. Image translation leaves the statistic unchanged, justifying normalization
- Four-point windows: 924 nonzero-middle-defect cases in Z, Z/7 and Z/8, with integer, Z/3 and (Z/2)^2 targets, checking ordinary energy 44 and respected energy at most 32
- Index-two SOS: 80 rational-weight cases over Z and the even cyclic groups of orders 2, 4, 6 and 8, including both correlation identities and strictness on Z
- Jensen remainder: all eight normalized maps (Z/2)^2 → Z/2, their four nonadditive cases, the exact 40/64 ratio, and all 255 nonzero weight vectors from {0,1,2,3}^4
- Interval, cylinder and box formulas: 12 intervals, 12 cylinders and 25 two-dimensional boxes, including the positive constant 17 in the box-excess numerator
- Indicator upper witnesses: all 136 interval choices 1 ≤ m ≤ n ≤ 16 in Z/(2n), 36 six-point-or-smaller products with coordinate orders 0,2,4,6,8,10 (zero denotes Z), covering all six wrapping types and the exact worst ratio 47/63, and five exact-rational support-bound samples
- Indicator lower bound: all 1,023 nonempty subsets of {-4,-3,...,5}, checking the signed-convolution norm lower bound, the cubic energy bound and the 1/(4s^2) ratio excess
- Binomial witnesses: m=1,...,12 on Z, together with 180 even cyclic cases, checking exact binomial ratios, reflection symmetry, full-group endpoints and finite-folding bounds

The unit tests add independent fourfold enumeration, target-torsion comparisons, product-group SOS, affine invariance, negative exponents, exact ceiling boundaries, collision/no-collision folding, input caps and optimization-safe guards. They deliberately distinguish integer-valued parity from parity valued in Z/2: the latter is affine and has ratio one.

These target groups are a finite diagnostic collection. They do not represent an enumeration of all finite targets or establish a theorem for arbitrary targets. The public energy routine can also handle other bounded products, including mixed finite/infinite targets.

## Public API and bounds

- `Group(moduli)`: a tuple of one through three moduli. A zero denotes an infinite cyclic factor; a positive integer denotes a finite cyclic factor, including the trivial factor of order one. Each modulus is at most 128 and the product of the finite factor sizes is at most 128
- Elements are tuples of the same length. Coordinates are exact integers, not bools, with absolute value at most 4,096; finite coordinates must be canonical residues. `elements()` is available only for finite groups
- `energy(domain, target, weights, images)`: weights are a dictionary with at most 128 entries, containing nonnegative exact integers or `Fraction` values. Each numerator uses at most 256 bits and each denominator at most 128 bits. Zero entries are ignored, but some positive weight is required. The image dictionary must have exactly the positive-support keys, with valid target elements
- `convolution(group, left, right)`: the same weight validation, allowing empty inputs; returns exact convolution coefficients
- `parity_sos(domain, weights)`: verifies the index-two identity for first-coordinate parity, with integer target. The first factor must be Z or have even order. It returns U,V,C,D, the squared signed-convolution norm, correlation asymmetry and energies
- `cyclic_histograms(values, target)`: one through eight image points, returning derivative square sums, the full-indicator energies and a consecutive-difference affinity check
- `interval_ratio(m)`, `cylinder_ratio(m)`, `box_ratio(m1,m2)`, `binomial_ratio(m)`: exact formulas with integer parameters from 1 through 32
- `indicator_support_bound(epsilon)`: an exact positive integer or `Fraction`, with numerator and denominator at most 128 bits. Returns max{6,2 ceil(3/sqrt(32 epsilon))} without floating-point arithmetic

Returned energies have `ordinary`, `respected` and exact `ratio` fields. The implementation counts ordered pairs and squares bucket masses, agreeing with ordered-quadruple definitions. Resource caps are operational limits, not mathematical restrictions in the report. Private underscore-prefixed helpers are implementation details and do not provide separately validated entry points.

## Limits of the result

Finite checks do not prove the arbitrary-group theorem. The indicator lower bound is not a lower bound for arbitrary weights. The weighted witness construction does not claim optimal support size. The conditional 5/8 theorem applies only after affinity on every cyclic coset. A box reaches limiting ratio 5/8 only when both infinite side parameters grow. There is no classification of all maps at ratio 3/4, no arbitrary-target 8/11 classification, no partial-domain extension and no downstream density-increment claim.
