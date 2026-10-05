# Independent review: scaled six-port finalizer boundary

**PASS within the protected interface.** The all-polynomial multiplier lower bound and the attaining 84-row rearrangement are sound. No correction is requested. This review does not establish an unrestricted complete-source minimum or rule out a different positive-zero presentation.

## Pins and reading scope

The full reviewed proof is `/tmp/complete84_scaled_finalizer_boundary.md`, SHA-256 `492a07cd42913e88004ecaa0d65f4133c10d5caa6d529b27b5f8aa891748670e`. Its receipt is `/tmp/complete84_scaled_finalizer_boundary.json`, SHA-256 `7aa168cdfa03e9c63979690a67be9766838803335cab5215b6ffdad5294ae3d1`; I read its source guards, removed rows, complete replacement tail and count/scope metadata, and performed fresh data-only topology, equality and liveness checks of its full array.

The author helper `/tmp/complete84_scaled_finalizer_boundary.py`, SHA-256 `4aab6d264c55090e1f345d431f5efbb6f16945f3e7b8e4729129e18b45159174`, was authenticated only. No author or predecessor helper, saved source array, supplied program or builder was executed or imported.

The actual parent files under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` are `complete84_scaled_strong_output.json`, SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`, and its Markdown proof, SHA-256 `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`. The parent note and literal producer definitions were read, including the index/transport and finalizer rows. Historical local lower bounds mentioned in the author's introduction are background, not assumptions needed by this proof, and were not rereviewed here.

## Addition bound, including reuse and cancellation

The shared support-direction invariant is valid for an arbitrary arithmetic DAG. Initially every nonzero input or constant has singleton support. Maintain one common vector space V such that each nonzero register has support in some translate of V. A product adds offsets and keeps direction space V; reusing a register changes nothing. An addition of two nonzero registers enlarges V by at most the difference of their offsets, one direction. If one register is zero there is no enlargement. Cancellation only removes support points, and a zero result imposes no support condition. Thus a additions/subtractions allow affine support dimension at most a, independently of the multiplication count.

For `F=P(U-Q)(Q(A-B)+B)-D`, the displayed seven monomials have affine dimension exactly four. The author's four-difference minor is nonsingular; the two independent affine equations on all six exponent coordinates give the matching upper bound. No two displayed coefficients vanish in characteristic zero.

For any nonzero polynomial H, the Newton polytope of `H*F` is the Minkowski sum of the two Newton polytopes. A generic exposing weight gives a unique leading monomial in each factor with nonzero product coefficient, so cancellation of other terms cannot remove the exposed sum vertices. The sum contains a translate of the polytope of F. Therefore every such multiplier still needs at least four additions/subtractions. H may depend on all six ports; it need not be positive or preserve zeros.

## Multiplication bound

The quartic leader of F is `P*Q*(U-Q)*(A-B)`. Its four distinct linear factors have multiplicity one, so it is not a nonzero scalar times a square.

With at most two multiplications and arbitrarily many additions, the first product has degree at most two. Every register before the second multiplication is an affine combination of original inputs and this one product. A degree-four second product therefore has leading part proportional to the square of the first product's quadratic leader. There is only one resulting quartic register direction. Subsequent additions either retain a scalar multiple of it or cancel it entirely, leaving degree at most two. This excludes F and every nonzero scalar multiple of F. For nonconstant H, the degree law gives `degree(HF)>=5`, exceeding the maximum degree four available from two multiplications.

These are simultaneous necessary inequalities `M>=3` and `A>=4`, so fewer than seven gates cannot suffice. The listed `3M+4A` schedule attains seven for H=1; the theorem does not say every other multiplier attains it.

## Actual-source independence and paid boundary

The six-source-port independence argument is valid on a fixed valid program slice. In the order `s,f,i,T,y_aux,tau_root`, each successive cut `D,U,Q,A,B,P` introduces its next variable with a nonzero polynomial leading coefficient, and no earlier cut uses that new variable. In particular the exterior coefficient of `tau_root^2` is nonzero: the main and input norms have nonzero quadratic coefficients in sigma and rho, the index factor has h coefficient `-UM`, and the transport factor has quotient coefficient `-repunit`. These expressions are nonzero polynomials with the valid fixed numerals. Comparing highest powers successively proves injectivity of the six-variable polynomial substitution. This is generic algebraic independence, not a claim that numerical values at a zero are independent.

The preliminary positive-domain observations are also sound. `D=(a+2)^2-1` is nonsquare and positive. Thus `U-Q=0` with positive f and S would make D a rational square and hence an integer square. Likewise `Na=0` would make the nonsquare integer `S^2-1` the square of the rational number `SV/y_aux`; the literal S is at least8 and y_aux is positive. The resulting zero-preserving multiplier examples supply no free divisions or lower-cost implementation.

Fresh data-only inspection confirms exactly 75 literal retained parent rows, followed by two multiplications materializing P5 and seven residual gates. The full ledger is `84=47M+37A`; all 84 rows and all 25 supplied ports are live, with no duplicate definitions or forward references. The two-stage multiplication charge is not hidden: P5 is the product of the three available exterior factors. Those factors can themselves be treated as independent through their separate nonconstant tau_root, h and transport-quotient dependence, so their product is not a one-multiplication polynomial in those three ports.

The new nine-row tail expands to the original product of all seven factors minus D. All other rows are literal. Hence the whole polynomial, complete zero tuples, and inherited degree187 and positive-domain language remain unchanged for H=1. No old array was numerically evaluated to establish this identity.

The resulting exclusion is exactly the author's protected `75+2+7` boundary. It does not prevent saving a gate by sharing an exterior-product intermediate with the tail, using an additional already paid root or other donor, altering the retained producer graph, changing coordinates, or proving a different positive-zero equivalence. No broader source lower bound follows from this review.
