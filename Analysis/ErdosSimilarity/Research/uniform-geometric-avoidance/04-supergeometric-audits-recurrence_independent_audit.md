# Independent audit of stable recurrence and compact all-recurrence sections

Audit: independent AI-assisted mathematical review
Date: 2026-10-08
Files inspected:
- sections/04_stable_recurrences.tex
- the extension incorporated into sections/05_consequences_and_limits.tex
- sections/01_results_and_sources.tex (main theorem statement)

No article files were modified.

## Verdict

No mathematical correction is necessary in the inspected versions.
I found the stated continuum-parameter, arbitrary-tail, nonzero-hit
theorem justified by the signed block lemma, and the compact extension
to every infinite-range real constant-coefficient homogeneous recurrence
follows from the bounded-recurrence dichotomy.

This is an independent mathematical reading, not a Lean or other
machine-checked formal verification, and not a priority certification.

## Detailed checks

1. First-crossing selection:
   V0=1>Q^j, so minimality works even when nu_j=1. The one-step lower
   norm bound gives alpha Q^j<V_nu_j<=Q^j. The upper exponential
   estimate gives nu_j<=Tj. The selected scalar is an actual original
   coordinate, with index<=Tj+m-1. Selected original indices need not
   increase, but distinct selected magnitudes force them to be distinct.

2. Signed separation:
   For j<k, |b_j-b_k|>=(||b_j|-|b_k||)>(alpha-Q)Q^j.
   This remains true for opposite signs. The center is separated by
   |t b_j|>u alpha Q^j. Grid width Q^b/c with
   c=4/[u(alpha-Q)] is smaller than all relevant separations.
   All points lie in [x-vQ^j0,x+vQ^j0] of length<1/4, so circular
   and ordinary separations agree.

3. Stability:
   The closed forbidden interval around x correctly removes exact grid
   boundary centers, which matters for negative displacements with
   right-half-open keys. The density bound 4vcKQ^(g+1) is valid.
   Earlier keys are fixed for all parameter values and signed tests.

4. Conditioning:
   Center exposure reveals one address in every selector table and
   therefore fixes the first default vertex. Active selector addresses
   are distinct and unexposed. Conditional on all selectors, terminal
   addresses are pairwise distinct by disjoint subtrees, different leaf
   tables, or refinement within the same leaf. Averaging (1-p)^L over
   fresh fair selectors gives exactly (1-p/2)^((M-1)r).
   Independence of full routes is neither assumed nor needed.

5. Sign-key complexity:
   The threshold polynomials f_{n+i} +/- Q^j determine V_n<=Q^j,
   including threshold equalities, and hence the least first crossing.
   Squared-coordinate differences determine the least maximizing
   coordinate, including ties.
   Unwrapped local grid boundary polynomials determine the selected
   point's finest key, including equality and wraparound. Unselected
   candidate coordinates do not need additional boundary ranges.
   Counts S=O((B+1)^2 Q^(-2r)) and Delta=O((B+1)^D) are valid.
   Constants can depend on fixed tree/family parameters but not r0.

6. Sign-condition reference:
   Independently opened the original author-hosted PDF:
   https://www.math.purdue.edu/~sbasu/combinatorica_final.pdf
   Section3.2, printed page5, Eq(3.3) gives
       sum_{j=0}^{k'-i} binom(s,j) 4^j d(2d-1)^(k-1).
   With i=0, ambient k=k'=parameter_dimension+1, and degree Delta,
   this is exactly the finite inequality used in the manuscript.
   Zero signs are included by the paper's definitions. The main
   fixed-degree asymptotic theorem is not being used improperly.
   The further bound by [8 Delta(S+1)]^(d+1) is a valid crude estimate.

7. Representatives and parameter growth:
   The sign vectors fix every possible local table address before
   unrevealed table entries are sampled. A representative may be chosen
   separately on each center-exposure atom. The union bound is valid.
   Once M,h,g,j0 are fixed, B is affine in r0. Hence the polynomial
   factor in B is beaten by theta^r0. For every local r>=r0,
   theta^r<=theta^r0, so one choice works at every first-default height.

8. Compact-center repair:
   Residual set R uses all original continuous polynomials through
   N=TB+m-1, not the discontinuous selected functions. It is a
   projection of a closed subset of a compact product and is compact.
   Pointwise probability bounds imply expected residual density via
   this measurable R. If a finite hit has f_n=0, then x lies in A+;
   openness and arbitrarily late nonzero original terms supply a
   nonzero hit. The same argument works for x in the repair U.
   Lower norm control ensures infinitely many nonzero original terms.

9. Compact stable matrix exhaustion:
   Theta_{m,s,L} is compact and rational semialgebraic.
   The inverse norm bound m! L^m follows from cofactors and |det|>=1/L.
   The decay estimate from ||T^s||<=1-1/L is uniform on the family.
   Every invertible stable real companion matrix lies in one family:
   choose s first, then sufficiently large L. This avoids choosing a
   Jordan basis continuously near colliding roots.

10. Stable-tail reduction:
    Shift-polynomial isolation annihilates all other active roots and
    preserves convergence to zero. Its action preserves polynomial
    degree and nonzero leading coefficient on the isolated root.
    Hence active |lambda|>=1 is impossible. Nilpotent parts vanish after
    a finite tail, and the remaining real annihilator has nonzero
    constant term and roots strictly inside the unit disk.
    The resulting initial state is nonzero and invertibility keeps all
    later states nonzero.

11. Countable assembly:
    The countable matrix/scale families exhaust all needed real
    coefficients, orders, normalized initial states and positive
    scales. Every blocker has period1, so the sum-of-densities argument
    is legitimate. Reflections give symmetry (although signed initial
    states already handle negative affine dilations).
    Applying the block lemma to arbitrary later states supplies
    arbitrarily late nonzero hits. Since the sequence tends to zero,
    finitely many distinct nonzero values cannot account for them.

12. Effectivity:
    Theta emptiness and each finite rational-arc cover condition are
    first-order real formulas with rational coefficients.
    For fixed N, |f_n|<=L^n and t<=R give an effective finite bound on
    the periodic translates appearing in the formula.
    Applying the existence theorem with half the density budget gives
    room for a rational finite-arc witness. Nonzero f_n and membership
    in open H are open conditions. Compactness supplies finitely many
    witnesses and hence a finite N and a rational finite-arc subcover.
    Thus enumeration plus real quantifier elimination terminates.
    Finite unions of rational arcs have rational measures; the stated
    geometric tail budget gives a computable modulus for the limiting
    measure. No computable distance function is claimed.

13. All-infinite-range compact extension:
    The bounded-sequence shift isolation correctly excludes growing
    roots and nonconstant polynomial weights on unit-modulus roots.
    A rational basis of the unit-root arguments gives finitely many
    residue classes, each represented by a continuous real Laurent
    polynomial on a connected torus. Kronecker density of every tail
    makes each residue tail-limit set exactly its compact interval
    image. If all images are singletons, the unit-modulus part is
    periodic and the remainder tends to zero.
    If only finitely many affine pattern values lie outside K, all
    tail-limit intervals lie in closed nowhere-dense K union a finite
    set; hence they must be singleton intervals. One residue subsequence
    has infinite range, converges, and is not eventually constant.
    Subtracting its limit preserves the recurrence property, so the
    stable theorem contradicts the finite outside set.
    Unbounded sequences have infinitely many distinct values outside
    compact K automatically.

## Optional clarity edits only

- In the countable-assembly proof, one can explicitly say "relabel the
  stable tail" before writing a_{J+n}; the finite initial offset is
  harmless for the desired arbitrary-late-index assertion.
- The effective-cover proof can provide the bound
  |x+t f_n|<=1+R L^N for x in [0,1], n<=N, making the finite periodic
  translate range completely explicit.
- Neither edit repairs a mathematical gap.


## Final integration status

Both optional clarity edits were incorporated in the delivered manuscript.
