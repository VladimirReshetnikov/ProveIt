# Independent adversarial review: unequal-precision branch recovery

Reviewed the final chapter `papers/precision.tex` and the exact checker `code/verify_unequal_branches.py`. The theorem is over a field F, with finitely many pairwise distinct branches u_b in X F[[X]], arbitrary nonnegative integer precisions n_b, and unrestricted H in F[[X,Y]]. These hypotheses are important: this review does not extend the result to a coefficient ring with nilpotents.

**Verdict:** The kernel decomposition, complete target-jet criterion, ambiguity dimension, sparse certificate, clean recording budget, target-specific distance, sharp saturation budget, weighted tree merge and pruning recurrence are correct. A draft claim about total polynomial degree was corrected in the final chapter; the corrected witness and complexity statements have been checked below.

## 1. Exact kernel decomposition

Formal division by Y-u_b is valid because u_b has zero constant term. Substitution and the quotient series converge in the formal topology. Repeated division gives the unique Newton expansion

`H = Pi_N Q + sum_{j<N} c_j(X) Pi_j(Y)`.

Uniqueness can be proved by sequential evaluation on the selected branches; products of distinct branch differences are nonzero in the domain F[[X]]. This also shows that the asserted module sum is direct.

At greedy step j, maximality gives `n_b-sum_{i<j}s(b,b_i) <= mu_j` for every still unselected branch. Thus `X^max(0,mu_j) Pi_j` satisfies every observation constraint, including the selected branch. Conversely, after subtracting preceding kernel terms, evaluation at b_j forces exactly that divisibility of c_j. This is a two-sided proof of the full kernel; the basis terms are not merely sufficient witnesses.

The capped score exponents are intrinsic: in the kernel's polynomials of Y-degree at most j, the ideal of possible leading coefficients is precisely `X^max(0,mu_j) F[[X]]`. Therefore capped tie independence holds without needing a separate greedy optimality theorem. Full raw tie independence, including negative values, is correctly proved later by the ultrametric tree merge.

## 2. Total-degree jets and ambiguity dimension

Each Pi_j is monic of Y-degree j and its coefficient of Y^i is divisible by X^(j-i). The lowest total-degree form of a sum of Newton terms cannot cancel: among terms attaining the smallest total order, take the one with greatest Y-degree. Its highest Y-power cannot be supplied by any other leading form. Hence the Newton basis preserves total order exactly.

Since every contact is at least one, successive greedy scores decrease by at least one. Consequently `mu_(d-1)>0` forces every kernel generator of index j<d to have total order at least d. If `mu_(d-1)<=0`, Pi_(d-1) itself is an invisible function with nonzero d-jet. This proves both directions of recovery. For d>N, Pi_N prevents recovery, explaining the theorem's stated range and its claim that the number of positive scores is the largest recoverable order.

The classes `X^i Pi_j` with i+j<d form a basis of the target jet. Counting the classes with i>=max(0,mu_j) gives exactly the displayed ambiguity dimension; there is no hidden linear dependence in this count.

## 3. The sparse d-branch certificate

The first d branches of a full greedy order remain a greedy order on that subset, with the same initial scores. Thus every successful collection has a successful d-branch subcollection.

For exactly d branches, the componentwise necessary-and-sufficient condition is `n_b >= 1 + sum_{c!=b}s_bc`. Sufficiency follows from Lagrange interpolation: an invisible observation divided by its branch-difference denominator belongs to X F[[X]], so each degree-(d-1) Newton-type factor is pushed to total order d. Necessity uses the integral unit multiple of the product of all branch equations except one; its only potentially nonzero record has valuation equal to the denominator's contact sum. This verifies the certificate even when branch precisions vary enormously or some unused records have precision zero.

## 4. Optimal clean recording cost

Any successful precision profile contains a certificate subset S of size d. Summing its componentwise lower bounds yields `d+2 sum_{pairs in S}s_bc`. Conversely, recording exactly those bounds on any minimizing S and recording nothing elsewhere succeeds, proving the optimal cost formula.

The claim that ordinary P-ordering minimizes this pair energy has a self-contained determinant proof in the chapter. The normalized Newton polynomials P_j/alpha_j are integral valued on every branch by greedy minimality. Their evaluation determinant on an arbitrary d-subset is a Vandermonde determinant divided by the product of alpha_j. Its integrality gives the required energy lower bound. On the greedy d-subset that matrix is triangular with diagonal one, proving equality. No unproved global greedy principle is needed.

## 5. Target distance and corruption/erasure threshold

The target distance minimizes the number of nonzero records over functions with a nonzero d-jet. This is the correct distance for the problem; minimizing over all nonzero functions would be inappropriate because high-order terms may change records without changing the target.

A retained subset fails clean recovery exactly when it is a zero set of some function with a nonzero target jet. Maximizing its size therefore gives the exact distance `N-C_I(d-1,0)`. The standard two-explanations argument gives sufficiency of `2w+z<delta_d`. For necessity, take a minimum-distance difference, erase up to z of its support blocks, and split its remaining support between two error sets of size at most w. This construction works for unequal block lengths and does not require a finite field or a linear decoding algorithm.

The upper bound `delta_d<=N-d+1` follows from a product of d-1 branch equations. Equality means every d-branch subset is a clean certificate. Maximizing the componentwise contact sum over all such subsets selects the d-1 largest contacts at each branch, proving both the exact saturation profile and its optimal total cost. When N=d+2w+z, maximal distance is necessary and sufficient, so this same budget is the exact optimum for the requested error model.

## 6. Contact-tree merge and pruning

Contacts are ultrametric: `s_bc >= min(s_ba,s_ac)`. At an internal tree node with common incoming stem ell, every candidate pays the same j*ell after j choices. Its remaining score depends only on choices in its child. The global greedy process therefore merges the children's nonincreasing streams, and subtracts j*ell from the j-th merged entry. This proves the raw-score merge, including arbitrary ties and negative scores.

For a selected subset, the j-th parent score is at most T exactly when at most j child-stream entries exceed the common shifted threshold `T+j*ell`. Allocating those allowed entries among children gives the pruning recurrence, in both directions. The minus-infinity tail properly handles subsets containing at most j leaves, including empty subsets.

The claimed `O(N d^2 (n_max+1))` count is a count of integer arithmetic operations once the finite contact tree is known; it is pseudopolynomial in the recording precision, not a bit-complexity claim for arbitrary formal-series input. It is correct with the organization now stated in the chapter: for each common child threshold U, convolve all child tables across rank budgets once, then read parent state (j,T) at `U=min(n_max,T+j*ell)`. A separate fresh convolution for every (j,T) would waste a factor d, but the final checker includes the correctly batched implementation.

The dynamic program computes the exact distance and a sharp surviving ambiguity configuration. It does not itself identify corrupted locations or provide a fast error-correction decoder; the chapter states this limitation correctly.

## 7. Corrected witness statement

A Newton product is a polynomial in Y with formal X-coefficients. Its Y-degree is at most d-1 and its total order is at most d-1; its total polynomial degree need not be at most d-1. For example, over F_3 use branches X+X^100 and X+2X^100 with precisions 101 and 100 and target d=2. The invisible function Y-X-X^100 has a nonzero 2-jet, but no nonzero polynomial of total degree at most one is invisible on the first branch to precision 101.

The final chapter now makes the correct statement. Truncating every X-coefficient modulo X^M for `M=max(d,n_max)` produces a finite polynomial with the same target jet and all the same records, because the discarded part is in X^M F[[X,Y]]. This supplies genuinely finite witnesses without a false low-total-degree assertion.

## 8. Verification and scope

The accompanying checker compares the kernel formula with direct finite-field substitution and matrix ranks, and compares the pruning formula and batched tables with exhaustive subsets. Its domain cutoff `max(d,n_max)` is sufficient: any monomial of that total degree or higher evaluates to order at least the cutoff on branches in X F[[X]], and therefore affects neither the records nor the target.

The checker's examples and finite exhaustive checks corroborate the proof. They do not establish global novelty. The weighted greedy method, Newton interpolation, P-orderings, and the error/erasure distance inequality are established ingredients. The new contribution claimed in this package is their exact unequal-truncation observation-kernel and target-jet synthesis, including the resulting optimal budgets. Higher-power coefficient rings and a fast corruption-location algorithm remain outside the result.

