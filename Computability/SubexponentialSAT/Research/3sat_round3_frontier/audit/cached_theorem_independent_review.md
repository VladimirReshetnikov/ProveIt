# Independent review of the cached round-three certificate

## Verdict

The generic two-stage cached contraction theorem in `research_bounds/cache_tradeoff/proof.md` is mathematically consistent with the inspected source interfaces. Its explicit schedule gives displayed time coefficient 37.93010908288456 and space coefficient 33.62304092165775, and its rational checks certify the safe bounds **38 time / 34 space**, both on the normalized `s/sqrt(log_2 s)` scale. This is subexponential space, not polynomial space. No stronger logarithmic order or end-to-end solver has been established.

The comparison can be stronger and fairer than simply composing the old r16 example: an independent exact audit proves that **every fixed-alphabet r>=3, every three-block partition, and every positive taper allocation in the specified supplied generic cached certificate model has coefficient >38**. A feasible old-family example gives **38.2 time / 34.1 space**. The new theorem therefore crosses a verified certificate threshold instead of merely beating a convenient but poorly tuned baseline. These are bounds on formula families, not lower bounds on algorithms' actual runtimes. They do not exclude a different matrix-multiplication method, a different mode-graph evaluator, a multistage alphabet, cancellation, or a different contraction algorithm.

The optional low-degree theorem also checks: under the additional root-degree premise `Delta<=ceil(s^(1/12))`, allowing created packet degrees to grow rather than maintaining that unnecessarily strict cap yields **14.3 time / 12.4 space**, with displayed coefficients 14.23918819443970 / 12.36130145759395. This extra premise covers eventual bounded-degree direct clause networks, not the supplied general-density incidence reduction. The low-degree comparison here is to the supplied low-degree regime; no global low-degree optimality is claimed.

## 1. Shared source and normalization

The source pin is `d098ba436b33df19365a44dd178694ff52845d19`. The theorem imports the near-perfect asymmetric pair balancing, original deformation/Hermite/child-construction identities, full-block all-level Cauchy separation, and exact-weight cache/three-block/Strassen machinery. Imported reports were inspected but no imported code was executed. The input has at most s Boolean wires, maximum degree at most ceil(s^.9), polynomial descriptions and the unchanged modular tensor-entry oracle interface. This coefficient is not directly per SAT variable n.

The new schedule changes the root/tail alphabets, tapers and finite block sizes. It does not claim the slope-four basis, exact cache representation, asymmetric balancing, or seven-product multiplication as new.

## 2. Entropy and recurrence checks

Equal pair-class padding gives at most `(2+o(1))M/(r^2 D)` mode families for each directed off-diagonal group pair. The denominator remains **r^2**, not r(r-1): missing diagonal pairs remove terms but do not redistribute families. Combining the supplied slope-four entropy `pi^2/(24 theta)` with precision `(6+o(1))MD/u` gives

    sum_e w_e h_e <= (sqrt(sum_e w_e^2 / r^2)+o(1)) K,
    K = (pi sqrt(2)/ln 2) M/sqrt(u).

For a fixed three-block partition, the verified factors are:

* `alpha_r = sqrt(2(r-1))/r`, paying recursively evaluated group caches.
* `A_r = max_k sqrt(2rk-k^2-k)/r`, paying complete block-table construction.
* `J_r = max_k sqrt(2k(r-k))/r`, paying stored boundary tables.
* `B_r^2 = [sum v_j - (1-tau^2) min v_j]/r^2`, where `v_j=2k_i k_j` and `tau=log_2 7-2`.
* `beta_r=max(A_r,B_r)`, not the matrix term alone.

Thus the entire call satisfies

    T_d <= 2^((alpha_r+o(1))K_d) r T_(d+1)
           + 2^((beta_r+o(1))K_d),

up to polynomial factors. The second term uses already evaluated group caches and does not multiply a fresh recursive oracle call. Exact-weight allocation and list ranking are polynomial overhead because all chosen alphabets are fixed constants and precision is polynomial. Strassen is division-free and therefore valid over the relevant commutative quotient ring. The previously supplied sequential records/reblocking/sorting argument applies after changing only the fixed alphabet and partition constants.

At r7 with blocks (3,2,2), alpha^2=12/49, A^2=30/49, J^2=24/49, B^2=(24+8tau^2)/49. **Construction**, not matrix multiplication, controls beta. At r9 with blocks (3,3,3), alpha=4/9, A^2=42/81, J=2/3, B^2=(36+18tau^2)/81; here the matrix term controls beta.

## 3. Generic schedule and bit-cost checks

Use r0=7 and all later r=9, with

    u0/lambda = 89/5000,
    u_d/lambda = (1233/125000)(7/25)^(d-1), d>=1,
    total leading packet budget = 63/2000.

Flooring and the additive `ceil(log_2 lambda)^2` guard consume o(lambda). Exact capacity witnesses are `7^89<2^250` at the root and `9^63<2^200` on the retained high-degree side. The fresh-side and rounding exponents are below .232, well under one; created degrees remain below s^.9. Root and tail alphabets need not match: each recursive call creates its own fresh grouping, and the inherited precision/degree information depends on previous packet size, not the previous alphabet.

A hypothetical depth range `ceil(log_4 lambda)+3` is valid noncircularly: the strict power gaps hold throughout it, tail children eventually have at most M/4 wires, and `7/25>1/4` makes active tapers grow as a positive power of lambda. Sharply, `M_d <= (1+o(1))s(2/7)(2/9)^(d-1)`. This gives tail local exponents with ratio `gamma=10/(9sqrt(7))<1`.

The full time coefficient is

    max(beta7 K0,
        alpha7 K0 + K1 max(beta9, alpha9/(1-gamma))).

The formula evaluates to 37.93010908288456. Its root-only term is 37.5917025555. The source proof's uniform errors are preserved since active tapers diverge, precisions stay polynomial, and alphabets take only two constant values. Original entry costs exp(O(s^.9)), new entry costs exp(O(L log s)), direct leaves exp(O(s/lambda)), and polynomial work across O(log lambda) levels are lower order on the claimed scale.

Storage adds ancestor records rather than multiplying them. Its coefficient is `max(J7 K0,J9 K1)=33.62304092165775`; group caches are smaller than the same boundary-table bounds. This does not hide exponential storage inside an alleged polynomial-space guarantee.

## 4. Rigorous fixed-alphabet comparison, not just numerical search

This comparison fixes the supplied near-perfect/asymmetric/slope-four engine and the supplied three-block direct construction plus division-free seven-product cost model. It allows **all** integer alphabets r>=3, all three-block partitions, and all positive taper allocations in that model.

For generic degree exponent .9, the root budget is at most `A0=.05/log_2 r`; the cumulative retained-side budget is at most `A=.1/log_2 r`. Put `c=2/r` and `kappa=pi sqrt(2)/ln2`.

Every coefficient expression is at least its root-table contribution

    beta_r kappa / sqrt(A0).

It is also at least the full cache-chain contribution. Relaxing the root cap only weakens the latter lower bound. Holder gives

    sum_(d>=0) c^d / sqrt(v_d)
       >= [ A (1-c^(2/3))^3 ]^(-1/2),
    sum v_d <= A.

Consequently a lower bound is

    alpha_r kappa / sqrt(A (1-c^(2/3))^3).

The independent checker uses exact rational lower bounds and verifies:

* r=3,...,7: the relaxed full cache-chain expression is >38, regardless of partition or taper.
* r=8,...,11: enumerate every unordered positive three-block partition; every root-table expression is >38. The r8 actual limiting root coefficient is 38.1677456970, but the proof does not rely on a floating-point optimizer.
* r>=12: some block has k>=r/3, so `A_r^2 >= 5/9-1/(3r) >= 19/36`; also `log_2 r >7/2`. Conservative rational bounds for pi and ln2 already give root coefficient >38 for every remaining integer r.

The weakest certified universal lower bound is 38.0299943343. It is deliberately looser than the actual fixed-family optimum, but is strictly above the new exact certified upper bound 37.9567995130. This proves the separation without claiming to certify the numerical optimizer's last digits.

### A feasible old-family comparison

Take fixed r8, blocks (2,3,3), root `u0= floor(333 lambda/20000)`, and tail

    u_d = floor((999/100000)(2/5)^(d-1) lambda), d>=1.

The total leading budget is .0333; root and retained-side packing margins are strict. The fresh-side/rounding exponent is .2331. Add the same squared-logarithmic guard. The root-table term controls the time coefficient, displayed as 38.1868438947; space is 34.0097101721. The independent rational checker establishes **time<38.2 and space<34.1**. Thus the comparison is to a feasible combined algorithm, not only a boundary infimum or the old r16 display.

## 5. Optional low-degree theorem

The lower-degree proof correctly does **not** insist every created packet stay below s^(1/12). Existing tensors do not gain ports; at depth d their degree is at most `max(ceil(s^(1/12)),2L_(d-1))`. Symmetric balancing is sufficient whenever `a_d(1+2log_2 r_d)<lambda` with fixed slack. The proposed root r12 / tail r7 schedule uses leading root budget239/2000 and cumulative budget151/1000. Exact witnesses `12^478<2^1761`, `7^302<2^849` establish all degree/rounding packing constraints. Created degrees stay at most s^(.151+o(1)), still within the generic source oracle limits.

The tail has coarse child ratio1/3 and taper ratio7/16>1/3, so the same active-depth, precision and floor checks apply. Blocks (4,4,4) at the root and (3,2,2) thereafter give the reported 14.2391881944 time /12.3613014576 space. In the tail the infinite cache-chain endpoint, not merely the matrix endpoint, must be retained; the supplied formula does retain it. I found no missing resource term or incompatible premise in this optional theorem.

The dense/parity incidence network has degree s^(3/4+o(1)), so this optional rate cannot be applied to it. Direct bounded-degree sparse clause networks qualify eventually; conversion to an n-based coefficient still requires the actual wire-count factor.

## 6. Evidence

* `audit/check_cached_bound_independent.py`: original exact arithmetic checker for the entire fixed-alphabet exclusion and feasible38.2/34.1 comparator. Uses explicit `require` exceptions, not removable assertions. Machin/atanh intervals certify the conservative transcendental bounds; integer-power witnesses and integer-root intervals handle all other inequalities.
* `audit/fixed_alphabet_frontier_checks.json`: all exact rational bounds, all finite partitions, analytic large-r exclusion and comparator.
* Normal and `python -O` independent-check runs pass and produce byte-identical JSON.
* `research_bounds/cache_tradeoff/proof.md`, `certificate_checks.json`, `lowdegree_checks.json`: new theorem derivation and original-author rational checks, inspected as part of this audit.

The audit establishes these local interfaces, inequalities and certificate comparisons. It does not independently prove the entire original ETH manuscript, formally verify the theorem, benchmark a solver, or prove a universal lower bound on SAT or tensor contraction.
