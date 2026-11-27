# Independent adversarial audit: composite-exponent Euler matching

Reviewed material: the full cyclic and prime-primary theorem proofs incorporated into the accompanying manuscript. Source pin `6b034b74a8224c893e7e83127f33cd1a6958785d`.

## Verdict

The finite cyclic all-degree theorem and the p-primary mass/equality/saturation theorems are mathematically sound after correcting one numerical counterexample in the initial p-primary draft. The correction is already present: for X=C_(p^2), P=pX, and a generator t, the two coset packets P and t+P disagree at every nontrivial evaluation, so their density is 1-1/p^2, not 1-1/p.

No claim in this audit is an independent Lean kernel verification. The finite arguments were reviewed at the level of ordinary rigorous mathematics; exact finite experiments are supplementary.

## Cyclic result

- The small-marginal induction is valid. A signed integer array with all marginals on fewer than r coordinates zero has L1 norm at least 2^r. Slicing at a coordinate containing two support values gives at least two nonzero arrays each satisfying the (r-1)-condition. The r=0 and empty-coordinate cases are covered by integrality.
- The Euler-polynomial equality condition is the equality of the full root-value histogram, not only the first Fourier trace. This is essential at composite exponent.
- For a nonzero marginal on I, every evaluation that is a unit on the primary coordinates I has nonzero pushed-forward marginal. Thus the faithful-evaluation cylinder is contained in the mismatch set.
- The ordering of the prime factors gives the stated lower bound, since each factor 1-1/p is in (0,1) and increases with p.
- The parity-box construction uses elements E/p_i of different prime orders. Their subset sums are distinct, and their pushed-forward subset sums remain distinct precisely when every selected primary evaluation is a unit. Both signs have mass 2^(t-1). Padding with common characters yields every allowed degree k.
- Edge cases: E>=2, k>=1 are required; t>=1. A prime-power cyclic group has t=1 and exact minimum 1-1/p for every k, consistent with the p-primary theorem's M=1 case. The unrestricted threshold k=2^(s-1) follows from strict decrease of the products.
- The example modulo31 is correct. The element3 has order30, all listed exponent characters are nontrivial and hence primitive modulo31, and disagreement occurs exactly at the primitive roots (8 of 30 reduced residues).
- The full-power criterion using H(dv) for proper divisors d|E is valid because the trace at j is Galois-conjugate to that at gcd(j,E), and the trace at a multiple of E is zero by equal degree. This remains true for arbitrary finite abelian character groups.

## p-primary result

- The corrected kernel K_y(v)=1_(v(y)=1)-(1/p)1_(v(py)=1) has expectation (1-1/p)1_(y=0), range of length1, and positive Fourier coefficients of total1-1/p. Its anchored sum vanishes on every Euler-agreement evaluation and has absolute value at most the canceled mass m.
- The coefficient-sensitive bound and all equality constraints follow by exact finite averaging. In mass equality, all nonzero coefficients are +/-1; positive and negative supports each collapse to one value at every mismatching evaluation, with their ratio of exact orderp.
- Fourier inversion then forces the signed function to be a difference of full cosets of a subgroup P. The proof that their displacement must lie in P+X[p] is valid: otherwise duality produces v=pw annihilating P+X[p] but seeing the displacement; disagreement pulls back from v to w, contradicting the order-p ratio at w.
- The actual order-p representative condition is needed; a displacement of orderp only in X/P is insufficient. The corrected C_(p^2) example demonstrates this.
- M=N/p^b uses the SMALLEST invariant-factor exponent b. The mismatch set is closed under p-th-root lifting and under multiplication by p-units. Any nonempty mismatch set therefore contains the generator orbit of a primitive dual element of order at least p^b, giving the claimed floor.
- Attaining that floor forces the entire mismatch set to be exactly one minimum-order primitive generator orbit. Ordinary Fourier support lies there, so the signed function is constant on cosets of a kernel of size M. Integrality forces positive mass at least M; conversely a complement to a smallest cyclic factor supplies degree M, and padding supplies all larger degrees.
- For prime-power k<=M a subgroup of the complement of order k exists. Thus the exact formula for all prime-power degrees follows. The theorem does NOT determine arbitrary non-power degrees below M; this limitation should remain explicit.
- The complete saturated equality condition on the quotient function g is correct. Vanishing of its nonprimitive Fourier coefficients is equivalent to the p-term fibre balance. Integrality gives Galois-invariant primitive Fourier support. Primitive generator orbits have no extra power preimages outside themselves: if dv belongs to such an orbit, p cannot divide d, hence v belongs to the same orbit.
- The quartic rank-two example modulo65 has mismatch density1/8 as stated.

## Analytic transfer and novelty boundary

The smooth GRH estimate with error C_w ||f||_A sqrt(Y) log(2Q) is compatible with the standard compactly supported smooth explicit formula. A unit-interval zero count and rapid Mellin decay give the logarithm of the conductor; higher prime powers cost O_w(sqrt(Y)); omitted ramified primes cost O_w(log Q). This estimate is already in the source article. The derived sufficient window scale O(m^2 log^2 Q) is also available from the elementary anchored trace Re(H(v) overline(v(a))) and should NOT be called a new exponent improvement.

For cyclic groups, the exact cylinder Fourier norm ||1_CI||_A=2^r density(CI) is correct even at prime-power coordinates. The uniform lower window bound handles a negative right-hand bracket by positivity. The weighted Hamming/error-correction consequence and limiting half-distance obstruction follow by the triangle inequality and splitting weights; the maximal normalized prime weight tends to zero.

The minimum-volume signed-array/trade principle is classical background. The new repository-relative statements are the exact fixed-degree cyclic mismatch formula for every composite exponent, and the full arbitrary-p-group extension with its actual torsion-lift equality condition, minimal-exponent saturation floor and threshold, and exact prime-power-degree optima. The GRH estimate, trade bound, finite Fourier inversion, and character duality are inputs, not novelty claims. Worldwide priority remains unproved by a bounded literature search.

## Verification against latest actual Research sources

Fetched and inspected full TeX, rather than only README summaries, from all eight relevant current Research Euler papers, identified by the source manifests in this archive:

1. cubic_quintic_euler_agreement/paper.tex: prime exponent p; final research item explicitly asks composite-exponent extension.
2. grh_cubic_matching_and_precision_2026-11-27/papers/cubic.tex: exponent3.
3. odd_euler_agreement/paper.tex: prime exponent ell; final research paragraph asks prime-power exponent.
4. odd_prime_euler_agreement/paper.tex: prime exponent p; final research item(3) asks exponent p^j or mixed exponents.
5. odd_prime_euler_agreement_2/paper.tex: elementary prime exponent ell; final research paragraph asks composite orders.
6. odd_prime_euler_packets/odd_prime_euler_packets.tex: explicitly says trace equivalence needs prime exponent and does not hold for arbitrary composite exponent; final item(4) asks composite analogues.
7. prime_exponent_euler_agreement/prime_packet.tex: final research item asks exponent ell^m and all power traces.
8. prime_order_euler_agreement/paper.tex: prime exponent ell; final research item asks composite exponent.

These statements establish a concrete advance beyond the inspected repository snapshot. They do not establish priority over all external literature or over later repository commits.
