# Degree-four three-attachment positivity: independent exact audit

## Verdict

APPROVED. Independent exact replay passed all 53,722 rational target identities and complete coverage of all 204,388 nonnegative-integer population faces. Together with the approved exhaustive kernel, this proves the complete three-attachment sector. No mathematical gap or certificate failure was found.

## Scope

This note explains the independent positivity verifier `audit_positivity.py`. The authoritative completion verdict and exact counters are in `positivity_audit.json`, which is written only after every identity, every input gap, every necessary population face, and unchanged input hashes have passed. The companion `KERNEL_COVERAGE_AUDIT.md` independently establishes the complete template domain and every support coefficient.

The population domain is the nonnegative integers. A shifted-positive face certificate also proves positivity for real active populations at least one, but it does not assert positivity when a population is strictly between zero and one.

## 1. Reconstructing the exact target inequalities

For each of the 3,437 distinct input gamma arrays, the verifier rebuilds the binomial population kernel

γ_k(M)=Σ_q c_(k,q) ∏_t binom(M_t,q_t),   |q|≤3.

It constructs each falling-factor polynomial by direct multiplication of x, x−1, x−2, divides by the appropriate factorials, and sets G_k=6γ_k. The multiplier six clears every denominator because the total quota is at most three. This uses the arrays independently approved by the Hall recount, rather than importing the producer's transform matrices.

The two polynomials reconstructed by direct sparse multiplication are

P_2=4G_2²−9G_1G_3,
P_3=3G_3²−8G_2G_4.

They are exactly 36 times the second and third order-four Newton gaps. Their total degrees are at most four and six respectively. In particular neither the factor six nor the factor 36 changes any sign.

## 2. Independently verified coefficient certificates

The verifier recomputes the monomial-to-binomial transform using finite differences:

x^n = Σ_k (Σ_(j=0)^k (−1)^(k−j) binom(k,j) j^n) binom(x,k).

For every n≤6 it separately validates this polynomial identity at all seven points x=0,...,6; degree at most six makes those tests an exact identity verification. The multivariable transform is its tensor product. A polynomial with nonnegative coefficients in this binomial basis is nonnegative at every nonnegative integer population.

Every advertised binomial-positive ID is compared with the independently computed set; non-advertised inputs are also checked. No producer Stirling table, NumPy multiplication, or classification routine is imported.

## 3. Complete integer population faces

For a family with d variables, each integer population vector belongs to one of exactly 2^d disjoint cases:

- M_i=0 when the i-th mask bit is absent
- M_i=1+y_i, y_i≥0, when that bit is present

For every input not already certified by nonnegative binomial coefficients, the verifier reconstructs every such face directly by the binomial theorem. Faces whose resulting monomial coefficients are nonnegative are immediately proved nonnegative. The exact set of inputs for which all faces are coefficient-positive is independently compared with the producer's classification.

Every other face must have exactly one alias to a certified target. The verifier checks the complete alias domain and rejects missing aliases, repeated aliases, aliases attached to already coefficient-positive faces, and extraneous unused aliases.

An alias records a positive integer scale and an ordered list of face coordinates. The verifier proves the following exact equality, term by term:

face polynomial / scale, after the recorded coordinate permutation and deletion of unused variables, = normalized target polynomial.

Every omitted coordinate is checked to have exponent zero in every face term. The permutation is injective, dimension-compatible, and in range; no two distinct terms may collapse. The scale is independently recomputed as the positive gcd of the face coefficients. Comparison uses exact polynomial tuples, not numerical evaluations or hashes. Thus correctness does not depend on the producer's canonical-normalization algorithm finding a genuine orbit minimum.

All 6,874 gap inputs, all required masks, all 63,917 aliases, and all 53,722 normalized targets must be accounted for before the completion receipt is written. A global binomial certificate covers every integer face of its input directly.

## 4. Rational nonnegativity identities

The consolidated ledger has 53,477 binomial-square identities and 245 general-square identities. Each identity expresses its target as a sum of terms of either form

w y^m (u y^a−v y^b)^2,

w y^m (Σ_e c_e y^e)^2,

and positive monomials w y^e. All exponents are nonnegative integers; all displayed weights w are checked to be strictly positive rational numbers. Coefficients inside a square may be arbitrary rational numbers.

Every such term is nonnegative on the nonnegative real orthant: the monomial factor is nonnegative and the squared factor is nonnegative. The independent verifier expands every square using Python's unbounded-integer `Fraction` arithmetic, adds every term, removes exact zeros, and checks equality with the complete integer target polynomial. It checks every target ID and certificate ID in sequence and requires one certificate for every target.

No numerical linear-programming solution, floating-point tolerance, producer verification routine, or finite population grid is used as evidence for these identities.

## 5. First gap, actual degree, and the resulting theorem

The remaining first order-four gap has a direct general argument. Form a graph whose vertices are the directed off-diagonal relation arcs, joining two arcs when their four endpoints are distinct. Its clique number is the comparability matching number, at most four. Its vertex count is γ_1. Each feasible two-pair ordered support has at least one pair of compatible arcs, so γ_2 is at most this graph's edge count. Turán's bound therefore gives

γ_2 ≤ 3γ_1²/8.

This proves 3γ_1²−8γ_2≥0 independently of any population certificate.

For every integer population with actual gamma degree four, the three order-four Newton inequalities are consequently certified. The coefficient sequence has no internal zeros: deleting pairs from a feasible largest support supplies feasible supports of every smaller size. If the actual degree drops below four, the previously proved degree-at-most-three preorder theorem supplies the stronger normalization at that actual degree; order-four inequalities alone are not substituted for it.

Combined with the independently audited exhaustive kernel and all-population component pruning, these facts prove actual-degree ultra-log-concavity throughout the canonical Gallai--Edmonds three-attachment sector. They do not by themselves settle the four-attachment sector or the full degree-four conjecture.

## 6. Reproduction and immutable inputs

Run `python3 audit_positivity.py` with ordinary Python 3 and assertions enabled. It uses only the standard library. The verifier reads the six authoritative certificate/data files and the original template file, but never imports producer code. Input SHA-256 digests are computed before and after the entire audit; any concurrent change prevents a successful receipt.

The output `positivity_coverage.jsonl` records the proof route for each input gap and, where necessary, each population face. `positivity_audit.json` records the complete counters, input hashes, verifier hash, ledger hash, minimum positive rational weight, and runtime. The companion kernel receipts pin the same support-array files.
