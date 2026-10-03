# Independent mathematical audit: divisor-marked assemblies

Audit date: 1 October 2026. Scope: the local `divisor_assembly_asymptotics.tex`, `verify_divisor_assembly.py`, and `verification.json` in the producer directory. No producer file was modified and no external write was made. The latest threshold-envelope paragraph and further-questions section were included in the final review. Source hashes are recorded in `audit_results.json`.

## Verdict

**No blocking mathematical defect found.** The stated multiplicative equivalent, arbitrary finite relative expansions, factorial-core reversion, exact-input absolute-o(1) inverse, and qualified integer-threshold enclosure are supported by the arguments given.

This is an independent human/symbolic/numerical audit, not a formal proof certification. Literature/priority and repository-search claims were outside the mathematical audit and were not independently re-run.

## Independent checks completed

- Derived the shifted local phase directly from the logarithmic singular term and the saddle identity; checked its formal coefficients through weight 10.
- Computed R0 through R5 with a weight-partition sum, independently of the producer's exponential recurrence. All six exactly match the reported rational functions.
- Checked the Mellin residues at zero and the first three negative odd integers.
- Constructed the generating-function coefficients independently by multiplying the finite power series exp(d(k)z^k), through n=45; compared them with exact integer coefficients.
- Recomputed exact integers through n=1200 with the Bell-polynomial/binomial recurrence, and reproduced all seven numerical rows in the producer report, including every J=0,...,5 relative residual and both inverse errors.
- Checked the first three Lagrange reversion coefficients by direct substitution into the implicit equation with arbitrary g, rather than just manipulating the stated inverse operator.

The executable audit is `audit_checks.py`; its machine-readable output is `audit_results.json`. It finishes in approximately 14 seconds in the audited environment. An optional first command-line argument selects the source directory, so an archive containing `audit/audit_checks.py` can be replayed from its release root with `python audit/audit_checks.py .`.

## 1. Mellin constants, signs, and shift

The Dirichlet series is zeta(s)^2. At s=1, the product Gamma(s) zeta(s)^2 has principal part (s−1)^−2 + gamma(s−1)^−1: the two Euler constants from zeta(s)^2 combine with Gamma'(1)=−gamma. Thus the logarithmic singular term is (log(1/t)+gamma)/t, not a term involving 2gamma.

At zero the residue is zeta(0)^2=1/4. At negative odd integers the gamma residue is negative, so

c1=−1/144, c3=−1/86400, c5=−1/7620480.

The double zeta zeros remove the gamma poles at negative even integers. Moving the Mellin contour in a closed proper subsector of the right half-plane gives arbitrary algebraic depth; the gamma decay dominates the argument-dependent factor in t^(−s). Fixed derivatives are handled by multiplying by a polynomial in s and the corresponding power of t. No additional unaccounted residue is present.

Consequently L(w)+nw has linear analytic term (n−1/144)w. The n−1/144 sign is correct. Solving the singular stationarity equation gives u=log(1/t)+gamma+1 and (n−1/144)t²=u; the displayed Lambert W expression is the positive solution. Its stationary action is (2u−1)/t and its Gaussian curvature is D/t³, giving the e^(1/4)t^(3/2)/sqrt(2pi D) prefactor exactly.

## 2. Minor arcs and arbitrary-order Gaussian remainder

The geometric-series lower bound for sum r^k(1−cos(k theta)) is algebraically correct. Since d(k)≥1, it is a valid lower bound for the full loss of real part, including near every root of unity. For |theta|≥c0 t it gives a uniform exp(−c/t) loss. This bound is more than enough for every fixed algebraic expansion order and does not require special root-of-unity cancellation.

On |theta|≤c0 t, the fourth-order cosine inequality gives the stated quarter-curvature bound after using K4/K2=O(t^−2). The central cutoff log(1/t) in Gaussian units fits inside this inner arc, since its ratio to t is O(sqrt(t/log(1/t)) log(1/t))→0.

At the exact saddle, the normalized j-th cumulant is O(eta^(j−2)), eta²=t/log(1/t). Taylor's integral remainder can indeed be bounded by K_j(t): along the imaginary segment, the positive exponential series gives |L^(j)(t−i theta)|≤K_j(t). Thus phase truncation through degree 2m+3 has a remainder O(eta^(2m+2)|x|^(2m+4)). On the chosen cutoff, eta(1+|x|³)=o(1), so exponentiation and weight truncation have the stated fixed-polynomial Gaussian majorant. Integrating this majorant, rather than evaluating it at the cutoff, removes any spurious logarithmic loss.

Odd weight has odd total power of x and vanishes on a symmetric interval. The intermediate Gaussian tails are exp(−c log²(1/t)), and the outer tails are exp(−c/t); multiplication by the inverse central width preserves their beyond-all-fixed-orders character. These observations validate the exact-saddle O(epsilon^(m+1)) error, with constants allowed to depend on the fixed truncation order.

At the shifted saddle, exact stationarity of the full L is not needed for the modulus bounds. The omitted analytic phase is retained in the generator, including its constant and linear-in-Gaussian pieces. Fixed-order Mellin truncation is uniform on the central segment, where w/t→1. Bounded rational coefficients and the same integrated Taylor argument establish O_J(t^(J+1)). No differentiation of an uncontrolled sequence remainder is used later in the inverse proof.

## 3. Generator and first coefficients

With w=t(1−vz), v=sqrt(t), and z=iZ/sqrt(D), the singular/core phase minus its constant and quadratic terms is

sum over j≥3 of (u+H_j−1) z^j v^(j−2).

The analytic remainder is sum c_p v^(2p)(1−vz)^p. This confirms both signs and powers in the formal generator, including the minus sign in (1−vz)^p. Gaussian parity makes the final coefficients rational functions of u despite the intermediate square roots of D.

Independent partition summation exactly reproduces the displayed R1 and R2 and all reported R3–R5. R3−c3=O(u^−3), as claimed. The two-loop signs are consistent with i^6=−1, i^8=1, i^10=−1, i^12=1. The logarithmic-coefficient recurrence follows correctly from differentiating the formal logarithm.

The stated simpler relative bound follows: R1=O(1/u), R2=O(1/u²), and t³=o(t/u). In particular its logarithmic scale is (n log n)^−1/2.

## 4. Factorial-core inverse and uniform reversion

The correct dominant inverse variable is X=y/W(y/e), satisfying X(log X−1)=y. Writing f(x)=x(log x−1), h=f^−1, and G=g∘h, ordinary Lagrange inversion in f(x) gives the coefficient

(−1)^k/k! times (d/dy)^(k−1)[h'(y) G(y)^k].

Since h'(y)=1/log X and d/dy=(1/log X)d/dX, this is exactly the manuscript's operator applied to g(X)^k/log X. The operator must act on every X-dependent factor, as explicitly stated. Direct implicit substitution checks the first three coefficients. Differentiating the saddle identities gives u'=t²/D, t'=−t³/D, and S'=t, so the newly added explicit formula g0'=psi(X+1)−log X+t−3t²/(2D)−t²/D² is also correct. These identities were numerically checked independently at every reported inverse input. In particular the two-term formula contains the necessary negative term −g²/(2X log³X).

The complex-disk proof supplies uniform finite-order errors: on |x−X|=cX, f(x)−f(X) has size comparable to X log X, whereas g_J(x)=O(sqrt(X log X)). All chosen branches are analytic on a sufficiently small fixed relative disk centered on a sufficiently large positive X; Gamma has no zero or pole there, the Lambert branch is regular, and the finite correction factor is uniformly close to one. The derivative of f differs from log X by O(1), which also gives univalence on this convex disk. Rouché therefore gives one simple root for |lambda|<c''sqrt(X log X). Cauchy bounds on that root produce exactly

O(X^((1−K)/2) (log X)^(-(K+1)/2)).

The explicit model derivative is log x+O(sqrt(log x/x)), so sequence-to-model transport uses only a mean value theorem, not a presumed smooth continuation of the actual sequence. J≥K makes its transport error smaller than the displayed K-th-order reversion remainder. With J=0 and K=2, the sharper relative coefficient error produces transport of the same order as the claimed O(X^−1/2 log^−3/2X) two-term inverse remainder.

## 5. The +1/4 and integer thresholds

Combining Stirling's half-logarithm with the saddle prefactor yields

g0(X)=S(X)−(1/4)log X+(3/4)log u_X−(1/2)log(2u_X+1)+1/4+O(1/X).

Therefore the first inverse correction contributes +1/4, while the remaining prefactor terms divided by log X are O(log log X/log X). The second reversion term is O(1/log X). This proves the asserted exact-input absolute-o(1) approximation. Retaining the full Lambert S(X) is essential: replacing it by its leading equivalent does not have the claimed absolute accuracy.

The latest threshold paragraph explicitly restricts to sufficiently large real Y, correctly avoiding a domain issue with log Y and the large branch of the smooth inverse. The upper and lower smooth envelopes Phi_J±C t^(J+1) have positive derivatives eventually. Their inverse endpoints x_- and x_+ give ceil(x_-)≤I(Y)≤ceil(x_+). This inequality is valid even when an endpoint is an integer; it is not an illicit ceiling-of-an-asymptotic argument. The sharper J=0 envelope scale and the warning near integer jumps are consistent. No effective starting index or globally unconditional rounding rule is asserted.

## Nonblocking suggestions

1. A producer-script comment originally claimed an exact-saddle numerical diagnostic that was not implemented. The producer trimmed that comment during audit. This issue is resolved and never affected a theorem or numeric result; adding such a diagnostic remains optional.
2. For maximal exposition, the Gaussian-remainder proof could display the bound |L^(j)(t−i theta)|≤K_j(t) and its ensuing polynomial remainder explicitly. The current argument already has enough information to justify it.
3. Effective constants and a certified starting index remain genuinely unproved and are correctly listed as future work. Numerical agreement through n=1200 should not be presented as such a certification.
