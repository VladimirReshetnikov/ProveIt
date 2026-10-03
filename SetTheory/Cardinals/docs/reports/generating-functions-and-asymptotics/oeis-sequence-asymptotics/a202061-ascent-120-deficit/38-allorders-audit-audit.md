# Independent adversarial audit: all finite inverse-logarithmic orders

Date: 2 October 2026. This is a new research audit, separate from the frozen third-order release.

## Verdict

**Approved within the stated imported analytic dependencies.** The coefficient-to-action reduction and the endpoint-safe deterministic action expansion together establish the all-finite-orders inverse-logarithmic sector of the logarithmic deficit. There is no unresolved row-normalization, concentration, exact-repair, convex-calibration, endpoint, inversion, or finite-order uniformity obstruction.

For every fixed integer J>=1, put L=log n, F=n^(1/3)L^(2/3), and B=kappa+(7/3)log L. Then

    D_n = C F [sum_(j=0)^J P_j(B)/L^j + o(L^(-J))].

The polynomials are given by the audited recurrence in action-expansion/proof.md. Their leading coefficients are binomial(2/3,j)(3/2)^j, and in particular

    P0=1,
    P1=B,
    P2=-B^2/4+(7/2)B-10.

The constants are those of the approved third-order kernel: C=alpha/Y0, Y0=(2v alpha/(3pi^2))^(1/3), kappa=log Y0-2log3+2c_*.

The indexing is worth making explicit. To prove the expansion through F/L^J, use the reduction with K=J-1 and N=K+3=J+2, exactly satisfying the scalar theorem's N>=J+2. The leading-only case follows immediately. Each order is fixed before n tends to infinity.

This does **not** prove a multiplicative asymptotic equivalent for a_n, a power-law prefactor, convergence of the formal infinite series, uniformity for growing J, or an exponentially complete transseries. P3/P4 printed by the producer are ancillary outputs; this audit independently checks P2 and the general recurrence, rather than claiming a separate second implementation of those two extra polynomials.

## Inputs and audit boundary

The new sources reviewed are:

- ../a202061-allorders-research/classical-action-reduction.md
- ../a202061-allorders-research/action-expansion/proof.md
- the action-expansion generation and verification scripts

The imported sources are the approved exact positive macro representation, analytic square-root transfer with uniform parameter derivatives, critical derivative identities, local positive Gaussian lower bound, and fixed-ceiling first-hit estimate, as incorporated in:

- ../a202061-third-order-upper-audit/lower-construction-audit.md
- ../a202061-third-order-upper-audit/one-sided-next-constant-proof.md
- ../oeis-a202061-third-order-report/

This audit checks their use at stronger precision, not a new proof of the entire imported enumerative foundation. It does not modify a frozen release. Exact source hashes are recorded separately after the small clarifications discussed below.

## 1. Row Watson expansion and inversion

Write B_q(s,theta)=W_q(s,theta) exp(-q Psi(s,theta)). The imported differentiated transfer plus finitely many positive small q gives uniformly bounded first logarithmic derivatives of B_q. Thus

    B_q(s,theta)=B_q(0,0)[1+O(|s|+|theta|)]

uniformly in q. A bounded-mass scalar envelope therefore permits the all-q replacement without losing the critical small-q mass m_*.

The split at r/k^2 and r/2 is valid in k=(log r)/2+log log r+O(1):

- The perturbation of the critical head is O(r^(-1/2)); subtracting its missing tail costs O(k r^(-1/2))
- The tilted middle is O(r^(-1/4) times a fixed power of log r)
- On the final half, replacing q^(-3/2) by its endpoint integral costs relative O(k/r); the transfer's O(1/q) correction costs relative O(1/r)
- Taylor expansion of (1-u)^(-3/2) and the Laplace moments gives (3/2)_j k^(-j), with a controlled finite remainder

The finite fractional last term costs the same O(k/r) relative error. All algebraic-r errors are smaller than every fixed inverse-log order on r>=H L^(-E).

The logarithmic implicit derivative is 1+O(1/log r), bounded away from zero. Finite substitution therefore proves the stated root expansion with remainder

    O((1+log log r)^(N+1)/(log r)^(N+1))
      + O(r^(-1/4) (log r)^c).

The discrepancy r Psi(s_r,0)-r s_r/alpha=O((log r)^2/r) is already absorbed. Our independent symbolic check verifies the displayed p1, p2, p3 directly in the original implicit equation.

### A clarification incorporated during review

The upper-row hypothesis gives only k<=k_N-delta+o(delta); actual k need not lie in the endpoint band. First dominate by the critical scalar envelope G_r(k), then use its positivity and monotonicity to replace k by the endpoint-band upper bound. Only then invoke the local derivative, which tends to 1-m_*>0. This proves the row gap uniformly even for much smaller k. The author has incorporated this clarification.

No arbitrary h derivatives of the fractional-cutoff root are used. That root is merely continuous and piecewise C1 at integer knots. The lower construction uses its audited one-sided first derivative bounds; smooth derivatives belong to the explicit truncation or a finite smooth inverse surrogate. This resolves the regularity hazard in the original plan.

## 2. Action, reciprocal height, and fixed endpoints

For any decreasing positive potential in the audited range, the square inequality gives the peak lower bound

    J_a(Y)=n V(Y)+2sqrt(2/v) integral_a^Y sqrt(V(h)-V(Y)) dh.

Its interior minimum satisfies the exact duration equation; at a fractional-cutoff junction both one-sided derivatives have the same continuous duration bracket and strictly negative prefactors. Thus the lower construction has an actual exact-duration arch without assuming smoothness or uniqueness of the rough potential.

A shifted Kepler trial has action O(F). Kinetic coercivity bounds its peak by O(H); the potential part and log Y asymptotic give Y>=cH. Constants can depend on the fixed requested order but not n.

For h<=Y/2, V(h)-V(Y) is comparable to log h/h. For the peak half, it is comparable to (L/Y^2)(Y-h). These imply

    endpoint action below a <= C sqrt(a log a),
    integral_0^n dt/h(t) <= C sqrt(Y/L) = O(M0).

For the second estimate, splitting at Y/L^C with C>2 bounds the small-height part by O(sqrt(Y)L^(-C/2)) and the remaining part by O(sqrt(Y/L)). There is no hidden divergence at fixed h_b.

Changing the equal endpoints from a1 to a2 at fixed duration costs at most

    2sqrt(2/v) integral_(a1)^(a2) sqrt(V(h)) dh.

This follows either by comparing the two peak minima or by the endpoint-momentum formula. Hence fixed changes of h_b cost O(1), raising to h0 costs only a fixed power of L, and raising to H epsilon costs O(F sqrt(epsilon)). No informal zero-height evaluation of log log h is used.

## 3. Tunable independent-row construction and exact repair

Fix K. The explicit choices are

    B0=K+3, eta=L^(-B0), A0=4B0+10, h0=L^A0,
    N=K+3, r=M^(3/4)+O(1), M comparable to M0=F/L.

(The subscripted B0 here is a cutoff exponent, not the classical leading potential constant.) The fractional cap factor 1-2eta eventually lies in [1/2,1]. Every constant in the derivative, moment, and mean estimates can therefore be chosen uniformly in eta. The laws remain independent and retain the entire critical head.

The permitted tube is eta h/10. Below half-height, variance is at most C L h^(3/2)/sqrt(log h). The deterministic drift error divided by eta h is at most

    C L^(2+B0-A0/2)/sqrt(log L) + C/(M eta) = o(1).

The Bernstein exponent is at least

    c eta^2 sqrt(h log h)/L
      >= c L^(A0/2-2B0-1) sqrt(log L)
      = c L^4 sqrt(log L).

Its quadratic-regime ratio is O(eta sqrt(log h/L)), so the quoted quadratic exponent is legitimate. At the peak the corresponding ratio is O(eta) and the exponent is at least c eta^2 F/L. Both dominate log M=O(L). The union over all boundaries therefore succeeds with probability 1-o(1). Complementary suffix reconstruction does not condition the laws. The cap lies safely below the actual source height, since eta h tends to infinity even at h0.

The total-degree bias remains O(HL), degree fluctuation is bounded by LH sqrt M, and the gap by L sqrt(nL). The symmetric omitted patch has deterministic equal edge heights and expected degree asymptotic to r(1-m_*)Y/alpha. Since r/(L sqrt M) tends to infinity, every retained realization has positive residual degree with that same relative asymptotic.

The local patch uses the entire exact macro degree, subtracting one only when applying the imported internal-block estimate. Its q-saddle is (1-m_*)Y[1+o(1)], with a fixed positive margin below source height. The rounded height increments sum exactly to the gap and stay in the allowed local Gaussian range. Both integer constraints hold for every retained realization. Fixed patch positions allow deletion to recover the outside marked data, so the weighted count is injective; fractional factors are <=1.

## 4. Complete finite-order error ledger

Let Q_K=M0/L^K denote the target. Constants below depend only on fixed K and the imported kernel.

- Lower normalization: O(M L^(3/2-A0/2)); divided by Q_K this is O(L^(-K-19/2))
- Interior summation by parts: O(M L eta); relative error O(L^(-2))
- Central boundary terms: O(r L eta); relative error O(M^(-1/4)L^(-2))
- Patch and omitted central action: O(M^(3/4)L+M^(1/4)L^3); relative error O(M^(-1/4)L^(K+1)+M^(-3/4)L^(K+3))
- Seeds and deterministic rounding: fixed powers of L, hence o(Q_K)
- Stieltjes quadrature: O(L^2), hence o(Q_K)
- Retained-event logarithm: o(1)
- Bulk root truncation: O(M0 (1+log L)^(K+4)/L^(K+4)); relative error O((1+log L)^(K+4)/L^4)
- Bulk cutoff displacement: O(M0 eta L); relative error O(L^(-2))
- Height region below H L^(-2K-8): O(F L^(-K-4)); relative error O(L^(-3))
- Soft upper endpoints, epsilon=L^(-2K-8): the same O(L^(-3)) relative error
- Upper potential slack, delta=L^(-K-2): O(M0 delta); relative error O(L^(-2))
- Upper renewal prefactor: O(log L), hence o(Q_K)
- Analytic Taylor and amplitude errors: n to a fixed negative power times a fixed power of L, hence o(delta) at the row level and harmless at the final scale

Macro-duration rounding changes total degree by O(H), included in the patch allowance, not an unaccounted O(M) action term. No item in this ledger relies on an unspecified o(M0) bound being automatically improvable.

## 5. Exact convex calibration and transformed rows

For U_n(y)=(n/F)[phi_N(H(y+epsilon))-alpha delta/(H(y+epsilon))], positivity, decrease, and convexity hold on the whole half-line for large n. On a fixed bounded y range its derivatives have the stated powers of y+epsilon.

The direct method, convexity, and the nonnegative first variation give y_n''<=v U_n'(y_n)<0 in distributions. Thus the minimizer has strict interior positivity, solves the smooth Euler equation, is symmetric, and has a peak in a fixed positive compact interval. An O(1) Kepler-trial bound together with kinetic coercivity makes this compactness independent of n. The energy integral gives integral dt/(y_n+epsilon)<=C.

Set p=-y_n'/v and J(A)=min_y(Ay+U_n(y)). Because p'=-U_n'(y_n), the optimizer in J is exactly y_n. Integration by parts then proves

    f(0,0)=integral_0^1[y_n'^2/(2v)+U_n(y_n)]dt.

This is an exact value identity; there is no omitted perturbative Legendre error. The constrained Legendre value has the required C1 regularity, enough for the C2 bound on f. Every derivative grows as a fixed power of L because epsilon is a fixed inverse power.

On the good-step region, Taylor errors are n^(-1/3) times a fixed power of L. The HJ inequality gives r Psi<=k_N(log r)-delta+o(delta), uniformly from r=H epsilon through (R+1)H. The corrected scalar row-gap argument gives 1-c delta.

For large degree, an extra fixed positive length tilt gives exp[-cH L^T+CH]. For large height increment, an extra tilt cL^T/sqrt H gives a negative -cL^(2T) with positive quadratic C_R c^2L^(2T); choose c small and T>P+2. Cross terms, including the unlisted base-height term L^(2P+1), are absorbed by the listed O(L^(P+T+1/2)). Cubic errors are still algebraically small in n. Thus omitted steps are o(delta), not merely o(1).

The Neumann norm is O(delta^(-1)). The terminal factor is uniformly bounded because its corrections are o(1) relative to the fixed negative log rho and -log t_*. The initial-height correction is o(1). A fixed R can be chosen using any fixed upper bound on the trial action so that the imported first-hit exponent strictly exceeds it; no unproved next action coefficient is needed here.

## 6. Endpoint-safe scalar expansion and inversion

The scalar proof treats the lower height cutoff before expanding. With z=h/Y and delta=T^(-C0), the actual tails obey

    I_+ small-z tail = O(sqrt delta),
    I_- small-z tail = O(sqrt T delta^(3/2)).

The coefficient tails are bounded by O(sqrt delta times fixed powers of log delta). Choosing C0 after the fixed expansion order makes every tail smaller than the required inverse power. This works for an actual fixed core b even though the pointwise large-height expansion fails there.

At the peak, factoring (1-z)/z leaves the removable expression

    [k_N(T+log z)-k_N(T)]/[k_N(T)(1-z)].

It is uniformly O((1+|log z|)/T) on z>=delta. Each expanded numerator has a zero at log z=0, and products give moments log(z)^m/(1-z)^r with m>=r. The two beta weights then make every coefficient genuinely integrable at both endpoints. Analytic continuation of the beta derivative is valid precisely because the differentiated integrand is convergent; it is not being used to assign a value to a divergent integral.

The derivative needed for inversion can also be checked directly. In the small-z region, q_T>=c/T and |partial_T q_T|<=C/T imply the differentiated I_- tail is O(sqrt T delta^(3/2)), plus an exponentially small moving-lower-limit term. On z>=delta, differentiating the removable expression gives O(T^(-2) times a fixed power of log T). Thus

    d(log n)/dT=3/2+O(1/T),

bounded away from zero. Finite residual bounds therefore imply equal-order inverse errors by the mean-value theorem. This supplies a concrete derivative check instead of differentiating an unspecified asymptotic remainder.

The peak-k recurrence follows directly by subtracting two copies of the finite smooth surrogate equation. It is a formal contraction with derivative O(1/k) for |log z|<=C0 log k. The duration relation and algebraic elimination of Y then give the stated universal q and action recurrences. Every operation is at finite order and has already been justified by uniform remainder bounds. The top degree of P_j comes only from the j-fold leading B contribution in q^(2/3), proving the displayed leading coefficient and universality.

## 7. Independent checks and minor clarifications

The script independent_checks.py does not import producer code. It verifies:

1. p1, p2, p3 in the original row implicit equation by exact symbolic cancellation
2. P1 and P2 from a separate finite hand expansion of the normalized peak integrals
3. Four convergent beta-log moments by direct 65-digit quadrature
4. The fixed-core, unexpanded action integrals at T=100,200,400,800, agreeing with the P2 scale

These checks corroborate, but do not replace, the analytic proof. Their stdout is in independent-checks-output.txt.

Review led to minor clarifications, none of which changes a coefficient or parameter choice: scalar monotonicity before using the root-band derivative; a direct first-duration-derivative tail estimate; and an elementary two-interval proof of |log z|/(1-z)<=C(1+|log z|). The row-gap clarification is incorporated in the source. The author has also incorporated the direct derivative estimate in the scalar source; the bound is recorded above for completeness.

**Final conclusion:** the all-finite-orders reduction and scalar recurrence are mathematically supported at the claimed logarithmic-deficit precision. The new explicit fourth-scale coefficient P2 is approved. The required proof scope remains a single inverse-logarithmic sector.


## 8. Added inverse-threshold corollary: approved

The later source action-expansion/inverse-scaling.md was reviewed separately. Define lambda=log mu>0, N(p)=min{n:a_n>=p}, T=log p and S=log T. Then, for every fixed J,

    N(p)=T/lambda
      + C lambda^(-4/3) T^(1/3) S^(2/3)
          sum_(j=0)^J P_j(kappa_inv+(7/3)log S)/S^j
      + o(T^(1/3) S^(2/3-J)),

where kappa_inv=kappa-(2/3)log lambda.

The factor lambda^(-4/3) includes both the leading inverse slope lambda^(-1) and the n^(1/3) rescaling lambda^(-1/3). In the peak-k duration equation the parameter pair (L,kappa) enters through L+(3/2)kappa, while the action divided by C n^(1/3) depends only on k. Thus the formal covariance is valid to every finite order. Ordinary Taylor expansion of the finitely many polynomial-log terms then proves its quantitative uniform bounded-shift version. This avoids requiring an exact covariance identity for the unexpanded fixed-core action itself, whose core contribution can differ by O(1).

The inverse argument differentiates only the explicit smooth finite truncation d_J. Its derivative is O(T^(-2/3)S^(2/3)) at x=T/lambda+O(T^(1/3)S^(2/3)); multiplying by that displacement gives o(1). The exact sequence remainder is used solely at the two nearby integer comparison points. Its eventual all-integer little-o bound is uniform over those points simply by the definition of little-o, and their target scales remain comparable. Since every fixed target T^(1/3)S^(2/3-J) tends to infinity, floor/ceiling errors are negligible. The epsilon squeeze therefore gives the claimed inverse remainder without assuming any derivative or smooth interpolation of the exact discrete deficit.

For the monotonicity input, the imported foundation identifies a_n as the number of classical 120-avoiding ascent sequences. Appending a copy of the last letter preserves the ascent bound. Any new 120 using the final copy would already exist using the preceding copy; equality precludes using both as two distinct-valued pattern entries. The operation is injective. Thus a_n is nondecreasing, and the positive exponential leading term makes the threshold finite.

There is no inverse o(1) error claim or exact rounding formula. This corollary is approved at each fixed retained scale only.
