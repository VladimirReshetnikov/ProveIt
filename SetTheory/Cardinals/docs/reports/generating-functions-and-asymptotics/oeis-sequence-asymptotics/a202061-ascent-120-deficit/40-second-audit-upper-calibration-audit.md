# Independent audit: finite-n calibration and the matching second logarithmic term

Audit date: 2 October 2026. Audited source: `../a202061-second-order-upper/coefficient-upper-second-order.md`, SHA256 `54b44b0864732e831e95596c6915cf06b0caa20551f70b55353f3cc042a26736`. Frozen releases were read but not changed.

## Verdict

The upper-coefficient argument proves

D_n >= C F +(7C/3) F loglog(n)/log(n) - O(F/log(n)),

where F=n^(1/3)(log n)^(2/3) and C=(3 pi^2 alpha^2/(2v))^(1/3).

Together with the separately audited exact-length lower-coefficient construction, this establishes

D_n = C F +(7C/3) F loglog(n)/log(n) + O(F/log(n)).

I found no unresolved gap in the finite-n calibration, its uniform transformed rows, terminal factors, or remainder accounting. The second coefficient is not inferred from the leading theorem's sequential parameter limits. The new proof instead supplies explicit n-dependent cutoffs and quantitative errors. This audit does not determine the next constant multiplying F/log(n), a coefficient amplitude, or a multiplicative equivalent for a_n.

## 1. Analytic input has a uniform neighborhood

The necessary imported analytic estimate is

W_q(s,theta) <= C q^(-3/2) exp(q Psi(s,theta)),
Psi(s,theta)=(s+v theta^2/2)/alpha+O(s^2+|s theta|+|theta|^3),

in one fixed real neighborhood of (0,0), for every positive integer q. It is already proved and independently reviewed in the frozen leading-constant release; the new proof does not need the stronger full local coefficient equivalent.

I checked why the neighborhood can indeed be fixed before n, q, or the calibration. At the critical point the discriminant has distinct positive roots z*=0.198062... and z2=0.881723..., both below 1. Their strict separation and separation from the pole at 1 persist in a small fixed real neighborhood. The explicit square-root coefficient convolution therefore gives a uniform constant and root expansion there; finitely many small q can be absorbed in the same constant. This is an analytic coefficient estimate, not a spectral-radius guess.

For the separate fixed-q convergence step, the positive Narayana representation has eta=x^2 T/(1-x)^2, with eta*=0.127374...<1. Shrinking the same neighborhood makes eta<1 uniformly. Thus every fixed-q generating function is analytic there and converges uniformly to its critical value as its arguments tend to zero. No q-uniform domination of the full unrestricted row is claimed or needed.

The exact algebraic identities Psi_s=1/alpha, Psi_theta=0, and Psi_thetatheta=v/alpha were replayed using the frozen independent identity script; its output is saved in `foundation-identities-replay.txt`. Numerical root values above are only explanatory; the proof relies on the strict certified inequalities and analytic continuity in the frozen argument.

## 2. The endpoint Laplace factor is present

Let kappa=(1/2)log r+loglog r-C0/2. The three ranges in the new tail sum are sufficient:

- Q<q<=r/kappa contributes O(Q^-1/2), because its exponential multiplier is at most e
- r/kappa<q<=r/2 contributes O(sqrt(kappa/r) exp(kappa/2))=O(r^-1/4 log r), uniformly as r tends to infinity
- r/2<q<=r contributes O(r^-1/2 exp(kappa)/kappa)=O(exp(-C0/2))

The final division by kappa is essential: it is the geometric-series endpoint factor responsible for the additional loglog term. Ignoring it would lose the proposed coefficient. Integer endpoints and nonintegral r do not alter any estimate.

Choose Q first so the first tail is a small fraction of 1-m*, then choose the fixed C0 so the last is another small fraction, and only then let n grow. The constants in this ordering are legitimate. The middle error vanishes uniformly for r>=epsilon H, since epsilon H tends to infinity. Finitely many q<=Q contribute at most m*+o(1). No sign splitting doubles this critical mass; sign splitting is used only in the negligible complementary-step estimates.

## 3. Regularized potential and the exact dual inequality

With L=log n, epsilon=delta=L^-12, the potential is

V_n(y)=alpha/[2L(y+epsilon)] [log(H(y+epsilon))+2loglog(H(y+epsilon))-C0].

All logarithms are defined uniformly because H epsilon tends to infinity. Write t=log(H(y+epsilon)). Apart from the positive factor alpha/[2L(y+epsilon)^3], the second derivative is exactly

2t+4log t-2C0-3-6/t-2/t^2,

which is positive uniformly for large n. Thus V_n is strictly convex; its constrained minimizer for Ay+V_n(y) is unique and continuous in A. The value J_n(A) is C1 with derivative equal to that minimizer, including when it lies at a boundary. In particular 0<=J_n'(A)<=R.

For f=g+p y and g'=vp^2/2-J_n(p'), the Hamilton-Jacobi inequality

-f_s+(v/2)f_y^2=J_n(p')-p'y<=V_n(y)

is exact. There is no derivative approximation or error of order loglog(n)/log(n) hidden at this stage.

## 4. Quantitative calibration value

The key infimum inequality is valid with a constant independent of n:

J_n(A)>=2sqrt(B_n A)-C/L sqrt(A)(1+|log A|)-epsilon A.

To verify it, set a=alpha/(2L), u=y+epsilon, lambda=sqrt(B_n/A), and r=u/lambda. Uniformly over epsilon<=u<=R+epsilon,

V_n(y)>=[B_n+a log u-a]/u, and B_n+a log u-a>=B_n/2.

The second inequality holds since log u is bounded below by -12log L; the first uses 2log(log(Hu)/log H)>=-1, valid uniformly for large n. Outside r in [1/8,8], the normalized expression is at least r+1/(2r)>=4. Inside this interval, r+1/r>=2 and the correction is bounded below by -C(a/B_n)(1+|log lambda|). This proves the displayed inequality. It does not suppose that the minimizer lies in an unproved interior region.

The truncated Kepler momentum has

p=O(L^4), p'=O(L^16), p''=O(L^28),

and its weighted integral obeys

integral sqrt(p')(1+|log p'|) ds=O(1).

Indeed the endpoint comparison is s^-2/3(1+|log s|), which is integrable. Also epsilon integral p' ds=O(L^-12 L^4)=O(L^-8), while the two discarded Kepler ends cost O(delta^1/3)=O(L^-4). The reparametrization coefficients differ from 1 by O(delta), so they cause no larger error. Therefore f_n(0,0)>=C(B_n)-O(1/L), with an actual quantitative O(1/L) bound, not a sequential limiting argument.

## 5. Derivative growth and the local transformed row

From 0<=J_n'<=R, the exact identity

g''=v p p'-J_n'(p')p''

gives a C2 norm O(L^28). Also |f_s|=O(L^16) and |f_y|=O(L^4). Boundary minimizers do not obstruct these derivatives because only J_n' is needed.

On e<=H L^40 and |d|<=sqrt(H)L^40, Taylor expansion over a segment inside the rectangle gives

F[f(s,y)-f(s+e/n,y+d/H)]
 =-a f_s e-b p d+o(1),

uniformly, where a=F/n and b=F/H. The absence of a pure d^2 term follows from the affine height dependence. The two remainder scales are bounded explicitly by

O(n^-1/3 L^(109+1/3)) and O(n^-1/3 L^(108+5/6)),

both tending to zero. Thus even the very large fixed logarithmic exponents do not invalidate uniformity.

The linear tilts satisfy |lambda|<=a O(L^16), |theta|<=b O(L^4), so they tend to zero uniformly. Multiplying the discriminant remainder by q<=RH still gives o(1): H times a product of the relevant vanishing tilts is n^-1/3 or n^-2/3 times a fixed logarithmic power. The exact potential inequality then gives

q Psi(lambda,theta)<=kappa(r) q/r+o(1), r=h+epsilon H.

Since h<=r and r>=epsilon H tends uniformly to infinity, the row estimate in Section 2 applies without any lost small-height regime. The small-q part tends to its true critical mass rather than twice that mass.

## 6. Complementary lengths and increments

The unrestricted transformed exponent is bounded by

C a L^16 e+C b L^16 |d|.

This follows directly from the global derivative bounds on the rectangle. It suffices for both complementary regimes.

For e>H L^40, an additional fixed positive length tilt lambda0 stays in the same analytic neighborhood. Summing all destinations and q<=RH costs at most exp(O(H)), whereas Chernoff gives exp(-lambda0 H L^40). This tail is o(1).

For |d|>sqrt(H)L^40, use an extra signed tilt theta0=c L^40/sqrt(H), which also tends to zero. The negative Chernoff exponent is -cL^80. The positive generating exponent is at most

C_R c^2 L^80+O(L^57).

The L^57 term includes the cross term between bL^16 and theta0; the base quadratic and length terms are smaller. Choose fixed c sufficiently small after R and the fixed analytic constants. The resulting exponent is at most -cL^80/2+O(L^57), which tends to minus infinity. The discarded discriminant remainders are themselves o(1). Splitting the two signs only in these negligible tails is legitimate.

Consequently the full transformed row is bounded by one fixed m_bar<1, uniformly in elapsed length, height, and n sufficiently large. It is not necessary to retain any independence among rows.

## 7. Exact telescoping and terminal factors

The positive sum over transformed prefixes is bounded by 1/(1-m_bar). Undoing the telescope introduces exp(-F f_n(0,1/H)). At elapsed macro-length k and height h the original terminal factor is exactly rho^(n-1-k)t^(1-h), apart from the initial rho.

The bound f_n(s,y)<=p_n(1)y+C L^16(1-s) gives the residual exponent

(n-1-k)[log rho+O(aL^16)]+h[-log t+b p_n(1)]+O(1).

Both corrections tend to zero, so the residual is bounded by a constant independent of k,h,n. A terminal height near the strip ceiling is therefore covered; the proof does not assume a return to a small height. The initial shift costs F[f_n(0,1/H)-f_n(0,0)]=b p_n(0)=o(1).

The imported first-hit estimate applies at fixed strip ceiling RH since RH/n tends to zero. Choosing fixed R with R^2/(4D0)>C+1 makes paths leaving the strip exponentially smaller than the desired bound. This comparison needs only the lower estimate f_n(0,0)>=C(B_n)-O(1/L); no unproved upper bound on the calibration value is needed.

## 8. Expansion and scope

The identity log H=(2/3)L+(1/3)log L gives

B_n=alpha/3+(7alpha/6)log L/L+O(1/L).

Since C(B)=3(pi^2 B^2/(2v))^(1/3), its expansion is

C(B_n)=C[1+(7/3)log L/L]+O(1/L).

The quadratic expansion error O((log L)^2/L^2) is O(1/L), as required. Every calibration error is O(F/L), while renewal and terminal prefactors contribute only O(1). This proves the matching bound and hence the two-sided second-logarithmic expansion.

The finite-height addendum and any proposed exact finite-height constant are separate results outside this main audit. The coefficient expansion is rigorously established without them.
