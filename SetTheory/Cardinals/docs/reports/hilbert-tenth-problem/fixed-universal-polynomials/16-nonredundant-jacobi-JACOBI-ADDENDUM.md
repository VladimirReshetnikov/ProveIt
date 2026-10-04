# A fixed-modulus Jacobi obstruction and infinitely many certified misses

Independent audit and extension of the root proposal, 3 October 2026.

## Result and scope

The frozen parent theorem constructs infinitely many positive reduced-system tuples for each actual fixed complete75 compiler export and each input x>=1. This addendum proves that an explicit infinite subfamily **fails** the omitted main congruence. It therefore establishes nonredundancy of the raw main comparison and, separately, the positive21 main norm comparison. It does not produce a full child zero and does not establish global restored-index positivity.

Every compiler constant remains the actual exported constant. The full inherited proof, Report37 theorem, static source evidence, and checkers are included unchanged under `inherited-family/`. That packet's earlier statement that no individual congruence miss had been proved describes its earlier evidence stage; this addendum supplies the new exclusion argument. No enormous candidate is numerically materialized.

## 1. General arithmetic lemma: a fixed-modulus filter

Let q be an even square with 3 not dividing q. For any positive integer w define

    h0=4q^3+3, X=q^3*w, H=4q^6*w+h0.

Write J(a,m) for the Jacobi symbol, with positive odd denominator m. Then

    J(X,H)=J(w,h0).                                      (A)

In particular, for every positive odd p,

    2^p = X (mod H)  implies  J(w,h0)=-1.                (B)

This is a necessary condition only. Symbol -1 does not assert that the congruence is attainable.

### Proof, including composite and noncoprime cases

The integers H and h0 are both 3 modulo 8. Since H=3 modulo q, gcd(q,H)=1. Because q^3 is a square, J(q^3,H)=1, so J(X,H)=J(w,H). Also

    gcd(w,H)=gcd(w,h0).

If this gcd exceeds one, both sides of (A) are zero, proving that case. Otherwise write w=2^nu*z with z positive and odd. The supplementary law gives

    J(2,H)=J(2,h0)=-1.

The case z=1 is immediate. For z>1, both required denominator pairs are coprime. Quadratic reciprocity and H=h0 modulo z give

    J(z,H)=(-1)^((z-1)/2) J(H,z)
           =(-1)^((z-1)/2) J(h0,z)
           =J(z,h0).

The signs cancel because H and h0 are each 3 modulo 4. Multiplying by the equal factors J(2,H)^nu and J(2,h0)^nu proves (A). No denominator is assumed prime or squarefree. Finally,

    J(2^p,H)=J(2,H)^p=-1

for odd p. Jacobi symbols depend only on numerator residue classes, giving (B).

The facts used here are the multiplicativity, supplementary law, and reciprocity law for Jacobi symbols. NIST DLMF Section 27.9, equations 27.9.2--27.9.3 and its final paragraph, explicitly gives the extension to relatively prime odd composite denominators: https://dlmf.nist.gov/27.9 .

## 2. Genuine compiler slice and two valid thinnings

Fix a genuine compiler export and x>=1 as in the inherited theorem. Retain its B=2^d_cell, b, K0, MC, MFsrc, u=2*d_cell*x+b, W=2^u, and all source hypotheses. Choose

    q=B^(2x+2)=(B^(x+1))^2.

Thus q is an even square and 3 does not divide q. The inherited proof verifies q=1 modulo B-1 and q>=W+u-b+2 using b<=d_cell and B>=16. Fix its remaining constants

    Y=q^3, Z=1, C=W+1, s=t=1,
    Q=q^2-1, J=(q-1)/(B-1), M=(MC+q*MFsrc)J,
    L0=q(q-1)Q,
    P0=Q*((1+q*(K0+q^3))*C-q^2-W)-M,
    p0=P0 mod L0.

The genuine recipe makes MC even, hence M even. Therefore p0 is odd, L0 is even, and each selected p=p0+L0*k is odd. The source provenance and parity proof are inherited unchanged.

For either fixed choice

    T=h0  or  T=4h0,

restrict the parent progression parameter to r=T*j, j a positive integer. Then

    w_j=1+(q-1)T*j=1 (mod h0).

Consequently J(w_j,h0)=1. By (B), the main congruence fails for **every odd p** at these scales. The choice T=h0 is a stronger thinning result and includes even w; the root proposal T=4h0 is also valid and has w=1 modulo 4h0. For the latter, the original proof can alternatively swap (w/H), (H/w), (h0/w), (w/h0), with both reciprocity signs positive.

## 3. Quantitative existence after fixed thinning

This section verifies that the arithmetic exclusion meets infinitely many of the exact Pell-ratio candidates. It is not enough to exclude arbitrary auxiliary tuples.

Use the parent's exact center f and phase

    g(r)=(f(q^3*(1+(q-1)r))-p0)/L0.

Its controlled derivative estimate is

    g''(r)=-Kstar/[r*(log r)^2]*(1+O(1/log r)),
    Kstar=2Y*log(2Y)*q^3*(q-1)/(9L0)>0.

All fixed compiler and q parameters precede the limit. Define g_T(j)=g(T*j). By the exact chain rule,

    g_T''(j)=T^2*g''(T*j)
             =-Kstar*T/[j*(log j)^2]*(1+O(1/log j)).   (C)

In the final asymptotic equality T is fixed. Its potentially large size changes the implied constants and eventual threshold; no uniformity in T is asserted.

For integer N sufficiently large and every frequency 1<=h<=Hf, the parent's second-derivative estimate applied to (C) gives

    |sum_(N<=j<2N) exp(2*pi*i*h*g_T(j))|
      << sqrt(h*N)/log N + sqrt(N)*log N/sqrt(h).

The derivative-comparability constant is independent of h. Erdős--Turán with Hf=floor((log N)^4) gives interval counting error

    O(N/(log N)^4+sqrt(N)*log N)=o(N/log N),          (D)

uniformly in the chosen target interval. The exact primary references and controlled analytic expansion are included in the parent proof and analytic reference file.

Let delta0=(1/2)log(1+1/Y) and kappa0=delta0/(8L0). Apply (D) to

    [0, kappa0/log(2*T*N)).

Because T is fixed, the expected count kappa0*N/log(2*T*N) dominates the error. For all sufficiently large N, at least half that count remains. Enlarge the threshold so that N>=2T, whence log(2*T*N)<=2log N. Therefore at least

    delta0/(32L0) * N/log N                          (E)

integers j in [N,2N) satisfy

    0<=fractional_part(g(T*j))<kappa0/log(T*j).

With k=floor(g(T*j)), p=p0+L0*k, and n=(X_j*Y+1-p)/2, the inherited interior-margin argument now gives the **exact** Pell ratio

    Y<psi_A(p)/(2psi_P(n))<Y+1.

The parent controls the two Binet tails; no approximate ratio is substituted. Every other strict predicate bound, positive marker, positive quotient, input equation, and outer transport/packing identity holds once the single threshold is enlarged as in the parent. Thus these are genuine-compiler reduced candidates, not merely congruence fixtures.

In (E), N counts j. The corresponding r values lie in [T*N,2*T*N), and the actual w values lie in

    [1+(q-1)*T*N, 1+2*(q-1)*T*N).

The bound is not a positive natural density claim. Its constant and threshold depend on the fixed data; the proof supplies no practical numerical threshold or giant materialized witness. Distinct j give distinct w and thus distinct tuples. The lower bound tends to infinity, proving infinitude.

## 4. Literal nonzero residuals and comparison nonredundancy

For every selected candidate, inherit the parent's positive witnesses and put

    c=psi_A(p), Dpell=chi_A(p), a=Y(X+1),
    rho=(Dpell-a*c-X) mod H=(2^p-X) mod H,
    ga=floor((Dpell-a*c-X)/H)>0.

The Jacobi obstruction makes 1<=rho<H. The parent proves Dpell>H and positivity of every supplied coordinate.

In raw29, all comparisons except the main projection are exactly zero, and that projection residual is

    Dpell-(X+a*c+ga*H)=rho.

Its saved sum-of-squared-residuals polynomial is exactly rho^2>0.

In positive21, triangular elimination gives Dprime=Dpell-rho=X+a*c+ga*H>0. All comparisons except the main norm vanish; its exact residual is

    Dprime^2-(A^2-1)c^2-1=-rho*(2Dpell-rho).

The saved sum of squares is [rho*(2Dpell-rho)]^2>0. This is a different residual from the raw one, as required by the eliminated root.

Consequently, on each actual compiler/input slice, removing the raw main projection comparison admits infinitely many positive tuples violating it. Separately, removing the positive21 main norm comparison admits infinitely many positive tuples violating that norm. These are precise logical nonredundancy statements for the respective remaining conjunctions, with restored R=-p. No such tuple is asserted to be a zero of either full child.

## 5. Novelty and unresolved scope

The parent established simultaneous packing, transport, positive input loading, exact Pell ratio, auxiliary positivity, and all retained bounds with only one congruence omitted. The new arithmetic lemma adds a fixed-modulus necessary test and certifies an infinite subfamily of actual misses. It changes the residue evidence status without changing the frozen earlier packet.

The Jacobi test can be evaluated at the fixed odd modulus h0, without factoring h0 or building Pell integers. It is only an exclusion test: the symbol -1 sector is unresolved. No assertion is made that any candidate has zero residue. Full raw29/positive21 negative-zero existence and the global sign theorem remain open.

## 6. Reproducible evidence

`INDEPENDENT-AUDIT.md` records the audit checklist and limitations. `check_jacobi_addendum.py` uses exact integer arithmetic, a binary Jacobi implementation cross-checked against an independent trial-factorization/Euler-criterion oracle, and explicit exceptions. It checks composite and noncoprime denominators, both thinnings, the more general filter, odd-exponent obstruction, and formal fixed-thinning identities. Finite arithmetic fixtures corroborate the proof; they do not empirically prove the shrinking-target theorem or materialize a genuine compiler tuple.

The packet also contains the entire unchanged parent packet, including its exact checks and source snapshots. Those snapshots are inert evidence; no upstream code or saved schedule is executed. All fresh checkers support deterministic normal and Python -O replay, byte-exact expected receipts, and external output destinations.
