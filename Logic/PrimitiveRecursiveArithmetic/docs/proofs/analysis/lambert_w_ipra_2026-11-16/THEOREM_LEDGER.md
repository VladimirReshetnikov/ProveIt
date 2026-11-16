# Theorem ledger

The status codes are: **F** = finite exact iPRA theorem, **A** = constructive-analysis theorem with primitive-recursive moduli, **F/A** = finite theorem plus analytic lifting, **C** = conditional reduction, **P** = partial reconstruction/check, and **D** = deferred/not claimed.

| ID | Topic | Status | Statement | Location | Guard / constructive qualification | Notes |
|---|---|---:|---|---|---|---|
| LW-001 | Definition | A | A branch value W_k(z) satisfies W_k(z) exp(W_k(z)) = z. | Thm. 3.2; Sec. 5 | named branch and branch-separation data | rapid real/complex names |
| LW-002 | Real branches | A | No real solution exists for x < -1/e. | Thm. 3.2 | strict comparison with -1/e | rapid real names |
| LW-003 | Real branches | A | At x = -1/e the unique real solution is -1. | Thm. 3.2 | located equality at the named endpoint | rapid real names |
| LW-004 | Real branches | A | For -1/e < x < 0 there are exactly two real roots, W_0(x) in (-1,0) and W_{-1}(x) in (-infinity,-1). | Thm. 3.2 | positive separation from both endpoints | rapid real names |
| LW-005 | Real branches | A | For x >= 0 there is exactly one real root, W_0(x) >= 0. | Thm. 3.2 | none beyond input domain | rapid real names |
| LW-006 | Real branches | A | W_0 is strictly increasing and W_{-1} is strictly decreasing on their real domains. | Lemma 3.1; Thm. 3.2 | branch interval | rapid real names |
| LW-007 | Real branches | A | The inverse-search construction gives primitive-recursive continuity moduli away from the branch point. | Cor. 3.3 | compact branch interval with \|F'\| bounded below | rapid real names |
| LW-008 | Complex branches | A | A local complex branch can be constructed by path continuation while F' stays apart from zero. | Sec. 5 | finite polygonal path and positive separation certificate | rapid complex names |
| LW-009 | Complex branches | F/A | The preimage of the real axis satisfies v cos v + u sin v = 0 and u = -v cot v off v=0. | Prop. 5.1 | ordinary trigonometric side conditions | finite algebra plus complex rapid names |
| LW-010 | Complex branches | A | The unique critical point of w exp(w) is w=-1 and its critical value is -1/e. | Prop. 5.2 | none | rapid complex names |
| LW-011 | Transcendence | C | For nonzero algebraic z, every W-value is transcendental. | Sec. 5 | effective Lindemann-Weierstrass theorem imported; not developed here | conditional constructive number theory |
| LW-012 | Identities | A | W(z exp z)=z when the selected branch contains z. | Thm. 4.1 | branch selection | branch-safe rapid names |
| LW-013 | Identities | A | exp(W(z)) = z/W(z) for z and W(z) apart from zero. | Thm. 4.1 | z # 0 and W(z) # 0 | rapid names |
| LW-014 | Identities | A | log W(z) = log z - W(z) with compatible logarithm branches. | Thm. 4.2 | logarithm branch and nonzero arguments | rapid complex names |
| LW-015 | Identities | A | For n>0 and x>0, W_0(n x^n / W_0(x)^(n-1)) = n W_0(x). | Thm. 4.3 | integer n>0; x>0 | rapid complex names |
| LW-016 | Identities | A | W(x)+W(y)=W(xy(1/W(x)+1/W(y))) under branch and apartness guards. | Thm. 4.3 | W(x), W(y) # 0; output branch selected | rapid names |
| LW-017 | Identities | A | The multiplication identity for W(x)W(y) follows from the defining equations with explicit branch guards. | Thm. 4.3 | denominators and branches separated | rapid names |
| LW-018 | Identities | A | The two real roots at a common negative argument admit the ratio parametrization in Proposition 4.4. | Prop. 4.4 | parameter away from its removable singularities | rapid real names |
| LW-019 | Special values | A | W_0(0)=0, W_0(e)=1, and W_0(-1/e)=W_{-1}(-1/e)=-1. | Thm. 4.5 | none | rapid real names |
| LW-020 | Special values | A | Omega=W_0(1) is the unique real fixed point of exp(-x), and satisfies Omega exp(Omega)=1. | Def. 4.6; Cor. 4.7 | none | rapid real names |
| LW-021 | Special values | D | The printed W_0(-pi/2)=i pi/2 requires an upper-boundary convention on the principal cut. | Audit 4.8 | boundary value convention; the unqualified identity is not asserted | branch audit |
| LW-022 | Calculus | A | z(1+W)W'=W. | Thm. 6.1 | away from branch point | constructive differentiation |
| LW-023 | Calculus | A | W'=W/(z(1+W))=1/(z+exp(W)). | Thm. 6.1 | displayed denominators apart from zero | constructive differentiation |
| LW-024 | Calculus | A | W_0'(0)=1 by removal of the apparent singularity. | Thm. 6.1 | principal branch at zero | rapid real names |
| LW-025 | Calculus | F/A | All higher derivatives have the polynomial form (6.5) with recurrence (6.4). | Thm. 6.2 | branch point excluded | finite polynomial recurrence plus rapid names |
| LW-026 | Calculus | F/A | A root w of P_n maps to a root w exp(w) of W^(n), when the denominator is nonzero. | Thm. 6.2 | denominator apartness | finite polynomial algebra |
| LW-027 | Calculus | A | W''=-exp(-2W)(W+2)/(W+1)^3. | Cor. 6.3 | branch point excluded | constructive differentiation |
| LW-028 | Calculus | A | W_0 is strictly concave on (-1/e,infinity). | Cor. 6.3 | input in open branch domain | rapid real order |
| LW-029 | Calculus | A | W_{-1} is convex on (-1/e,-2/e^2), concave on (-2/e^2,0), with inflection at -2/e^2. | Cor. 6.3 | input separated from endpoints for strict signs | rapid real order |
| LW-030 | Integrals | A | Integral W(x) dx = xW-x+exp(W)+C. | Thm. 7.1 | fixed differentiable branch | constructive Riemann integration |
| LW-031 | Integrals | A | Integral W(x)/x dx = W^2/2+W+C. | Thm. 7.1 | x # 0 on the interval | constructive Riemann integration |
| LW-032 | Integrals | A | Integral W(A exp(Bx)) dx = (W^2/2+W)/B+C. | Thm. 7.1 | B # 0; fixed branch | constructive Riemann integration |
| LW-033 | Integrals | A | Integral W(x)/x^2 dx = Ei(-W)-exp(-W)+C. | Thm. 7.1 | separated interval defining Ei and x # 0 | constructive named special function |
| LW-034 | Integrals | A | Integral_0^e W_0(x) dx = e-1. | Cor. 7.2 | none | constructive Riemann integration |
| LW-035 | Integrals | A | For integer N>1, integral_0^infinity W_0(x^{-N}) dx = N^{1-1/N} Gamma(1-1/N). | Thm. 7.3 | fixed N>1 | constructive improper integration |
| LW-036 | Integrals | A | Integral_0^infinity W_0(x^{-2}) dx = sqrt(2 pi). | Thm. 7.3 | constructive Gamma(1/2)=sqrt(pi) | constructive improper integration |
| LW-037 | Integrals | A | Integral_0^infinity W_0(x)/(x sqrt x) dx = 2 sqrt(2 pi). | Cor. 7.4 | positive branch | constructive improper integration |
| LW-038 | Integrals | A | Integral_0^pi W_0(2 cot^2 t) sec^2 t dt = 4 sqrt(pi). | Cor. 7.4 | split at pi/2; endpoint tail moduli | constructive improper integration |
| LW-039 | Series | F | The truncated equation G=X Phi(G) has a unique solution after N+1 primitive iterations. | Lemma 8.1 | commutative coefficient ring with coded operations | finite truncated-series algebra |
| LW-040 | Series | F | Finite Lagrange-Buermann coefficient extraction holds in Q[X]/(X^{N+1}). | Thm. 8.2 | division by n available | finite truncated Laurent algebra |
| LW-041 | Series | F/A | [x^n]W_0(x)=(-n)^{n-1}/n!. | Thm. 8.3 | n>=1 | finite coefficients plus analytic lifting |
| LW-042 | Series | A | W_0(x)=sum_{n>=1}(-n)^{n-1}x^n/n! for \|x\|<1/e. | Thm. 8.3; Thm. 8.5 | strict radius witness | rapid analytic names |
| LW-043 | Series | F/A | W_0(x)^r has coefficient formula (8.5) for fixed integer r. | Thm. 8.4 | Laurent interpretation when r<0 | finite Laurent series plus analytic lifting |
| LW-044 | Series | F/A | (W_0(x)/x)^r has coefficient formula (8.6) for fixed constructive complex r. | Thm. 8.4 | \|x\|<1/e; n=0 coefficient interpreted separately | finite parameter-polynomial identity plus analytic lifting |
| LW-045 | Series | A | The exact centered radius of the Maclaurin series is 1/e. | Thm. 8.5 | none | constructive convergence/divergence certificate |
| LW-046 | Series | A | The Maclaurin series converges absolutely on \|x\|=1/e. | Thm. 8.5 | finite Wallis/Stirling bound | constructive series with tail modulus |
| LW-047 | Series | F/A | Both real branches have the displayed Puiseux expansions at -1/e. | Thm. 9.1 | nonnegative p=sqrt(2(1+ez)) on real side | ramified finite inversion plus analytic remainder |
| LW-048 | Series | A | Every fixed Puiseux order has an explicit primitive-recursive remainder bound. | Thm. 9.1 | computable neighborhood | rapid analytic names |
| LW-049 | Asymptotics | F/A | For every fixed N, W_0(x) has expansion (10.3) with explicit residual bound. | Thm. 10.1 | x above computable threshold | finite series reversion plus rapid names |
| LW-050 | Asymptotics | F/A | The first four logarithmic correction terms are those in (10.4). | Thm. 10.1 | x above computable threshold | finite rational polynomial identity |
| LW-051 | Asymptotics | F/A | W_{-1}(x) as x->0- has the finite-order expansion beginning (10.5). | Thm. 10.2 | x<0 sufficiently close to zero | finite series reversion plus rapid names |
| LW-052 | Bounds | A | The Hoorfar-Hassani lower and upper bounds (11.2) hold for x>=e. | Thm. 11.1 | x>=e | constructive real inequalities |
| LW-053 | Bounds | A | The Iacono-Boyd enhanced bounds (11.3) hold for x>=e. | Thm. 11.2 | x>=e | constructive real inequalities |
| LW-054 | Bounds | A | For y>1/e and x>=-1/e, W_0(x)<=log((x+y)/(1+log y)), with equality iff x=y log y. | Thm. 11.3 | positive logarithm argument | constructive real inequalities |
| LW-055 | Bounds | A | The specialization y=x+1 gives bound (11.6). | Thm. 11.3 | x>=-1/e | constructive real inequalities |
| LW-056 | Bounds | A | For -1/e<=x<=0, sqrt(1+ex)-1 <= W_0(x) <= cbrt(1+ex)-1. | Thm. 11.4 | real square/cube roots | constructive real inequalities |
| LW-057 | Bounds | A | Near the common branch point, W_{-1} obeys both strict bounds in (12.1). | Thm. 12.1 | u>0 with positive witness | constructive real inequalities |
| LW-058 | Bounds | A | As x tends to zero on W_{-1}, the two logarithmic bounds in (12.5) hold. | Thm. 12.2 | u>1 | constructive real inequalities |
| LW-059 | Representations | A | The nested exponential converges with a supplied invariant interval and contraction factor. | Thm. 13.1 | branch-safe invariant interval; q<1 | finite iteration with error modulus |
| LW-060 | Representations | A | The nested logarithm converges with a supplied positive invariant interval and \|W\|>1 witness. | Thm. 13.2 | lower bound d>1 | finite iteration with error modulus |
| LW-061 | Representations | D | The Poisson integral representation is not reconstructed. | Audit 13.3 | would require constructive Poisson/contour development | audit |
| LW-062 | Representations | D | The Kalugin-Jeffrey-Corless integral representation is not reconstructed. | Audit 13.3 | would require dedicated global integral proof | audit |
| LW-063 | Representations | D | The displayed continued fraction is not claimed beyond finite convergent checks. | Audit 13.3 | missing general recurrence and convergence majorant | audit |
| LW-064 | Equations | F/A | All branch solutions of x=a+b exp(cx) have formula (14.1). | Thm. 14.1 | b,c # 0 | finite algebra plus branch evaluation |
| LW-065 | Equations | F/A | All branch solutions of ax+b=exp(cx) have formula (14.2). | Thm. 14.1 | a,c # 0 | finite algebra plus branch evaluation |
| LW-066 | Equations | A | The two real solutions of 2x+2=3^x lie in the certified intervals printed in Example 14.2. | Example 14.2 | real logarithm of 3 | rapid interval evaluation |
| LW-067 | Equations | A | The inverse of x^x has all branch solutions exp(W_k(log y)) and the complete real solution count. | Thm. 14.3 | x,y>0; quotient form uses continuity at y=1 | rapid real names |
| LW-068 | Equations | F/A | All branch solutions of exp(-cx)=a_0(x-r) have formula (14.5). | Thm. 14.4 | a_0,c # 0 | finite algebra plus branch evaluation |
| LW-069 | Equations | F/A | The displayed thermodynamic equilibrium equation has algebraic solution formula (14.6). | Thm. 14.5 | positive T,K; c # 0; physical model premise not claimed | finite algebra plus branch evaluation |
| LW-070 | Equations | F/A | The Wien-type stationary equation has solutions x=D+W_k(-D exp(-D)). | Thm. 14.6 | integer D>0 | finite algebra plus branch evaluation |
| LW-071 | Equations | F/A | The Bernoulli-Todd equation yields the branch-difference formula (14.10). | Thm. 14.7 | Y in (-infinity,-1) or (-1,0); removable endpoint treated separately | finite algebra plus branch classification |
| LW-072 | Equations | A | The orthogonal-trajectory equation integrates to y^2=W_0(x^2 exp(-2C-x^2)). | Thm. 14.8 | sign-fixed interval and branch-safe square root | constructive integration plus differentiation check |
| LW-073 | Combinatorics | F | The number of rooted labeled trees on n vertices is n^{n-1}. | Sec. 15 | n>=1 | finite Prüfer bijection |
| LW-074 | Combinatorics | F | The truncated rooted-tree EGF satisfies T_N=X exp(T_N) mod X^{N+1}. | Thm. 15.1 | fixed truncation N | finite exponential generating functions |
| LW-075 | Combinatorics | F | W_0(X)=-T(-X) as a formal series. | Thm. 15.1 | coefficientwise interpretation | finite truncated-series uniqueness |
| LW-076 | Numerics | F/A | Newton iteration is formula (16.1). | Thm. 16.1 | denominator separated from zero | finite interval operations |
| LW-077 | Numerics | F/A | Halley iteration is formula (16.2). | Thm. 16.1 | all displayed denominators separated from zero | finite interval operations |
| LW-078 | Numerics | F/A | Logarithmic Newton iteration is formula (16.3) and has exactly the branch-safe roots as fixed points. | Thm. 16.2 | x/w>0, w#0, w+1#0 | finite interval operations |
| LW-079 | Numerics | A | A generic quadratic Newton error certificate follows from bounds m<=\|f'\| and \|f''\|<=M. | Thm. 16.3 | invariant interval and positive m | constructive Taylor remainder |
| LW-080 | Numerics | A | Interval Newton with bisection fallback preserves a real branch root and contracts quadratically away from -1/e. | Algorithm 16.4 | branch bracket and derivative separation | primitive-recursive interval algorithm |
| LW-081 | Numerics | P | Published universal starting-value constants are recorded and stress-tested, but not fully replayed. | Sec. 16.1 | source-specific global inequalities remain | partial external-certificate audit |
| LW-082 | Numerics | D | Quoted minimax rational bit accuracies are not claimed without external coefficient tables and uniform error proof. | Sec. 16.1 | external approximation certificate required | audit |
