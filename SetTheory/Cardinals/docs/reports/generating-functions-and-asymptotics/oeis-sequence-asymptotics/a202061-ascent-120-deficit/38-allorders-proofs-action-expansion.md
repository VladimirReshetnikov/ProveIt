# All finite inverse-logarithmic orders of the classical action

Research result, 2 October 2026. This proves the deterministic action calculation. It does not prove a reduction of the A202061 coefficient deficit to this action. No release files have been changed.

## 1. Precise statement and the necessary fixed cutoff

Let alpha>0, v>0 and c be fixed. Introduce the formal Watson series

    S(k) = sum_{j>=0} (3/2)_j k^{-j}.

The formal large-T solution of

    k - log k + log S(k) = T/2 + c + log 2                         (1)

has the expansion

    k(T)=T/2+A+sum_{j>=1} p_j(A) T^{-j},   A=log T+c,

where p_j is a polynomial of degree at most j. In particular,

    p1=2A-3,
    p2=-2A^2+10A-33/2,
    p3=8A^3/3-24A^2+86A-120.

Let k_N retain the terms through p_N/T^N, and put

    V_N(h)=alpha k_N(log h)/h,  h>=b.

Here b is a sufficiently large fixed number, chosen after N. It ensures V_N>0, V_N'<0 and V_N''>0. Define A_{N,b}(n) as the minimum of

    integral_0^n [h'(t)^2/(2v)+V_N(h(t))] dt,

over absolutely continuous paths with h(0)=h(n)=b and h>=b.

The truncation cannot literally be used down to h=0: log log h is undefined there. A fixed lower cutoff, or an explicitly specified positive decreasing convex extension below it, is essential.

Set

    L=log n,  ell=log L,  F=n^{1/3} L^{2/3},
    Y0=(2 v alpha/(3 pi^2))^{1/3},  C=alpha/Y0,
    kappa=log Y0-2 log 3+2c,  B=kappa+7 ell/3.

**Theorem.** For every fixed J>=0 and N>=J+2,

    A_{N,b}(n)/(C F)
       = sum_{j=0}^J P_j(B)/L^j
         + O_J,N((1+log L)^{m_J,N}/L^{J+1}),                    (2)

for some finite exponent m_J,N. The polynomials P_j are independent of N, b, alpha, v and c. Their degree is j and

    [B^j]P_j = binomial(2/3,j) (3/2)^j.

The first terms are

    P0=1,
    P1=B,
    P2=-B^2/4+7B/2-10.

Thus the remainder in (2) is o(L^{-J}). In particular, the requested fourth-scale coefficient is rigorously the displayed P2 for this classical action. The error statement is for each fixed order; it makes no claim that the resulting infinite series converges. In the reduction convention o(M/L^K)=o(F/L^{K+1}), choose J=K+1 and N=K+3.

The recurrence in Section 7 specifies the whole sequence and is implemented by generate_action_polynomials.py. It also gives

    P3=(4B^3-105B^2+774B-2050-27pi^2)/24,

    P4=-(7B^4-273B^3+3444B^2-19768B-189pi^2 B
          +1944 zeta(3)+999pi^2+46290)/48.

These latter identities are generated symbolic outputs of the action recurrence. They have not received the separate direct-substitution replay performed for P2 below; keep them marked as additionally generated until that independent replay is done. They are not assertions of additional A202061 coefficient asymptotics.

## 2. The minimizing arch and its exact parameterization

Since k_N(T)=T/2+O(log T), k_N'(T)=1/2+O(1/T),

    V_N'(h)=alpha h^{-2}(k_N'-k_N),
    V_N''(h)=alpha h^{-3}(k_N''-3k_N'+2k_N).

The asserted positivity, decrease and strict convexity therefore hold for all h>=b, once b is sufficiently large. All required derivatives have fixed finite powers of log h times their natural powers of h^{-1}.

The direct method gives a minimizing path: a constant trial path bounds the kinetic energy, which bounds the maximum height; weak H^1 compactness and uniform convergence then give a minimizer. Strict convexity of the kinetic term together with convexity of V_N makes the minimizer unique. On (0,n) it is above b (raising a hypothetical interior minimum lowers the first variation of the potential) and satisfies

    h''=v V_N'(h)<0.

It is symmetric about n/2, with one maximum Y>b. Its conserved energy is

    h'^2/(2v)=V_N(h)-V_N(Y).

Conversely, integration of this identity gives a positive concave arch for each Y>b, and convexity of the functional makes that stationary arch its global minimizer. The duration is a continuous one-to-one function of Y, ranges from zero to infinity, and hence is increasing. The linearized boundary-value operator has quadratic form

    integral [eta'^2/v+V_N''(h) eta^2] dt>0

for nonzero endpoint-vanishing eta. This also gives smooth dependence on the duration and endpoint height, either by the boundary-value implicit-function theorem or the equivalent shooting equation.

Write T=log Y, z0=b/Y, k=k_N(T), and

    q_T(z)=k_N(T+log z)/k,
    I_-(T)=integral_{z0}^1 [q_T(z)/z-1]^{-1/2} dz,
    I_+(T)=integral_{z0}^1 [q_T(z)/z-1]^{ 1/2} dz.

Then exactly

    n(Y)=sqrt(2/(v alpha)) Y^{3/2} k^{-1/2} I_-(T),             (3)

    A(Y)=n(Y) alpha k/Y
           +2sqrt(2alpha/v) sqrt(Yk) I_+(T)
         =sqrt(2alpha/v) sqrt(Yk) [I_-(T)+2I_+(T)].             (4)

Both limiting integrals equal pi/2. Consequently Y~Y0 n^{2/3}L^{1/3} and A~CF.

## 3. The small-z endpoint is negligible to any fixed order

Fix an expansion order J. Choose an integer C0>2J+4 and let delta=T^{-C0}. Constants can depend on J,N,C0 and b, but not on T.

For all sufficiently large T, k_N is positive and increasing on [log b,T]. Thus on z0<=z<=delta,

    c0/T <= q_T(z) <= 1,

and, because T delta tends to zero,

    q_T(z)/z-1 >= q_T(z)/(2z).

It follows that

    integral_{z0}^{delta} [q_T(z)/z-1]^{1/2} dz = O(sqrt delta),
    integral_{z0}^{delta} [q_T(z)/z-1]^{-1/2} dz
                                                =O(sqrt T delta^{3/2}).  (5)

The first bound is the relevant larger error. Taking C0 as large as required makes both errors smaller than any specified finite inverse power of T. These estimates apply to the actual unexpanded integrands; they do not assume a uniform Watson expansion at heights of order b.

If an expanded integrand is integrated from zero instead of delta, its additional tail is bounded by a fixed finite sum of

    integral_0^delta z^{-1/2}(1+|log z|)^m dz
        =O(sqrt delta (1+|log delta|)^m).

Thus the formal beta integrals over (0,1) differ negligibly from the properly cut-off integrals. Increasing C0 absorbs all fixed logarithmic factors.

## 4. The z=1 cancellation and termwise finite-order integration

Factor

    q_T(z)/z-1=((1-z)/z)(1+r_T(z)),
    r_T(z)=[k_N(T+log z)-k_N(T)]/[k_N(T)(1-z)].                 (6)

At z=1 the second expression has the removable limit -k_N'(T)/k_N(T). There is no extra singularity from the apparent division by 1-z.

For delta<=z<=1, |log z|<=C0 log T. The mean-value theorem gives

    |r_T(z)| <= const |log z|/[T(1-z)]
               <= const (1+|log z|)/T = O(log T/T).             (7)

The last inequality uses -z log z<=1-z. Taylor expansion of the explicit smooth k_N about T, followed by expansion of 1/k_N(T), therefore gives r_T to every requested finite inverse-T order, uniformly on this interval. Each numerator polynomial in w=log z has zero constant term. The Taylor remainders retain a factor w, and hence division by 1-z is harmless. Their uniform bounds are T^{-J-1} times fixed powers of (1+log T).

The binomial expansion of (1+r_T)^{+/-1/2} has the same type of uniform finite-order remainder. The leading weights are

    w_-(z)=z^{1/2}(1-z)^{-1/2},
    w_+(z)=z^{-1/2}(1-z)^{1/2},

both integrable. Every coefficient is a linear combination of

    w_sigma(z) (log z)^m/(1-z)^r,   m>=r.                      (8)

These are integrable at z=1 since log z=-(1-z)+O((1-z)^2), and integrable at z=0 since the worst power there is z^{-1/2}. Equations (5)-(8) justify finite-order integration, with a uniform remainder. Only a first duration derivative is needed for inversion. It can be bounded directly, rather than invoking an arbitrary differentiable asymptotic remainder: on z<=delta, q_T>=c/T and |partial_T q_T|<=C/T, so differentiating the I_- integrand gives another O(sqrt T z^{1/2}) bound. Its tail is O(sqrt T delta^{3/2}), and the moving lower-limit contribution is O(sqrt T (b/Y)^{3/2}), exponentially small. The moving artificial cut contributes no larger error. On z>=delta, differentiating the removable r_T gives O(T^{-2} times fixed powers of log T) against the same integrable weight. Consequently I_-'(T)=O(T^{-2}(1+log T)^m) plus an arbitrarily small inverse-power tail. Hence d log n/dT=3/2+O(1/T), as required in Section 8.

The beta-moment rule is

    M_-(r,m)=d_a^m Beta(a,1/2-r)|_{a=3/2},
    M_+(r,m)=d_a^m Beta(a,3/2-r)|_{a=1/2}.                     (9)

For negative second beta argument, (9) means the derivative of the analytic continuation. This is not a prescription for a divergent integral: the differentiated integrand in (8) is convergent because m>=r. The identity follows by continuing the convergent differentiated integral in the beta argument, or by repeated integration by parts after using the order-m zero of (log z)^m at z=1.

For calculation without spurious polygamma poles, first use

    Beta(a,b0-r)=Beta(a,b0)
                product_{j=0}^{r-1}(a+b0-r+j)/(b0-r+j),

with b0=1/2 or 3/2, and only then differentiate. This is the rule implemented in both scripts.

## 5. Fixed core extensions and moving endpoint cutoffs

For a positive decreasing convex potential V, let A_a(n) be the same action with both endpoints a. Let E_a(n)=V(Y_a(n)). Differentiating the action with respect to its equal endpoint values gives the exact boundary-momentum formula

    d A_a(n)/da = -2 sqrt(2/v) sqrt(V(a)-E_a(n)).               (10)

Indeed, the two endpoint momenta are opposite and have magnitude sqrt(2/v)sqrt(V(a)-E_a). Smooth dependence was established above. Therefore, for b<=a,

    0 <= A_b(n)-A_a(n)
       <= 2sqrt(2/v) integral_b^a sqrt(V(h)) dh.                (11)

For the present V_N,

    integral_b^a sqrt(V_N(h)) dh = O(sqrt(a log a))             (12)

when a tends to infinity. If a=H epsilon with H=n^{2/3}L^{1/3}, a>=b and epsilon=o(1), then (12) is O(F sqrt epsilon), since log a<=O(L). This supplies the endpoint-softening estimate directly at fixed duration; no uncontrolled duration inversion is needed.

A positive decreasing C^2 convex extension to [0,b] exists, for example by a quadratic matching V,V',V'' at b. Applying (10)-(11) on [0,b] shows that replacing endpoint b by endpoint 0 under any such fixed extension changes the action by O(1). Different such core extensions also change it by O(1), by comparing both with A_b. The assertion is about fixed admissible positive core extensions, not arbitrary extensions with a negative well or an n-dependent core.

For completeness, at a common peak Y the omitted core duration is O(1): the core potential is bounded away from zero and E=V(Y) tends to zero. Its action contribution is also O(1). The fixed-duration estimate (11) is stronger and avoids any ambiguity from this time shift.

## 6. Uniform reciprocal-height bound

A useful perturbation bound is

    integral_0^n dt/h(t)=O(n/Y),                               (13)

uniformly for the minimizing arches with b<=a=o(Y), including a=H epsilon.

After division by n/Y, the integral is the ratio

    R(T)/I_-(T),
    R(T)=integral_{a/Y}^1 z^{-1}[q_T(z)/z-1]^{-1/2} dz.

On z>=delta=T^{-C0}, q_T(z)=1+O(log T/T) and the integrand is bounded by a constant times z^{-1/2}(1-z)^{-1/2}. Below delta it is at most const sqrt(T) z^{-1/2}, whose integral is O(sqrt(T delta)). Taking C0>1 proves R=O(1), while I_- stays bounded away from zero. Since Y/H stays in a fixed positive compact interval,

    integral_0^1 dt/(y(t)+epsilon)=O(1)

for the dimensionless softened arch h=H(y+epsilon).

This estimate is uniform also for potentials V_N-alpha eta/h with eta=o(1), on h>=b for large n: positivity, decrease and convexity persist, and the same k estimates apply with k replaced by k-eta. Comparing minima by evaluating one functional at the other's minimizer then gives an action change O(alpha eta n/H)=O(M eta), where M=F/L.

## 7. A simpler universal coefficient recurrence using peak k

The recurrence is most transparent in the parameter k rather than T. Any requested finite order can be represented by replacing S in (1) by a sufficiently long finite truncation S_m. The function

    T(k)=2k-2log k+2log S_m(k)-2c-2log 2                       (14)

has derivative 2+O(1/k)>0 and a smooth inverse for large k. Finite Taylor expansion and substitution give the p_j above, with differentiable remainders of the standard form k^{-j} times fixed powers of log k. The explicit k_N and this smooth inverse agree to every order that can enter (2), provided m and N are chosen large enough. More explicitly, taking m>=N+2 gives a residual O(T^{-N-1}(1+log T)^{N+1}) when k_N is substituted in (1). The derivative of the left side of (1) with respect to k is 1+O(1/k), bounded away from zero. Hence the smooth inverse k_m differs from k_N by O(T^{-N-1}(1+log T)^{N+1}); differentiation gives an O(T^{-N-2}(1+log T)^{N+1}) first-derivative difference. On the central interval, the difference between the corresponding removable r_T expressions is therefore O(T^{-N-3}(1+log T)^{N+2}), and their peak normalizations differ relatively by O(T^{-N-2}(1+log T)^{N+1}). Their low-z tails are already controlled by (5). Consequently the rigorously integrated coefficients from Sections 3-4 can be calculated from (14). No differentiability of an exact discrete row root is required.

Use a formal variable r=1/k, and write

    Delta(r,w)=k(T+w)-k(T),  w=log z.

From (14), Delta is the unique formal fixed-point solution

    Delta = w/2 + log(1+r Delta)
              -log S(r/(1+r Delta))+log S(r),                 (15)

where S(r)=sum_j (3/2)_j r^j. Iteration starting at Delta=w/2 determines every coefficient. Every coefficient is a polynomial in w, vanishing at w=0. At finite order, (15) is also a uniform analytic expansion for |w|<=C0 log k: its right-hand derivative in Delta is O(1/k), so the usual finite Taylor remainder estimate is uniform. This is an alternative direct proof of the expansion needed in Section 4.

Define the formal power series J_-(r), J_+(r), with constant term one, by expanding and integrating

    J_sigma(r)=(2/pi) integral_0^1 w_sigma(z)
                   [1+r Delta(r,log z)/(1-z)]^{sigma/2} dz,   (16)

where sigma=-1,+1 and the weights are those of Section 4. Equation (16) means coefficientwise finite beta moments (9), which have already been justified analytically. Its first coefficients, with g=log 2, are

    J_-(r)=1+(1-g)r+(3/2)(1-g)r^2+O(r^3),
    J_+(r)=1-g r-(3/2)g r^2+O(r^3).                          (17)

Now put x=1/L and q=3k/L. Taking the logarithm of (3), using (14) and the definitions of Y0 and kappa, gives the universal implicit series equation

    q=1+x[ (3/2)B+3log 2+(7/2)log q
             -3log S(3x/q)-log J_-(3x/q) ].                  (18)

Eliminating Y between (3) and (4) gives

    sum_{j>=0} P_j(B)x^j
       =q^{2/3} J_-(3x/q)^{-1/3}
                    [J_-(3x/q)+2J_+(3x/q)]/3.               (19)

Equations (15)-(19) are the promised coefficient-generation rule. For a coefficient through x^J, every series can be truncated immediately after degree J. No infinite integration or divergent-series summation is being asserted.

## 8. Rigorous inversion and polynomial degrees

The integrated duration relation has leading form

    log n=(3/2)T-(1/2)log T+constant+O(log T/T).

It therefore places the true T in

    T=(2/3)L+(1/3)log L+log Y0+O(log L/L).

Finite substitution determines its full inverse expansion. Rigorously, the derivative of the logarithmic duration relation is 3/2+O(1/T), bounded away from zero. Thus an approximate inverse with residual O(L^{-J-1}(1+log L)^m) has an error of that same order by the mean-value theorem. The same statement follows in the k parameter from derivative 3+O(1/k). This verifies, rather than merely formally assumes, the inversion step.

In (18), the right-hand dependence on q beyond its constant term is multiplied by x. Hence iteration from q=1 determines its coefficients successively, and a fixed J requires finitely many iterations. Its first coefficient has degree one in B; for j>=2, [x^j]q has degree at most j-1. Equation (19) then gives deg P_j<=j. The only contribution to B^j is the j-fold use of ((3/2)B)x in q^{2/3}, so

    [B^j]P_j=binomial(2/3,j)(3/2)^j,

which is nonzero for every j>=1. This proves the degree assertion. Stability of (18)-(19) under the uniform finite-order remainders from Sections 3-4 proves (2). The constants and the finite exponent in the error may depend on the requested order; no uniformity in J is needed or claimed.

## 9. Independent verification of P2

The four required convergent beta-log moments are

    J1=integral_0^1 z^{1/2}(1-z)^{-3/2}log z dz
       =-2pi(1-log 2),
    J2=integral_0^1 z^{1/2}(1-z)^{-5/2}log^2 z dz
       =(8pi/3)(1-log 2),
    K1=integral_0^1 z^{-1/2}(1-z)^{-1/2}log z dz
       =-2pi log 2,
    K2=integral_0^1 z^{-1/2}(1-z)^{-3/2}log^2 z dz
       =8pi log 2.

These were independently recomputed by differentiating the beta recurrence, not copied as assumptions into the verification script.

One short hand calculation from (17)-(19) also checks the result. Let g=log 2, a=(3/2)B+3g. Then

    q=1+a x+[(7/2)a-33/2+3g]x^2+O(x^3),

and if W(r)=J_-(r)^{-1/3}[J_-(r)+2J_+(r)]/3,

    W(r)=1-(2g/3)r+(1/9-g-g^2/9)r^2+O(r^3).

Substituting r=3x/q and multiplying q^{2/3}W(r), all log 2 terms cancel. The two coefficients are exactly

    P1=B,
    P2=-B^2/4+7B/2-10=-(B-10)(B-4)/4.

The script verify_action_coefficients.py performs a genuinely different algebraic check: it substitutes

    T=2L/3+(log L)/3+log Y0+u1/L+u2/L^2

straight into the original duration and action formulas, solves the two duration equations, and verifies the action coefficient against P2. Both checks pass.

## 10. Scope and errors found

1. The claimed fourth-scale action coefficient is correct.
2. The apparent z=1 singularity causes no obstruction after (6); the finite beta moments are convergent.
3. The small-height region must be cut off before expanding. The bounds (5) make this rigorous at every fixed order.
4. The expression k_N(log h) alone does not define an improper zero-endpoint action. Use a fixed b or an admissible fixed core extension. Their difference is O(1).
5. Endpoint softening to H epsilon costs O(F sqrt epsilon) at fixed duration, by (10)-(12).
6. The reciprocal-height integral needed for subtracting alpha eta/h is uniformly bounded in normalized coordinates.
7. The global coefficient/action reduction remains separate. This proof alone yields neither a multiplicative equivalent for A202061, a prefactor, nor control of smaller n-scales.
