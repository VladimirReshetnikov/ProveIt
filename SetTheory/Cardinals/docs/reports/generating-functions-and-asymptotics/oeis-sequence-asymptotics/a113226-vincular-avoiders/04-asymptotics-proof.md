# An exact EGF and complete asymptotics for A113226

Research proof, 1 October 2026. Pending independent review. Let A_n be OEIS A113226, counting permutations avoiding the vincular pattern 12–34 (the two adjacent pairs are separated by an arbitrary gap). Let H(z)=sum A_n z^n/n! and L=log H, with L(0)=0.

## 1. Main result and scope

Put rho=log 4 and c=(pi^2/(4rho))^(1/3). Then

    H(z)=exp{ z/2 + q(3 arcsin q-pi/2)/sqrt(1-q^2) },  q=e^(z/2)/2,

with branches initially analytic at z=0. Equivalently, L is the unique analytic solution of

    (4-e^z)L'(z)-2L(z)=2+e^z-z,  L(0)=0.                 (1)

For each fixed integer J>=0,

    A_n = D n! rho^(-n) exp(3c n^(1/3)) n^(-5/6)
          [ sum_{j=0}^J a_j n^(-j/3) + O_J(n^(-(J+1)/3)) ],    (2)

where D=2e^(-3)sqrt(c/(3pi)), a_0=1, and every a_j is explicitly and finitely computable. In particular,

    a_1 = c^2(1-rho)/2 - 5/(36c),
    a_2 = [324c^6(rho-1)^2 + c^3(1908rho-612)-35]/(2592c^2).

Numerically c=1.21188506246461864249, D=0.03570604125804483339,
mu=exp(3c)=37.92669385021515730, a_1=-0.39827424329477706556,
a_2=0.98158861254222799575, a_3=-0.53022033843535145958,
a_4=-0.66858737252587671304.

This proves the exponential-growth and stretched-exponential forms of Conjectures 13 and 14 of Bevan–Cheon–Kitaev, with exact beta=-5/6 and exact D,mu. Their quoted decimal fits are estimates, not exact values. The expansion is a full Poincare expansion to each fixed algebraic order. Neither convergence of the coefficient series nor an exponentially complete transseries is asserted.

## 2. Attribution and the exact combinatorial identity

Bevan–Cheon–Kitaev, Proposition 7, identifies these permutations (via their poset bijections) with labelled binary words beginning in zero, with decreasing labels inside zero runs, increasing labels inside one runs, and every one label larger than every earlier zero label. Equivalently an object is

    E_1,M_1,...,E_k,M_k,E_{k+1},

where E_i and M_i for i<=k are nonempty sets, E_{k+1} is an arbitrary set, and every label of M_i exceeds all labels in E_1 union ... union E_i. Runs have their uniquely prescribed orders. The case k=0 includes the empty object and a single decreasing zero run.

To translate this existing model, replace distinct integer labels by continuous coordinates in [0,1]. For fixed block cardinalities summing to n, integrate over the coordinate cube and divide by the factorial of each block size. Each ordering chamber has volume 1/n!, and unordered coordinates within the blocks contribute exactly their block factorials. Thus the resulting coefficient is precisely the number of valid labelled objects divided by n!, not a probability with an extra multinomial factor. Coincident coordinates have measure zero.

Let x denote the largest coordinate in the previous zero blocks; initially x=0. A new nonempty zero block either has maximum at most x, with EGF weight e^(zx)-1, or creates a new maximum t>x, with weight density z e^(zt) dt. For the latter statement, among m coordinates the maximum density is m t^(m-1), so summing z^m m t^(m-1)/m! gives z e^(zt). A following nonempty one block contributes e^(z(1-t))-1. The unrestricted final zero block contributes e^z regardless of the state. There is no restriction relating its labels to earlier one labels.

Let f(x) count any number of additional zero/one block pairs. Then, as a formal series (and analytically for sufficiently small |z|),

    f(x)=1+(e^(zx)-1)(e^(z(1-x))-1)f(x)
           + integral_x^1 z(e^z-e^(zt))f(t) dt.               (3)

The operator increases size by at least two, so the formal solution is unique. Define

    D_z(x)=e^(zx)+e^(z(1-x))-e^z,
    h(x)=D_z(x)f(x), b(x)=z(e^z-e^(zx)).

Equation (3) becomes h(x)=1+integral_x^1 b(t)h(t)/D_z(t)dt. Hence
h'(x)=-b(x)h(x)/D_z(x), h(1)=1, and D_z(0)=1. Consequently

    L(z)=z+integral_0^1 z(e^z-e^(zx))/D_z(x) dx
        =z/2+(ze^z/2) integral_0^1 dx/D_z(x).               (4)

For the second equality, average x and 1-x and use e^(zx)+e^(z(1-x))=D_z(x)+e^z.

Setting v=z(x-1/2), q=e^(z/2)/2, and then u=tanh(v/2) evaluates (4) as

    L(z)=z/2 + (2q/sqrt(1-q^2))
          atan[ ((2q-1)/(2q+1))sqrt((1+q)/(1-q)) ].

The arctangent is zero at q=1/2. Its derivative in q equals 3/(2sqrt(1-q^2)); therefore it equals (3/2)arcsin(q)-pi/4 near q=1/2. This proves the displayed EGF. Differentiation gives (1); alternatively the derivative of the arctangent expression verifies it directly.

## 3. Exact recurrence and a known cumulant sequence

Let ell_n=L^(n)(0), ell_0=0. Equation (1) gives the exact recurrence

    3 ell_(n+1)=sum_{k=0}^{n-1} binom(n,k) ell_(k+1)
                 +2ell_n+1+2[n=0]-[n=1],  n>=0,            (5)

and H'=L'H gives

    A_0=1,  A_(n+1)=sum_{k=0}^n binom(n,k)ell_(k+1) A_(n-k). (6)

These use O(N^2) integer arithmetic operations to obtain all terms through N; this is an arithmetic-operation statement, not an O(N^2) bit-complexity claim.

The cumulants are not a new integer sequence: ell_n=A136127(n-1) for n>=1. One exact verification uses the already known poly-Bernoulli-relative array T_(a,b), whose doubly exponential generating function is

    T(x,y)=log[1/(e^x+e^y-e^(x+y))],  a,b>=1.

The known antidiagonal identity, recorded in Testart (2026), is
A136127(n)=sum_{k=0}^{n-1}T_(k+1,n-k), for n>=1, with A136127(0)=1.
Equation (4) reads

    L(z)=z+integral_0^z T_x(t,z-t)dt.

The beta integral of t^(a-1)(z-t)^b/[(a-1)!b!] is z^(a+b)/(a+b)!, proving the claim. Thus H'/H is the EGF of A136127. Its objects and leading asymptotic are prior work; the scoped contribution here is the exact transform for A113226 and its consequences.

## 4. Analytic continuation and a convergent singular expansion

For |z|<rho,

    |(e^(zx)-1)(e^(z(1-x))-1)|
       <=(e^(|z|x)-1)(e^(|z|(1-x))-1)
       <=(e^(|z|/2)-1)^2 < 1.

The second inequality follows by minimizing e^(rx)+e^(r(1-x)) at x=1/2. Hence the integral is analytic there. On |z|=rho, equality is possible only at z=rho and x=1/2. More strongly, (1) continues L along every path avoiding rho+2pi i k, k in Z. In a disk of radius R with rho<R<|rho+2pi i|, cut along [rho,R), the continuation is single-valued, and there are no other singularities. This follows from existence and uniqueness for a first-order linear analytic ODE on a simply connected domain.

Let w=rho-z and choose sqrt w positive for w>0. The explicit formula has the local convergent form

    L(z)=pi/sqrt(e^w-1)+R(w),                                (7)

where R is analytic at w=0. Indeed,
R(w)=(rho-w)/2-3 arccos(e^(-w/2))/sqrt(e^w-1); the two square roots in the second term cancel. Its Taylor expansion begins

    R(w)=rho/2-3+w/2-w^2/10-w^3/210+O(w^4).

For complete computational specification, write R(w)=sum r_m w^m. Then r_0=rho/2-3 and, for m>=1,

    r_m={-[m=1]-4(-1)^m/m!
          -4 sum_{k=1}^{m-1}(-1)^(m-k) k r_k/(m-k+1)!}/(4m+2).  (8)

This follows by substituting R into
4(1-e^(-w))R'(w)+2R(w)=rho-w-2-4e^(-w).
Also let s_m=[w^m]sqrt(w/(e^w-1)); s_0=1,s_1=-1/4,s_2=1/96,s_3=1/384.

With t=1-z/rho, K=rho/2-3, A=pi/sqrt(rho)=2c^(3/2), we have

    L(rho(1-t))=K+A t^(-1/2)+sum_{j>=1}g_j t^(j/2),      (9)

convergently for sufficiently small |sqrt t|, where

    g_(2m-1)=pi s_m rho^(m-1/2),  g_(2m)=r_m rho^m.

In particular g_1=-pi sqrt(rho)/4 and g_2=rho/2. There is no log t term; this is important for the power n^(-5/6).

## 5. Dominant arc and rigorous all-orders expansion

Set delta=n^(-1/3), t_0=c delta^2, and take the Cauchy circle z=rho(1-t_0)e^(i theta). Uniformly on a fixed small neighborhood of theta=0, (9) gives

    log|H(z)|=K+A Re(t^(-1/2))+O(|t|^(1/2)),
    t=1-(1-t_0)e^(i theta).

For |theta|<=epsilon t_0, Taylor expansion of (1+v)^(-1/2), with Re t>=t_0 and Im t comparable to -theta, gives

    Re(t^(-1/2)) <= t_0^(-1/2)-b theta^2 t_0^(-5/2),    (10)

for a fixed b>0 after choosing epsilon small. For epsilon t_0<=|theta|<=theta_0, the elementary modulus bound |t|^2=t_0^2+2(1-t_0)(1-cos theta) implies
Re(t^(-1/2))<=|t|^(-1/2)<=t_0^(-1/2)(1+b epsilon^2)^(-1/4).
Away from theta=0, L is uniformly bounded on the remaining arc as n increases, by continuation across the compact subset of |z|=rho not containing rho.

These estimates show that all arcs outside

    |theta| <= delta^(5/2) log(1/delta)

are smaller than the main scale by every negative power of n. In the intermediate range between the cutoff and epsilon t_0, use (10); beyond epsilon t_0 use the fixed fractional loss in the singular exponent. The O(|t|^(1/2)) term is bounded and does not affect these losses.

For transparent coefficient extraction deform only the small central arc to the vertical segment

    t=c delta^2(1+i sqrt(delta)u).

One may take endpoints with |Im t|=epsilon t_0. They differ from the original circular arc by O(t_0^2) in real part. The connecting segments stay in Re t>=t_0 and |Im t| comparable to epsilon t_0, where the preceding fixed fractional loss holds. The change in -n log|1-t| is O(n t_0^2)=O(delta), so these connectors remain exponentially negligible. No singularity is crossed. Reversing orientation gives a positive Gaussian integral.

The main phase is

    A t^(-1/2)+nt=3c/delta-3c u^2/4+Q_0(delta,u),

where Q_0 begins at delta^(1/2)u^3. The Cauchy Jacobian is exactly c delta^(5/2)/(2pi); the extra factor (1-t)^(-1) is included below. If U is a centered normal random variable of variance 2/(3c), then the coefficient after its leading normalization is the formal Gaussian expectation of exp Q, where

    Q(delta,U) = 2c sum_{k>=3} binom(-1/2,k)(iU)^k delta^(k/2-1)
       + sum_{m>=2} (c^m/m) delta^(2m-3)(1+i sqrt(delta)U)^m
       + sum_{m>=1} (c^m/m) delta^(2m)(1+i sqrt(delta)U)^m
       + sum_{j>=1} g_j c^(j/2) delta^j(1+i sqrt(delta)U)^(j/2).   (11)

The first line is the remainder of the principal essential-singularity phase; the second is n[-log(1-t)-t]; the third is -log(1-t); the fourth is the regular Puiseux perturbation. Therefore

    a_j=[delta^j] E exp Q(delta,U).                          (12)

Every requested coefficient involves only finitely many summands. Odd powers of sqrt(delta) are odd in U and integrate to zero. Gaussian moments evaluate all remaining monomials, so a_j belongs to Q[c,c^(-1),rho].

For rigor, restrict the vertical segment to |u|<=log(1/delta). The complement is superpolynomially small by the same quadratic estimate. On this segment Q_0=O(sqrt(delta)(1+|u|^3)); all other terms and their finite Taylor remainders have bounds by a fixed power of delta times a polynomial in u. The convergent expansion (9) and the analytic binomial/logarithm expansions provide these bounds uniformly. The perturbed integrand is bounded by C exp(-b u^2) for small delta, because sqrt(delta)|u|^3=o(1+u^2) on the cutoff. Expand to two more half-orders than needed, bound the exponential remainder by an integrable polynomial times exp(-b u^2), and integrate. The odd half-order vanishes on the symmetric segment and its Gaussian extension. The resulting remainder is O_J(delta^(J+1)), with no unaccounted logarithmic factor. This proves (2) and (12).

Finally the leading Gaussian factor is

    e^K c delta^(5/2)/(2pi) * sqrt(4pi/(3c))
       =2e^(-3)sqrt(c/(3pi)) n^(-5/6),

as asserted. The term nt^2/2 is order delta and changes a_1, not the leading constant.

## 6. Explicit coefficients and executable generator

The coefficient of delta in (12) is

    c^2(1-rho)/2 + (35c/64)E U^4 -(25c^2/128)E U^6
       =c^2(1-rho)/2-5/(36c).

The program asymptotic_coefficients.py constructs (11) to any requested fixed order J. It obtains the s_m by series expansion and r_m from (8), writes Q=sum Q_k h^k with h=sqrt(delta), and computes exp Q=sum E_k h^k by

    E_0=1,  E_k=(1/k)sum_{j=1}^k j Q_j E_(k-j).

It then replaces U^(2m) by (2m-1)!![2/(3c)]^m and odd powers by zero. This is an implemented general finite-order algorithm, not a claim that a fixed table establishes all orders. Default execution computes through J=4. Larger orders may have substantial symbolic time and memory cost.

The expressions for a_3 and a_4 and 70-digit numerical evaluations are recorded in asymptotic_coefficients.json. They are ordinary high-precision computations, not certified interval enclosures.

## 7. Controlled inverse expansion and integer thresholds

Use log Gamma(x+1) to express the factorial contribution. A smooth increasing realization F(x) of the exact sequence can be constructed for sufficiently large x with F(n)=A_n and with a differentiable all-orders asymptotic expansion. For completeness, first realize the formal log expansion by a locally finite sum with successively later smooth cutoffs, choosing cutoffs so the tail and its fixed derivatives satisfy all prescribed bounds. This gives a smooth G. The discrepancies log A_n-G(n) are smaller than every power of n. Add these discrepancies times one fixed smooth bump centered at each integer, with disjoint supports of radius <1/3 and value one at the center. The corrections and all their fixed derivatives are flat. Exponentiating gives F, and (log F)'~log(x/rho)>0. No canonical analytic interpolation is asserted.

Write

    log F(x)=x log(x/(e rho))+C x^(1/3)+alpha log x+d
                    +sum_{j>=1} beta_j x^(-j/3),            (13)

where C=3c, alpha=-1/3, d=log(D sqrt(2pi)),
beta_1=a_1, beta_2=a_2-a_1^2/2,
beta_3=a_3-a_1 a_2+a_1^3/3+1/12, with the later Stirling terms included at their respective orders.

For Y tending to infinity let

    L_Y=log Y, N=L_Y/W(L_Y/(e rho)), ell=log(N/rho).

Thus N log(N/(e rho))=L_Y and ell=W(L_Y/(e rho))+1. Put

    a=-C/ell,
    b=1/3+(log(rho)/3-d)/ell,
    d_1=-(a^2/2+C a/3+beta_1)/ell,
    e_1=-[(a+C/3)b+alpha a+beta_2]/ell.                   (14)

Then

    F^(-1)(Y)=N+N^(1/3)a+b+N^(-1/3)d_1+N^(-2/3)e_1
                      +O(1/(N ell)).                      (15)

In particular omitting the two decaying corrections leaves error O(N^(-1/3)/ell). To verify (15), substitute x=N+N^(1/3)a+b+N^(-1/3)d_1+N^(-2/3)e_1 into (13). Orders N^(1/3),1,N^(-1/3),N^(-2/3) vanish in turn. The remaining logarithmic residual is O(N^(-1)); since the derivative is asymptotic to ell, the mean value theorem yields the stated inverse error. The coefficients a,b,d_1,e_1 remain bounded as ell grows.

Repeating coefficient cancellation generates a full inverse Poincare expansion in powers of N^(-1/3), beginning at N^(1/3), with coefficients rational in ell. The logarithmic term causes no separate growing log N coefficients because log N=ell+log rho. Each residual bound is converted to an inverse bound by division by a derivative comparable to ell. Flat changes of the smooth realization leave all these orders unchanged.

For an eventual integer threshold tau(Y)=min{n:A_n>=Y}, the monotone interpolation gives tau(Y)=ceil F^(-1)(Y) for all sufficiently large Y. Any explicitly established approximation |F^(-1)(Y)-X(Y)|<=E(Y) gives the safe envelope

    ceil(X-E)<=tau(Y)<=ceil(X+E).

An o(1) inverse error does not justify unconditional rounding of X when X is close to an integer.

## 8. Exact and numerical checks

exact_recurrence.py generated A_n and ell_n through n=1000 with integer arithmetic. All 21 displayed OEIS terms agree. A separate implementation of the five insertion rules of Bevan–Cheon–Kitaev Proposition 11 agrees through n=65; it does not use the EGF or cumulants. Exhaustive permutation enumeration with the literal vincular-pattern predicate agrees through n=8. These are checks, not substitutes for the combinatorial proof.

validate_asymptotics.py compares exact terms with the complete expansion. At n=1000 the normalized ratio A_n/[D n!rho^(-n)e^(3c n^(1/3))n^(-5/6)] is 0.969404954960...; its slow approach to one explains why a free finite-range fit can underestimate the leading amplitude. The scaled residual after a_0,...,a_4 is about 1.3572 at n=1000 and remains consistent with a fifth-order term. This does not numerically certify the asymptotic error constants.

At Y=A_1000, inverse approximation errors after the constant term, after d_1, and after e_1 are approximately -0.0115393,+0.00233040,-0.0000291627. The complete sample table is in validation.json.

## 9. Scope of prior-work screening and remaining questions

The current OEIS entry, BCK v2/published paper, Elizalde's 2006 primary paper, A136127 and its listed primary literature, and Testart 2026 were inspected. BCK provide the combinatorial model and numerical conjectures; Elizalde provides earlier bounds, not the exact EGF. A136127 and its leading asymptotic are known. The focused source search found no earlier A113226 closed EGF or logarithmic-derivative transform. This is not an exhaustive priority claim.

Current ProveIt default-branch searches for A113226, 12-34 and Bevan Cheon Kitaev returned no matches. The branch head was 63b9d68407f21832316eb296fd0885e40e033c90. Local workspace hits were the present project and an earlier screening note identifying this as a separate unsolved target.

Further questions: a direct labelled bijection explaining the A136127 exponential transform; multivariate refinements counting zero/one blocks or poset statistics; certified numerical bounds for the saddle error; and exponentially improved expansions resolving the other singularities rho+2pi i k. None of these is needed for (1)–(15), and no exponentially complete transseries is claimed here.

## Primary sources

- OEIS A113226: https://oeis.org/A113226
- D. Bevan, G.-S. Cheon, S. Kitaev, On naturally labelled posets and permutations avoiding 12–34, European Journal of Combinatorics 126 (2025), 104117. https://doi.org/10.1016/j.ejc.2024.104117 ; https://arxiv.org/html/2311.08023v2
- S. Elizalde, Asymptotic enumeration of permutations avoiding generalized patterns, Advances in Applied Mathematics 36 (2006), 138–155. https://math.dartmouth.edu/~sergi/papers/pp05_aam_elizalde.pdf
- OEIS A136127: https://oeis.org/A136127
- J.-C. Aval, A. Boussicault, M. Bouvel, M. Silimbani, Combinatorics of non-ambiguous trees. https://arxiv.org/html/1305.3716
- B. Testart, On minimal pattern-containing inversion sequences, arXiv:2602.12130v1, Section 6. https://arxiv.org/html/2602.12130v1
