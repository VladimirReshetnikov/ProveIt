# A113226 refined by strict downsets: complex-uniform asymptotics and local large deviations

Research addendum, 1 October 2026. Mathematical review and independent coefficient checks accompany this proof; conventional peer review remains appropriate. This does not alter the original A113226 release. All asymptotic expansions below are Poincare expansions to each fixed order, not convergent transseries or exponentially complete expansions.

## 1. Objects, exact marking, and computable coefficients

Let A_(n,k,j) count {3,2+2}-free naturally labelled posets on [n] with k distinct nonempty strict downsets and j isolated elements. By the established bijection of Bevan–Cheon–Kitaev (BCK), their sum is A113226(n). Here the statistics are defined on the poset side, or transported through that specific bijection; no identification with a usual permutation statistic is asserted.

BCK Proposition 7 encodes a poset by alternating nonempty blocks E_1,M_1,...,E_k,M_k, followed by an arbitrary E_(k+1). Its proof explicitly makes E_(k+1) the isolated elements, and M_i the maxima sharing the i-th distinct nonempty downset. The E_i are successive differences of these nested downsets. The requisite labels in M_i exceed all labels in E_1,...,E_i.

Set A_n(u,s)=sum_(k,j) A_(n,k,j) u^k s^j and

    H(z,u,s)=sum_(n>=0) A_n(u,s) z^n/n!,  H(z,u)=H(z,u,1).

Then, as formal series and near z=0,

    H(z,u,s)=exp((s-1)z) H(z,u),
    log H(z,u)=z+int_0^1 [uz(e^z-e^(zx)) /
                          (1-u(e^(zx)-1)(e^(z(1-x))-1))] dx.        (1)

Proof: apply the same maximum-coordinate transfer as in the original report, putting a factor u on each added E_i,M_i pair. Thus f(x)=1+u a(x)f(x)+u int_x^1 b(t)f(t)dt, where a=(e^(zx)-1)(e^(z(1-x))-1) and b=z(e^z-e^(zx)). With h=(1-u a)f, differentiation gives h'=-u b h/(1-u a), h(1)=1. The final block contributes e^(sz), proving (1). The cube-chamber normalization gives labelled counts divided by n!, exactly as in the original derivation.

There is an especially simple exact polynomial certificate. Let S(n,m) be a Stirling number of the second kind, and let L_n(u)=n![z^n]log H(z,u). Then L_1=1 and, for n>=2,

    L_n(u)=sum_(m=1)^floor(n/2) m!(m-1)! u^m
                 sum_(a=m)^(n-m) S(a,m) S(n-a,m).                  (2)

Indeed put T(x,y,u)=-log(1-u(e^x-1)(e^y-1)). Equation (1) is z+int_0^z T_x(t,z-t,u)dt. Expand T=sum_(m>=1)u^m(e^x-1)^m(e^y-1)^m/m and use the beta integral. Hence

    A_0(u,1)=1,
    A_(n+1)(u,1)=sum_(r=0)^n binom(n,r)L_(r+1)(u)A_(n-r)(u,1).    (3)

The first polynomials are 1, 1, 1+u, 1+5u, 1+17u+5u^2. Equations (2)–(3), together with (1), supply exact independent targets for computation.

### A direct record-to-cycle bijection for the exponential transform

There is also a purely labelled explanation of (2)–(3), independent of the transfer integral. Call a separated cycle a cyclic list of pairs (E_i,M_i) of nonempty disjoint sets, in which every E label is smaller than every M label. The labels used by the cycle form its component label set; cycles are considered up to cyclic rotation, never reflection. There is a unique representative starting with the E block containing the largest E label.

Given a valid BCK word, temporarily remove the final isolated block. Put e_i=max E_i, and cut the sequence of block pairs immediately before each strict left-to-right record of e_1,...,e_k. In a segment beginning at r, its first e_r is greater than every later E-block maximum in that segment. Every M label in the segment exceeds e_r by the original word condition. Therefore every E label in the segment is smaller than every M label, and the segment is the unique maximum-E-first representative of a separated cycle. Discard the order of the resulting cycles and retain the isolated labels as singleton components.

Conversely, start with a labelled set of separated cycles and singleton components. Rotate each cycle to its unique maximum-E-first representative, sort the cycles by increasing largest E label, and concatenate the representatives. Inside a cycle all M labels exceed all E labels. In a later cycle its largest E label exceeds every E label of an earlier cycle, so all cross-cycle word inequalities also hold. Append the singleton labels as the final decreasing zero block. Within each cycle there are no new E-maximum records after its first pair, and its first pair is a record relative to all preceding cycles. Thus the record cuts recover exactly the original cycles. These constructions are inverse, including the empty case, and preserve the total number of block pairs and isolated elements.

On a component label set of size n, if a labels belong to E blocks then they must be exactly its a smallest labels. Split them and the remaining n-a labels into m nonempty blocks in S(a,m)S(n-a,m) ways, match the two collections in m! ways, and put the pairs in cyclic order in (m-1)! ways. This proves (2) as a component-count formula. The labelled SET construction proves (3) and the exponential transform directly. At u=1 the nontrivial component counts, together with the singleton, are the already identified shifted A136127 sequence. This is a bijective explanation using explicit cycle objects; a direct map to any particular previously named excedance-permutation or tree model of A136127 is not claimed.

## 2. Parameters and the joint local singular expansion

For u>0 define

    a=u^(-1/2), rho=2log(1+a),
    c=[pi^2 a/(4rho)]^(1/3), K=rho/2-2-a,
    D=exp(K)sqrt(c/(3pi)).                                    (4)

All powers and logarithms extend holomorphically to a sufficiently small complex neighborhood of any compact interval of positive u. Unless an argument is displayed, functions on the right are evaluated at u.

Write w=rho-z. Symmetrizing (1) and evaluating its elementary integral gives locally near w=0

    log H(rho-w,u)=pi sqrt(a) w^(-1/2) S(w,u)+R(w,u),             (5)

where S,R are jointly analytic in (w,u), S(0,u)=1 and R(0,u)=K. The square root is positive when u>0,w>0. The following formulas fix every coefficient without ambiguous continuation of an arctangent:

    q=cosh(w/2)-a sinh(w/2), h=a cosh(w/2)-sinh(w/2),
    T=coth((rho-w)/4),
    S=(h/a) sqrt(a w/(1-q^2)),
    R=(rho-w)/2-[2h/(1+q)] sum_(m>=0)
           [(-1)^m T^(2m+1)/(2m+1)] [(1-q)/(1+q)]^m.             (6)

The quotient in S is analytic and equals one at w=0. The sum in R converges normally in a common sufficiently small neighborhood. For derivation, put q=cosh(z/2)-1/(2u e^(z/2)), N=1-u+u e^z. The integral first gives

    log H=z/2+N/[u e^(z/2)sqrt(1-q^2)]
                     atan[tanh(z/4)sqrt((1+q)/(1-q))].           (7)

Near the positive singularity replace atan(X) by pi/2-atan(1/X). Here N/(u e^(z/2))=2h. Expanding the second arctangent gives (5)–(6). Formula (7) is not used to infer singularities elsewhere: apparent q=-1 points can be removable.

For t=1-z/rho, write

    log H(rho(1-t),u)=K+2c^(3/2)t^(-1/2)+sum_(j>=1)g_j t^(j/2).
                                                                    (8)

If S=sum s_m w^m and R=sum r_m w^m, then

    g_(2m-1)=pi sqrt(a) s_m rho^(m-1/2), g_(2m)=r_m rho^m,
    s_1=(a^2-3)/(8a), s_2=(9a^4+10a^2-15)/(384a^2),
    r_1=(4-a^3)/(6a).                                         (9)

In particular at u=1 these reduce to the coefficients of the original report.

## 3. Uniform complex-parameter coefficient theorem

Theorem 1. For every compact interval U contained in (0,infinity), there is an open complex neighborhood Omega of U and holomorphic a_j(u), a_0=1, such that, for each fixed J>=0,

    A_n(u,1)/n! = D(u)rho(u)^(-n)n^(-5/6)exp(3c(u)n^(1/3))
           [sum_(j=0)^J a_j(u)n^(-j/3)+O_U,J(n^(-(J+1)/3))],    (10)

uniformly for u in a fixed closed neighborhood of U contained in Omega. The normalized remainder is holomorphic and its fixed parameter derivatives satisfy the same bound on a smaller neighborhood. The same result holds uniformly for s in every fixed compact subset of C, with leading amplitude D exp((s-1)rho) and computable coefficients a_j(u,s).

Proof of the uniform contour statements. For real u in U and r=rho(u),

    |u(e^(zx)-1)(e^(z(1-x))-1)|
       <=u(e^(|z|x)-1)(e^(|z|(1-x))-1)<=1,   |z|<=r.            (11)

On |z|=r equality requires x=1/2 and z=r. To see the latter strictly, the power series for e^(zx)-1 has positive coefficients in all positive powers for 0<x<1, so equality in its triangle inequality forces z positive real. At x=0 or 1 the product is zero. Therefore the denominator of (1) stays nonzero on the compact normalized set z=rho(u)zeta, |zeta|<=1, |zeta-1|>=epsilon. It remains nonzero on a fixed open neighborhood of that set and for u in a sufficiently small complex neighborhood of U. Near zeta=1, the jointly analytic representation (5) supplies continuation in a common slit neighborhood. These two representations agree on their initial intersection and give the needed common dented domain and coefficient contours. No global classification of the algebraic expression's apparent singularities is needed.

Here are quantitative saddle bounds, to address the complex parameter issue explicitly. Set delta=n^(-1/3). Use the Cauchy circle

    z=rho(u)(1-c(u)delta^2)e^(i theta), -pi<=theta<=pi.           (12)

Shrink Omega so Re(c)>c_*>0, Re(1/c)>b_*>0, and the local expansion and continuation above hold uniformly. This circle lies in the common dented domain for all large n: near theta=0, Re(1-(1-c delta^2)e^(i theta))>0; away from it, compactness applies. On its fixed outer arc log H is uniformly bounded, whereas the main modulus has exp(3Re(c)/delta) and the circle's radial factor is exp(Re(c)/delta+O(delta)).

On the local arc put theta=delta^2 y. Up to an O(delta) perturbation for bounded y, the nonconstant leading phase, after removal of the radial factor, is delta^(-1)Phi_c(y), with

    Phi_c(y)=2c^(3/2)(c-iy)^(-1/2)-iy,
    Phi_c(0)=2c, Phi_c'(0)=0, Phi_c''(0)=-3/(2c).              (13)

For small |y| the real-part loss is at least b y^2/delta, uniformly in Omega. This follows from the displayed second derivative and a uniform Taylor remainder. For the exact circle, the uncancelled linear term in the full exponent is O(delta^(-1)theta)=O(delta |y|). Completing the square therefore introduces only a negligible shift: on the Gaussian scale y=sqrt(delta)X this term is O(delta^(3/2)|X|). On the complement of the growing Gaussian cutoff it is absorbed by the quadratic loss. For epsilon<=|y|<=M, the loss is uniformly positive at real u because Re[(c-iy)^(-1/2)]<c^(-1/2). It remains so on a small complex neighborhood by compactness. For |theta|>=M delta^2 within the local arc, |t|>=b|theta|, whence |2c^(3/2)t^(-1/2)|<=C delta^(-1)/sqrt(M). Choose M large. This gives a fixed fractional loss from the main exponent. Together, these estimates make every arc outside |theta|<=delta^(5/2)log(1/delta) smaller than the main scale by every power of n, uniformly in u. The bounded O(t^(1/2)) perturbations do not change these estimates.

For the central integral deform to

    t=c delta^2(1+i sqrt(delta)X), X real.                      (14)

At fixed scaled endpoints |X|=epsilon/sqrt(delta), the connectors lie in a region of fixed leading-phase loss. For real u choose the short connectors from the original circle to the two vertical-segment endpoints inside the open fixed-loss neighborhoods. Continue this specific choice of connector curves continuously as u leaves the real interval, using a finite cover of U. Their compact images remain in the loss region after shrinking the common complex neighborhood; the curves do not cross t=0 or the local cut. Thus the same deformation is valid uniformly for complex u. On |X|<=log(1/delta), the phase is

    3c/delta-3c X^2/4+Q(delta,X;u).

The exact formal expression is

    Q=2c sum_(m>=3) binom(-1/2,m)(iX)^m delta^(m/2-1)
      +sum_(m>=2)(c^m/m)delta^(2m-3)(1+i sqrt(delta)X)^m
      +sum_(m>=1)(c^m/m)delta^(2m)(1+i sqrt(delta)X)^m
      +sum_(j>=1)g_j c^(j/2)delta^j(1+i sqrt(delta)X)^(j/2).     (15)

Consequently a_j is [delta^j] of the formal Gaussian average of exp Q, where the Gaussian has moments E X^(2m)=(2m-1)!![2/(3c)]^m and odd moments zero. This notation for complex c means analytic Gaussian integration; Re c>0 ensures convergence. The leading Jacobian/Gaussian product is exp(K)sqrt(c/(3pi))delta^(5/2).

The expansions in (8), (15) converge locally before their finite truncation. Uniform Taylor remainders on the cutoff are a prescribed power of delta times a polynomial in X, dominated after multiplication by exp(-bX^2). Expanding two additional half-orders and using parity leaves O(delta^(J+1)) with no logarithmic loss. This proves (10). The normalized remainders are holomorphic in u; Cauchy estimates give their fixed derivatives on smaller neighborhoods. The analytic multiplier exp((s-1)z) changes K to K+(s-1)rho and g_2 to g_2-(s-1)rho; all bounds are uniform for bounded s. This proves the full statement.

The first two coefficients, putting T_0=c^2/2+g_1 sqrt(c), are

    a_1=T_0-5/(36c)
       =c^2[1/2+rho(a^2-3)/(4a)]-5/(36c),
    a_2=T_0^2/2+c g_2-17g_1/(36sqrt(c))-17c/72-35/(2592c^2).   (16)

Equation (15) is a finite algorithm at every requested order. The included symbolic program also supplies a_3 without hiding a finite-order limitation.

## 4. A global phase-gap lemma in the marking variable

Lemma 2. For any compact positive U and epsilon>0 there are eta>0 and C<infinity such that, uniformly for u in U and epsilon<=|theta|<=pi,

    |[z^n]H(z,u e^(i theta),s)|<=C(rho(u)+eta)^(-n),             (17)

for s in any prescribed compact set.

Proof. For |z|<=rho(u), (11) is strict except when x=1/2,z=rho(u). At that exceptional point the product multiplied by u e^(i theta) equals e^(i theta), which is not 1. Thus the denominator never vanishes on this compact set. It remains nonzero for |z|<=rho(u)+eta with uniform eta>0. The integral in (1) is analytic and bounded there, uniformly in the listed parameters. Cauchy's bound proves (17). This excludes hidden periodic marking saddles; pointwise positive-u asymptotics alone would not do so.

## 5. Precise refined enumeration and large deviations

Use v=log u and define

    f(v)=-log rho(e^v), d(v)=log D(e^v),
    alpha(u)=f'(v)=1/[(1+sqrt(u))rho(u)], V(u)=f''(v)>0.         (18)

All primes below mean derivatives in v. Explicitly, with a=u^(-1/2), l=log(1+a),

    V=a(a-l)/[4(1+a)^2 l^2].                                  (19)

Because a>log(1+a), V>0. Moreover alpha maps (0,infinity) increasingly onto (0,1/2). Thus each alpha in (0,1/2) determines exactly one u.

Theorem 3. Let alpha=k/n lie in a fixed compact subinterval of (0,1/2), and choose u by alpha(u)=alpha. Then for every fixed J>=0,

    A_(n,k):=sum_j A_(n,k,j)
      = n! D(u)rho(u)^(-n)u^(-k) exp(3c(u)n^(1/3))
          n^(-4/3)/sqrt(2pi V(u))
          [sum_(j=0)^J b_j(u)n^(-j/3)+O(n^(-(J+1)/3))],         (20)

uniformly in these integer pairs (n,k). All b_j are explicitly computable and analytic on (0,infinity). In particular

    b_0=1,
    b_1=a_1-9(c')^2/(2V),
    b_2=a_2-9a_1(c')^2/(2V)+81(c')^4/(8V^2)
           -3c''/(2V)-3c'd'/V+3c'f'''/(2V^2).                 (21)

Thus replacing a_j with b_j matters already at order n^(-1/3); the stretched exponential shifts the marking saddle.

Proof. Fourier inversion on the u-circle gives the integral of A_n(u e^(i theta),1)u^(-k)e^(-ik theta). For small theta use Theorem 1. The real part of f(v+i theta)-f(v)-i alpha theta is <=-b theta^2 by V>0. The real parts of c(v+i theta)-c(v) and d(v+i theta)-d(v) are O(theta^2), because these functions and their derivatives are real on the real axis. Hence the normalized integrand has modulus <=C exp(-b n theta^2), after reducing b if necessary. Outside a fixed small theta-neighborhood apply (17); its exponential-in-n gain beats every stretched factor. Consequently only |theta|<=n^(-1/2)log n matters.

Set delta=n^(-1/3) and theta=delta^(3/2)X. Remove the Gaussian exp(-VX^2/2). Define the formal remainder

    P=sum_(m>=3) f^(m)(v)(iX)^m delta^(3m/2-3)/m!
       +3sum_(m>=1)c^(m)(v)(iX)^m delta^(3m/2-1)/m!
       +sum_(m>=1)d^(m)(v)(iX)^m delta^(3m/2)/m!.               (22)

Then

    b_j=[delta^j] E{ exp(P)
                sum_(r>=0) a_r(v+i delta^(3/2)X)delta^r },     (23)

where X is a centered normal with variance 1/V, and a_0=1. At each finite order every sum is finite. The half-integer powers with odd numerator have odd X parity, so only integer powers survive. Uniform analytic Taylor bounds and a Gaussian majorant give the remainder exactly as in Theorem 1. The additional Gaussian factor is n^(-1/2)/sqrt(2pi V), proving (20). Expanding (23) gives (21).

The first logarithmic correction -9(c')^2/(2V)n^(-1/3) can also be checked by shifting the full saddle: its log-u displacement is -3c'/[V n^(2/3)]+O(n^-1), and substitution yields the same correction.

Dividing (20) by (10) at u=1 gives a precise local large-deviation expansion. In particular, if K_n denotes the downset count for a uniform object,

    P(K_n=k) ~ [D(u)/(D(1)sqrt(2pi n V(u)))]
       exp{-n I(alpha)+3[c(u)-c(1)]n^(1/3)},
    I(alpha)=alpha log u+log rho(u)-log rho(1).                 (24)

The rate is nonnegative and vanishes only at alpha(1). Its derivative is log u and second derivative 1/V(u)>0. Full relative corrections follow by series division, not by discarding the stretched correction.

## 6. Gaussian, local, and isolated-element laws

Let rho_0=log4, c_0=c(1). Uniform analyticity of (10) gives

    E K_n = n/(2rho_0)
        + c_0(1-rho_0)/(2rho_0)n^(1/3)
        +1/6+1/(12rho_0)+O(n^(-1/3)),
    Var K_n = V(1)n+3[c(e^v)]''|_(v=0)n^(1/3)+d''(0)+O(n^(-1/3)),
    V(1)=1/(4rho_0^2)-1/(8rho_0)>0.                           (25)

For general u, 3c'=c(alpha-1/2) and 3c''=c[V+(alpha-1/2)^2/3]. The limiting Gaussian is

    (K_n-n/(2rho_0))/sqrt(n V(1))  ==> N(0,1).                 (26)

The global phase-gap lemma also proves the lattice local limit theorem, uniformly in all integers k:

    sup_k |sqrt(nV(1)) P(K_n=k)
           -phi((k-n/(2rho_0))/sqrt(nV(1)))| -> 0.             (27)

Indeed the characteristic functions converge after the n^(-1/2) rescaling; their integrals outside a growing central rescaled interval vanish by the Gaussian bound in the proof of Theorem 3 and (17). Fourier inversion bounds the supremum by this L1 error. Centering by the true mean gives the same statement.

If J_n counts isolated elements, (1) and Theorem 1 imply jointly

    ((K_n-n/(2rho_0))/sqrt(nV(1)), J_n)
         ==> (Z,P),  Z~N(0,1), P~Poisson(rho_0), independent.   (28)

This is a consequence of the uniform joint generating function, not of a real pointwise estimate. The mixed generating function factors in the limit into exp(-t^2/2) exp((s-1)rho_0). One may take real t and s on the unit circle to apply the usual characteristic-function criterion.

A stronger conditional statement follows from (20) with s retained:

    law(J_n | K_n=k) -> Poisson(rho(u)),                       (29)

uniformly for k/n in compact subsets of (0,1/2). In fact the total-variation error is O(n^(-2/3)). To see the rate explicitly, the multiplier in Theorem 1 gives

    a_1(u,s)=a_1(u), a_2(u,s)=a_2(u)-(s-1)rho c,
    d_s=d+(s-1)rho.

Thus uniformly on every fixed bounded s-set,

    E[s^J_n | K_n=k] = exp((s-1)rho)
       {1-(s-1)[rho c+3c'rho'/V]n^(-2/3)+O(n^-1)}.           (30)

The O(n^-1) error is holomorphic and uniform on |s|<=R for any fixed R>1. Cauchy coefficient bounds and sum_(j>=0)R^(-j)<infinity imply the stated total-variation bound. Unconditionally,

    E[s^J_n]=exp((s-1)rho_0)
            {1-(s-1)rho_0 c_0 n^(-2/3)+O(n^-1)},             (31)

so its Poisson approximation also has O(n^(-2/3)) total-variation error. Although the limits in (28) are independent, finite covariance is not zero: Cov(K_n,J_n)=[rho(e^v)]'|_(v=0)+O(n^(-2/3))=-1/2+O(n^(-2/3)), by differentiating the tilted version of (31).

## 7. Scope and novelty assessment

The source model is BCK's, and general Gaussian/quasi-powers mechanisms are standard. A Gaussian block count or an isolated-element Poisson law alone would be a modest corollary of the EGF. The substantive addendum includes the direct record-to-cycle explanation of the exponential transform and the fully parameterized EGF together with its complex-uniform saddle justification, the global marking phase gap, and the all-orders local large-deviation formula (20), including the second-saddle stretched correction and conditional law (30).

The conclusions are uniform only for compact positive u, equivalently compact interior block densities. They do not cover k=o(n), n/2-k=o(n), a transition to these boundary regimes, nor other complex z singularity sectors. No numerical experiments establish the theorem; they are checks of the exact formulas and correction algorithm. No independent peer-review or exhaustive novelty claim is implied.

## Primary sources and overlap screen

- BCK, On naturally labelled posets and permutations avoiding 12–34, European J. Combin. 126 (2025), 104117; Proposition 7 supplies the precise statistics and model. https://doi.org/10.1016/j.ejc.2024.104117 and https://arxiv.org/html/2311.08023v2
- OEIS A113226 and its references were rechecked: https://oeis.org/A113226
- Elizalde (2006), Asymptotic enumeration of permutations avoiding generalized patterns, Section 5 supplies earlier bounds: https://math.dartmouth.edu/~sergi/papers/pp05_aam_elizalde.pdf
- ProveIt default-branch connector searches on 1 October 2026 for A113226, 12-34, and Bevan Cheon Kitaev returned no hits. A naturally-labelled-poset query returned unrelated ordinal/order-theoretic enumerations. The head reported by the connector was 63b9d68407f21832316eb296fd0885e40e033c90 (22:32:47 UTC): https://github.com/VladimirReshetnikov/ProveIt/commit/63b9d68407f21832316eb296fd0885e40e033c90
- Focused public searches for A113226 asymptotics, 12–34 avoidance with bivariate/distribution/Poisson terms, and naturally labelled posets with downset distribution terms returned the BCK/Elizalde sources or unrelated material. No earlier matching refinement theorem was located. Code-search coverage and keyword searching are not an exhaustive literature audit.
