# A126348 coefficient asymptotics and inversion

Status: analytic proof and final article transcription independently reviewed on 2026-10-01. The computations check the formulas but are not numerical onset certificates. The coefficient theorem is a relative asymptotic theorem. It does not specify an exact continuous interpolation of the integer sequence or a canonical beyond-all-orders sector decomposition.

## Main quantities

Let

F(q)=product_{k>=1}(1+q^k/(1-q))=sum_{n>=0}a_n q^n,
c=pi^2/6,
L=log(1/t),
A(L)=L^2/2+L+c,
B(L)=L^2+L+2c,
V(L)=L^2+3L+2c+1.

For every sufficiently large realn choose the unique positiveL satisfying

n=e^(2L) A(L), t=e^(-L).

Define V_0=L^2/2+c and recursively V_j=(j+d/dL)V_{j-1}. ThusV_1=A,V_2=V,
V_3=3L^2+11L+6c+6,
V_4=12L^2+50L+24c+35.

The all-orders coefficient formula is

a_n=exp(e^L B(L)-1)/sqrt(2*pi*e^(3L)*V(L))
    *[sum_{j=0}^J e^(-jL) C_j(L)+O_J(e^(-(J+1)L)(1+L)^(J+1))],

whereC_0=1 andC_j are rational functions ofL with coefficients inQ[pi^2]. The remainder is meant for each fixedJ asn->infinity. The first correction is

C_1=P_1+E_1,
P_1=(5-L)/24,
E_1=V_4/(8V^2)-5V_3^2/(24V^3).

In particular, the displayed leading expression is a genuine coefficient equivalent, rather than only an equivalent for loga_n.

The second correction is

C_2=P_2+P_1^2/2+P_1E_1+E_2-1/(48V)-(6-L)V_3/(48V^2),
P_2=-1/9,
E_2=-V_6/(48V^3)+7V_3V_5/(48V^4)+35V_4^2/(384V^4)
    -35V_3^2V_4/(64V^5)+385V_3^4/(1152V^6).

## Logarithmic product expansion

Putdelta=1-e^(-t) andlambda=-logdelta. Euler--Maclaurin applied to
h(x)=log(1+exp(lambda-x)) gives

logF(e^(-t))
 =-Li_2(-e^lambda)/t -log(1+e^lambda)/2
  -sum_{m>=1} B_(2m)t^(2m-1)Li_(2-2m)(-e^lambda)/(2m)!.

The sum is asymptotic. Use the exact dilogarithm reflection identity to replace its first term by

[lambda^2/2+c+Li_2(-delta)]/t.

Since lambda=L+t/2-t^2/24+t^4/2880-..., the two terms proportional toL at ordert^0 cancel. Therefore

logF(e^(-t))=(L^2/2+c)/t-1+sum_{j>=1}t^jP_j(L),

with
P_1=(5-L)/24,
P_2=-1/9,
P_3=(2L+245)/5760,
P_4=-11/900,
P_5=-(8L+2037)/1451520,
P_6=341/52920.

EveryP_j is affine inL. The symbolic checker computes these coefficients from the finite Euler--Maclaurin expression, not by fitting data.

For each fixed truncation J, the remainder is O_J(t^(J+1)(1+L)). The exact modular argument below proves this uniformly on the complex neighborhood needed for coefficient extraction, without having to differentiate an Euler--Maclaurin remainder.

## Exact modular decomposition and uniform remainder

Let q=e^(-t), delta=1-q, lambda=-log(delta), u=lambda/t-1/2, and Q=e^(-4*pi^2/t). Jacobi's triple product gives

F(q) (-delta;q)_infinity (q;q)_infinity
 = sum_{k in Z} exp[-t*k^2/2+(lambda-t/2)*k].

Poisson summation of the Gaussian and the eta modular transformation give the exact identity, for every real t>0,

F(e^(-t)) = exp[K(t)] * Theta(u,t)/(Q;Q)_infinity,

K(t)=(lambda^2/2+c)/t-lambda/2+t/12-G(t),
G(t)=log(-delta;e^(-t))_infinity
    =sum_{j>=1} (-1)^(j+1)*delta^j/[j*(1-e^(-jt))],
Theta(u,t)=sum_{m in Z}e^(-2*pi^2*m^2/t)e^(2*pi*i*m*u).

The normalized modular quotient itself has an exact convergent sector expansion

Theta(u,t)/(Q;Q)_infinity=sum_{r>=0}D_r(u)exp(-2*pi^2*r/t),
D_r(u)=sum_{m in Z: m^2<=r, r-m^2 even}p((r-m^2)/2)exp(2*pi*i*m*u),

where p(k) is the ordinary partition function and p(0)=1. The coefficient at each action is a finite real trigonometric polynomial. Its first values are D_0=1, D_1=2cos(2*pi*u), D_2=1, D_3=2cos(2*pi*u), D_4=2+2cos(4*pi*u). For every fixed action cutoff R, the positive-real-t tail is O_R(exp(-2*pi^2*(R+1)/t)), uniformly in real u.

The series for G is absolutely convergent since 0<delta<1. The theta quotient is an exactly specified correction to the exactly specified core exp K. For real t its first correction is 2e^(-2*pi^2/t)cos(2*pi*u)+O(e^(-4*pi^2/t)); it is not inferred from an optimally truncated power series. This is a genuine normalized modular sector decomposition of the generating function. It does not yet identify the exponentially small sectors of its coefficients.

References for the standard identities: DLMF17.8.1 (Jacobi triple product), DLMF17.2.6_1 (Euler product modular transformation), and Poisson summation of a Gaussian. The signs and constant t/12 were independently tested numerically in verify_modular.py.

For a complex z with |z-t|<=t/(K_0 L^2), where K_0 is a fixed sufficiently large constant, use delta(z)=1-e^(-z), lambda(z)=-Log(delta(z)), and the same identity by analytic continuation. Here |delta(z)|<=2t<1 and Re z>=t/2. Consequently

|1-e^(-jz)|>=1-e^(-j Re z)>=c_0 min(jt,1).

For fixed J, the tail of G after j=J+1 is O_J(t^(J+1)), uniformly on this neighborhood. Indeed, it is bounded by a constant times sum_{j>=J+2}(2t)^j/[j min(jt,1)]. Each of the finitely many remaining summands has a removable singularity at z=0 and admits an ordinary Taylor expansion. Also lambda(z)=Log(1/z)+an analytic power series at zero.

The modular factors are uniformly negligible: Re(1/z)~1/t and

|Im(lambda(z)/z)|=O(1/(tL)).

Thus the m-th nonzero theta term is bounded by

exp[-c_1*m^2/t+C_1*|m|/(tL)],

and their sum is O(exp(-c_2/t)); the dual Euler product has the same kind of bound. It follows directly that

log F(e^(-z))=S(z)-1+sum_{j=1}^J z^j P_j(Log(1/z))
              +O_J(t^(J+1)(1+L)),

uniformly on the full major neighborhood, where S(z)=((Log(1/z))^2/2+c)/z. There are no branch issues there: delta(z) has positive real part, the small-fugacity partner has no zero, and the theta factor is uniformly close to one. Nested-neighborhood Cauchy estimates are available if derivative versions are wanted, but the coefficient proof below does not require differentiating this remainder.

## Coefficient contour and minor arcs

Writeq=r e^(i theta),r=e^(-t),delta=1-r,D=|1-q| andalpha=delta/D. The triangle inequality gives

|F(q)|<=product_k(1+r^k/D).

For everyk<=floor(lambda/t), w_k=r^k/delta>=1. On these factors,

log(1+w_k)-log(1+alpha w_k)>=(1-alpha)/2.

SinceD^2=delta^2+2r(1-costheta), for|theta|<=pi,

1-alpha>=c_0 min(theta^2/t^2,1).

Consequently

|F(r e^(i theta))|/F(r)
 <=exp[-c_1(L/t)min(theta^2/t^2,1)].

For|theta|>=t/(K L^2), this isexp[-Omega(1/(tL^3))], smaller than every power oft. No additional root-of-unity major arcs survive.

On the remaining arc put S(t)=(L^2/2+c)/t. The saddle equation is exactly -S'(t)=n and S''(t)=t^(-3)V. Its higher cumulants are (-1)^k S^(k)(t)=t^(-k-1)V_k.

Here is a detailed remainder argument retaining the stated L powers. Write epsilon=sqrt(t), X=theta*sqrt(V)/t^(3/2), and fix a central cutoff |X|<=epsilon^(-1/4). On the intermediate arc between this cutoff and |theta|=t/(K_0 L^2), Taylor's theorem for S gives

Re[S(t-i theta)-S(t)-in theta]<=-c_3*t^(-3)V*theta^2=-c_3 X^2.

Indeed, the ratio of the cubic remainder to the quadratic term is O(|theta|/t)=O(L^(-2)); this follows either from explicit S or from V_3/V=O(1). The remaining logarithmic amplitude differs from its value at t by O(t(1+L)), uniformly, so it cannot spoil this bound once |X|>=epsilon^(-1/4). The intermediate arc is therefore exponentially small compared with every retained power of t.

On the central arc, replace the logarithmic amplitude by its finite expansion R_J. This makes a uniform multiplicative error O_J(t^(J+1)(1+L)). The normalized integrand is e^(-X^2/2) times exp(Q+R_J), with Q and R_J defined in the next section. Treat epsilon as a complex auxiliary variable while L and real X are fixed. The singularity at epsilon=0 in the exact phase expression is removable after the linear and quadratic terms have been separated. On the auxiliary circle

|epsilon|=rho=c_J/[(1+L)^(1/2)*(1+|X|)^3],

both Q and R_J are uniformly bounded. To see this, |w|=|epsilon X|/sqrt(V) is small, Q=O(|epsilon|*|X|^3/(1+L)), and R_J=O_J(|epsilon|^2*(1+L)). Choose c_J small and fixed. Hence Cauchy's Taylor remainder, through degree 2J+1, is bounded by

C_J |epsilon|^(2J+2)*(1+L)^(J+1)*(1+|X|)^(6J+6).

For the actual epsilon=sqrt(t), the condition |epsilon|<=rho/2 holds throughout the central cutoff for all sufficiently large L, since epsilon^(1/4)*(1+L)^(1/2)->0. Integrating the displayed remainder against e^(-X^2/2) gives exactly

O_J(t^(J+1)*(1+L)^(J+1)),

with no uncontrolled extra power of L. The odd Taylor coefficients integrate to zero on the symmetric central interval. Extending the finitely many even Gaussian moments to the whole real line has an exponentially small error. Expanding through the odd degree 2J+1 before cancellation is what produces the next integer power t^(J+1), rather than a half-power error. The product remainder, the intermediate arc, and the minor arcs are all smaller than or within this bound. This proves the main coefficient expansion with the advertised remainder.

## Finite all-orders coefficient rule

LetG be the Gaussian moment functionalG(X^(2m))=(2m-1)!! andG(X^(2m+1))=0. Setepsilon=sqrt(t), w=-i epsilon X/sqrt(V). Then

C_j(L)=G([epsilon^(2j)] exp(Q+R_J)),

Q=sum_{k>=3} i^k epsilon^(k-2) V_k X^k/(k! V^(k/2)),
R_J=sum_{r=1}^J epsilon^(2r)(1+w)^r P_r(L-log(1+w)).

Onlyk<=2j+2 andr<=j enterC_j, so this is a finite exact algorithm. Odd Gaussian moments remove half-integer powers and all square roots ofV. The amplitude evaluation at the displaced complex argument is necessary; omitting it loses the last two terms ofC_2.

## Inversion on the sequence range

LetY be a large positive target, y=logY, and now chooseL by the dominant inverse carrier

y=e^L B(L).

This is a different L from the forward saddle at a preassignedn. Define

N_0=e^(2L)A(L),
T=1+(3/2)L+(1/2)log(2*pi*V),
T'=3/2+V'/(2V).

The explicit inverse approximation is

Nhat(Y)=N_0+e^L T+(T^2+2TT')/(2V)-C_1(L).

The range-inverse conclusion is

Nhat(a_n)=n+O(e^(-L)(1+L)^3)=n+o(1).

Thus nearest-integer rounding recoversn froma_n for all sufficiently largen. The constant-order correction includes-C_1, which is unbounded of orderL; the relative leading coefficient equivalent alone is insufficient for an accurate inverse.

To derive the formula putH(L)=e^LB, N(L)=e^(2L)A. The exact identities

H'(L)=e^LV, N'(L)=e^(2L)V, dN/dH=e^L

turn reversion into an explicit differential calculation. The logarithmic forward correction is

h(L)=-T+log(1+sum_{j>=1}e^(-jL)C_j(L)).

WithD_y=e^(-L)V^(-1)d/dL, the formal all-orders inverse is

N(H^(-1)(y))+sum_{k>=1}(-1)^k/k! D_y^(k-1)[e^L h(L)^k].

At each exponential order only finitely manyk contribute after the leading unbounded correction is organized by powers ofe^(-L). The first term yieldse^LT-C_1, and thek=2 term yields(T^2+2TT')/(2V). Taylor remainders, together with the forward error and slope~t, turn any fixed sufficiently deep truncation into a range-inverse approximation. This is formal/range inversion; no exact continuous interpolation has been singled out.

## A direct inverse error proof

For a completely analytic range statement, define the smooth first-correction model M_1(x) by the forward formula with the factor 1+t C_1(L), where x=e^(2L)A(L). This factor is positive for sufficiently large L, and (log M_1)'(x)=t(1+o(1))>0. The coefficient theorem gives

log a_n-log M_1(n)=O(t^2 L^2).

Its amplification under the inverse of M_1 is O(t L^2). To verify the explicit Nhat without relying on a purely formal Lagrange argument, let L solve H(L)=y and set

Delta_1=t*T/V,
Delta_2=t^2*[T*T'/V^2-(V+V')*T^2/(2V^3)-C_1/V].

Taylor expansion in the equation

H(L+Delta)-T(L+Delta)+log(1+e^(-(L+Delta))*C_1(L+Delta))=y

shows that Delta_1+Delta_2 has residual O(t^2(1+L)^2). The derivative in Delta is asymptotic to t^(-1)V, so the root error is O(t^3). Expanding N(L+Delta)=e^(2(L+Delta))A(L+Delta) through Delta^2 gives exactly Nhat, with index error O(t(1+L)^2). Combining this with the coefficient error proves the stated weaker O(t(1+L)^3) range bound, and in fact supports the sharper quadratic-log error. Every derivative estimate here follows from explicit rational functions of L and T=O(L).

For arbitrary fixed order, take a deeper positive smooth coefficient model, and apply the same Taylor residual procedure or the displayed Lagrange coefficient rule. This proves an all-orders range reversion with controlled finite truncations. It still does not select an exact interpolation through all integer sequence values.

## Threshold qualifications

The factor withk=1 is1/(1-q). All other factors have nonnegative coefficients, and thek=2 factor alone has positive coefficients in every degree>=2. Hencea_n-a_(n-1)>0 for every n>=2. The thresholdN(Y)=min{n>=2:a_n>=Y} is well defined forY>a_1.

A forward relative errorO(t^2L^2) is a logarithmic error of that size, amplified by1/t under inversion. Therefore the smooth first-correction model gives uncertaintyO(tL^2)=o(1) in index. A ceiling is justified only if the entire certified or asymptotic inverse bracket lies between the same two consecutive integers. AtY=a_n use nearest-integer rounding, not an unqualified ceiling. Near a threshold, retain the two adjacent candidates and compare the exact sequence values. The current derivation has no explicit numerical onset constant.

## Scope of the term transseries

The coefficient expansion is organized in powers oft=e^(-L), with rational functions ofL as coefficient blocks. Each block can in turn be expanded in inverse powers ofL; retaining its exact rational form is stronger. The dominant inverse carrier can be solved numerically or itself expanded throughLambert-W-style logarithmic reversion. These are rigorous all-orders logarithmic/exponential scales. The exact modular identity supplies normalized exponentially small sectors for the generating function on the positive real t-axis. The coefficient minor-arc bound proves a remainder beyond every fixed power of t but does not identify coefficient-sector amplitudes or a Stokes classification. The absolutely convergent exact j-series in its stated domain must not be confused with a convergent power-log series at t=0: its terms have boundary root-of-unity singularities accumulating toward zero, and the proof only asserts asymptotic expansion.


## One additional inverse order

Writing D_2=C_2-C_1^2/2, the next inverse correction is e^(-L) B_1(L), where

B_1=-D_2-(T*C_1)'/V+(1/(6V))*d/dL[(T^3+3T^2*T')/V].

This follows by keeping the first three Lagrange terms and the second logarithmic amplitude coefficient. It is an optional refinement; the shorter Nhat already has o(1) range error.

## Numerical checks and their limits

The checkers use exact integer coefficient generation followed by high-precision evaluation. They do not replace the analytic proof and do not certify an effective onset. Through n=10000, selected tests of Nhat(a_n) round to n. At n=10000 its error is approximately -0.0052252911442; the dominant inverse carrier alone has error approximately -261.3711894. Modular identities were checked to at least90 decimal places for five positive t values.
