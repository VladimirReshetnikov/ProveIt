# Sixth-order skewness penalty: independent proof audit notes

## Claim
For fixed N>=3 and nearby positive target frequencies lambda_j, counting duplicates as vanishing order, let kappa=mean(lambda), delta_j=(lambda_j-kappa)/kappa, d=max|delta_j|, p3=sum delta_j^3. The shortest support diameter of a probability measure whose Fourier transform vanishes at all targets is

B = N*pi/kappa + N*pi^5*p3^2/[180*(N-1)*(N-2)*kappa] + O_N(d^8/kappa).

For N=3,4, locally B>=N*pi/kappa exactly, with equality iff the centered frequency multiset is invariant under sign reversal. This strengthens Article fil:thm:split's O(d^3), and answers its open question asking for the next term and sign.

## Analytic coefficient coordinates, with no formal-root gap
Scale kappa=1. Put Q_e(y)=y^N-e1*y^(N-1)+e2*y^(N-2)-...+(-1)^N*eN. The monic division remainder of an entire function f(1+y) modulo Q_e is analytic in the real coefficients e near0. An explicit contour expression is
R_e(y)=(1/(2pi i)) int_C f(1+z)/Q_e(z) * [Q_e(z)-Q_e(y)]/(z-y) dz,
where C is a fixed small circle enclosing all roots. The quotient in brackets is polynomial of degree N-1 in y; this is the interpolation remainder (the polynomial matching f at roots with multiplicities). At e=0 its coefficients are f^(k)(1)/k!.

Take f(omega)=sum_{j=0}^N w_j exp(i omega u_j), fix u0=0, and impose R_e=0 (N complex equations) plus sumw=1. At e=0 the solution is u_j=j*pi and w_j=binom(N,j)/2^N. Its real Jacobian is invertible: in the equivalent moments sum w_j u_j^k exp(iu_j)=0 (k<N), imaginary parts of the variation are a Vandermonde system in w_j du_j for j=1,...,N. Thus du=0; real parts plus mass then force dw=0. The real analytic IFT supplies real analytic ordered nodes, positive weights, and endpoint L(e)=uN(e) for ALL real coefficient vectors e near0. Their polynomial roots may be nonreal. This independent-coefficient continuation is essential below and legitimate.

For real frequency roots the branch is the GLOBAL optimum. The real moment space has a certificate g_e vanishing at all N+1 nodes, and to order2 at interior nodes, normalized g_e'(uN)=-1. A rank argument from the invertible full Jacobian gives a one-dimensional certificate space, analytic in e. At0 it is a positive multiple of (-1)^(N-1) sin(u) prod_{k=1}^{N-1}(u-k*pi), positive between its nodes, with simple endpoints and double interior zeros. Strict curvature and derivative signs persist locally, so g_e>=0 on[0,L(e)]. Any competing measure of support width<=L can be translated into[0,L], integrates g_e to0, and is supported on those nodes. Independent mass/moment columns fix the weights, which occupy both endpoints. This proves global optimum and uniqueness. For comparison with repo this re-proves fil:thm:split's local analytic branch.

## Mirror stationarity
For distinct real centered roots symmetric about0, r_j=exp(i*pi*lambda_j) come in conjugate pairs, P(z)=prod(z-r_j) has strictly positive coefficients (roots near-1). Its coefficients normalized by P(1) on nodes j*pi solve the moment problem; uniqueness gives L=N*pi.

At such a base a real variation has transform F1(omega)=A(z)+i*omega*B(z), z=exp(i*pi*omega), deg A,B<=N, real coefficients, A(1)=0, B(0)=0. If j* is reflection partner (lambda_j*=2-lambda_j), subtract the conjugated partner root equation to get
B(r_j)= -pi/(2P(1)) *r_j P'(r_j)*(dlambda_j+dlambda_j*).
Lagrange interpolation of B(z)/z gives its leading coefficient = -pi/P(1)*sum dlambda_j. Since endpoint weight=1/P(1), dL=-pi*sum dlambda_j. Thus on e1=0 all partial derivatives of L are zero at every distinct symmetric-root configuration.

The even coefficient vectors of such configurations contain a nonempty open subset in the even-coordinate subspace (Vandermonde in distinct positive squared roots). By analytic identity, throughout a neighborhood in coefficient space, L(even,odd=0)=N*pi and derivatives in all odd coordinates vanish. Hence, on e1=0,
L-N*pi = sum_{a,b odd, >=3} e_a e_b G_ab(e).
This is just the multivariate Taylor formula in the odd coordinates. Therefore the weighted-degree6 term is A_N e3^2, there is no weighted degree7 term, and the rest is O(d^8). For N=3,4 only e3 is odd, so exact factorization is e3^2*G(e), positive once G(0)=A_N>0.

## Computing A_N
Use independent coefficient curve e3=t, all other e_k=0 (including e1). This gives Q_t(y)=y^N-t*y^(N-3). Some roots are complex; it is an analytic coefficient probe justified above, not an assertion that it is a real-frequency path.

Write w_j(t)=w_j+t*a_j+t^2*a2_j+..., u_j(t)=j*pi+t*v_j+t^2*v2_j+.... Set z=exp(i*pi*omega), w=z+1 (different symbol from masses), ell=log(1-w), y=ell/(i*pi). F0=2^-N*w^N. F1(omega)=A(z)+i*omega*B(z), A=sum a_j z^j, B=sum w_j*v_j z^j.

Near omega=1+y, divisibility by Q_t gives F1(1+y) congruent -F0/y^3 modulo y^N. Reality of the masses/nodes gives negative-cluster divisibility by y^N+t*y^(N-3), so F1(-1+y) congruent +F0/y^3. Subtract/average:
B congruent i F0/y^3,
A congruent F0/y^2, modulo w^N.
Mass A(1)=0 and anchoring B(0)=0 fix all degreeN ambiguities. Expanding log(1-w) yields exactly
A(z)=-pi^2/2^(N+2) *(z-1)^2*(z+1)^(N-2),
B(z)= pi^3/2^(N+1) *z*(1-z)*(z+1)^(N-3).
Thus v0=vN=0 and
v_j=pi^3*j*(N-j)*(N-2j)/(2*N*(N-1)*(N-2)).

At order t^2 put
F2(omega)=A2(z)+i*omega*B2(z)-omega^2*C(z)/2,
B2=sum (w_j*v2_j+a_j*v_j)z^j,
C=sum w_j*v_j^2*z^j.
B2(0)=0, deg C<=N-1, and leading coeff of B2 is 2^-N*A_N.

Second-order polynomial divisibility gives
F2(1+y) congruent -F1(1+y)/y^3-F0/y^6,
F2(-1+y) congruent +F1(-1+y)/y^3-F0/y^6, mod y^N.
Subtracting and using log variables gives
B2 congruent R(w):=pi^3*A/ell^3+pi^2*B/ell^2-ell*C/pi (mod w^N).
Let S_N(R)=sum_{k=0}^{N-1}[w^k]R. The remainder polynomial has degree<N, and B2(0)=0 means B2 = trunc_{<N}R - S_N(R)*w^N. Therefore A_N=-2^N*S_N(R).

For the A,B terms, direct expansion gives
-(w-2)^2*w^3/(4*ell^3)+(w-1)*(2-w)*w^2/(2*ell^2)
 = w^2/6-w^3/4+11w^4/120+O(w^5).
Thus S_N(R_AB)=pi^5/(120*2^N) for every N>=3.

For C, write c_j=w_j v_j^2, j1..N-1. Since C(w-1)/(1-w)=-sum_j c_j(w-1)^(j-1),
S_N(-ell*C/pi)=1/pi *sum_j c_j [w^(N-1)]ell*(w-1)^(j-1)
= -1/pi *sum_j c_j*(N-j-1)!*(j-1)!/(N-1)!
= -N/(pi*2^N) sum_{j=1}^{N-1}v_j^2/[j*(N-j)].
Use exact power sum
sum_{j=1}^{N-1}j*(N-j)*(N-2j)^2=N*(N-1)*(N-2)*(N+1)*(N+2)/30.
This gives S_N(R_C)=-pi^5*(N+1)*(N+2)/(120*2^N*(N-1)*(N-2)).
Combining yields
A_N=N*pi^5/[20*(N-1)*(N-2)].
Finally e3=p3/3, so the coefficient of p3^2 is A_N/9, as claimed.

## Exact equality in N3,4
G(0)=A_N>0, so locally L>=N*pi, equal iff e3=0. On centered real N3 or N4 tuples the root polynomial has only even powers (N4) or is y times an even polynomial (N3) exactly when e3=0; this is equivalent to reflection symmetry. In N3 one target must equal the mean, other two equidistant. In N4 the targets form two equidistant pairs, counting repetitions.

## Numeric checks (illustrative, not proof)
For delta=(-epsilon,-epsilon,2epsilon), N3, independently solve a centered 4-atom filter satisfying double root at1-epsilon and simple root at1+2epsilon. Excess/(36*epsilon^6) tends pi^5/120. General N3..10 checks use centered N+1 atom filters and Hermite divided differences, agree with N*pi^5/[180*(N-1)*(N-2)].
