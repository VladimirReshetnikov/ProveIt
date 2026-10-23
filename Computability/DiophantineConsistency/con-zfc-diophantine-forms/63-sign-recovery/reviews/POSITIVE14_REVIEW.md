# Independent mathematical audit: the fourteen-positive degree-34 adapter

Internal AI-assisted mathematical review of the frozen `positive14/build.py`, `positive14/pell14_degree34.json`, and `positive14/PROOF.md`. The primary circuit uses 87 live arithmetic operations. This is not an external peer review or a new proof-assistant certificate.

## Verdict

The new existence reduction is mathematically valid relative to the exact inherited normalized Pell/compiler interface. In particular, removal of the index quotient h is supported by a noncircular bootstrap: positivity of the two first-root gap coordinates excludes Pell index one and supplies the size bound needed by auxiliary rank recovery before h is restored.

The literal polynomial is the sum of squares of five residuals A0, A1, At, As, Au. Its fourteen supplied positive unknowns are J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,t. Intermediate registers are not additional unknowns.

## 1. Outer interface and integral first root

Write q=beta J+1, X=wq, k=eta+zeta, c=kY+eta, a=(X+1)Y, H=4a+3, Delta=(a+2)^2-1, ell=XkY^2, and use the authentic source R. The final shifted transport residual is At=(K0+w)C-F-z(q-1), with C=q-F-alpha. Its positive variable z is the old source transport variable minus one. At=0 restores the old source equation upon setting z_old=z+1. Positivity therefore gives C>0 and the authentic mask bounds q>=16 and 3q<R<q^4-2.

A0=0 says

    [q^3(ell+r)+Y]^2=q^6[ell(ell+k)+1].

The rational number tau=ell+r+Y/q^3 has integer square. A rational square root of an integer is integral, so tau is an integer and q^3 divides Y. Set s=Y/q^3>0. Then

    tau=ell+r+s>ell+1,
    tau^2-XY^2(XY^2+1)k^2=1.

The first Pell classification, for P0=2XY^2+1, gives k=2psi_P0(n), tau=chi_P0(n), n>=1. If n=1 then k=2, ell=2XY^2 and tau=ell+1, contradicting r+s>=2. Thus n>=2.

This supplies the crucial early bound

    k>=4P0>8XY^2,
    c>kY>8XY^3>=8q^10>2R.

It was obtained without a sign or existence assumption on deleted h.

## 2. Integral positive main root

Set M=4q^4, gap=k-R-1, b0=X+ac, Z=Mt-gap and W=Mb0+HZ. Since a>=3, H=4a+3<=5a. Consequently b0/H>c/5>k, because Y>=q^3>5. Also gap<k. Therefore

    W>Mb0-Hk>0.

A1=0 gives (W/M)^2=1+Delta c^2. Rational-root integrality gives the positive integer D=W/M. Thus the main Pell equation holds and M divides H*gap.

For A=a+2, classify D=chi_A(p), c=psi_A(p), p>=1. Since P0>A and c>k, Pell growth gives p>n>=2, hence p>=3. In particular c>2p. The prior bound already gave c>2R.

## 3. Strong and auxiliary rank, before index recovery

The shared register f^2-1 is used in both As and Q, which saves one arithmetic operation without changing the residual. As=0 is normalized strong Pell:

    f^2-Delta*(i*c^2)^2=1.

All f,i,c are positive. Classification gives f=chi_A(m), psi_A(m)=i*c^2. Strong divisibility yields p|m. Writing m=pb, expansion of the Pell unit modulo c^2 gives

    psi_A(pb)/c = b*chi_A(p)^(b-1) modulo c.

Since the left side is divisible by c and chi_A(p) is coprime to c, we get c|b. Hence pc|m, so c|m and m>2p.

Let Q=Delta*(f^2-1)=(Delta*i*c^2)^2>1 and y=V+u, where V=c(Tf-1)-Rf^2. Au=0 is identically

    Q*V^2-(Q-1)*y^2=1.

The auxiliary odd-index/step-down argument uses V=-c modulo f and V=-R modulo c. The second holds because f^2=1 modulo c, already a direct consequence of normalized strong. Squaring the first congruence removes any sign of V. The signed index theorem yields p=+R or -R modulo c. Since 0<p,R<c/2, it yields p=R.

The source requires y positive when recovering a positive-domain assignment. This follows from the new equation: if y<=0, then V=y-u<y<=0 and V^2-y^2>=1. Hence QV^2-(Q-1)y^2=Q(V^2-y^2)+y^2>=Q>1, a contradiction. Thus y>0. No fresh auxiliary witness is needed for this sign restoration.

## 4. Recover the deleted index quotient and main quotient

Because q^3|Y and X=wq, the integer a=(X+1)Y is divisible by q^3. H is odd and H=3 modulo q^3. Every common prime of H and M=4q^4 must therefore be 3; if 3 divides q, its valuation in H is exactly one. Hence gcd(H,M)<=3.

Set mu=M/gcd(H,M). We know mu divides gap and mu>=4q^4/3>R. The recurrence congruence psi_P0(n)=n modulo P0-1=2XY^2 gives k=2n modulo 4XY^2. Since 4XY^2=4w*s^2*q^7 is divisible by M=4q^4, we obtain k=2n modulo M. This argument does not assume q is even. Thus mu divides 2n-R-1. The inequalities 1<=n<p=R imply abs(2n-R-1)<R<mu. Therefore

    2n=R+1.

The stronger recurrence congruence psi_P0(n)=n modulo 2XY^2 gives

    gap=k-2n is divisible by 4XY^2=4EY,

where E=XY. Since n>=2, the gap is positive. It follows that h=gap/E is a positive integer. Also 4EY=4w*s^2*q^7 is divisible by M, so gamma=t-gap/M is an integer and D=b0+H*gamma.

The main norm gives D>(a+1)c. Since c>X, we get D-b0>c-X>0, hence gamma>0. Every old positive source coordinate has now been recovered, including s,h,tau,y,gamma. The exact inherited compiler can be invoked at this stage.

## 5. Completeness

Start from an authentic canonical positive source witness. Put Y=sq^3. Retain all uneliminated coordinates except for the exact transport shift z=z_old-1. This new z is positive: canonical w=2^R/q>q>F, C>=1, K0>=0 give (z_old-1)(q-1)=(K0+w)C-F>0. Define

    r=tau-ell-s,
    t=gamma+(k-R-1)/M,
    u=y-V.

The index identity R=2n-1 and the first recurrence make k-R-1 divisible by M, so t is a positive integer. For r, the first Pell relation and ell>k give

    tau-ell=(ell*k+1)/(tau+ell)>k/3.

Canonical n>=2 gives k>8XY^2>3s, so r>0. A canonical auxiliary witness has V>1 and y>0. Its Pell equation implies y^2-V^2=(V^2-1)/(Q-1)>0, hence u=y-V>0. Each of the five residuals vanishes by substitution.

## 6. Exact degree check

Degree refers to the fourteen supplied coordinates. Put q0=beta J, k0=eta+zeta. The leading forms are X0=wq0, E0=wq0Y, c0=k0Y, a0=wq0Y, H0=4wq0Y, ell0=wk0q0Y^2 and M0=4q0^4.

Expansion after cancellation gives

    deg A0=12,
    deg A1=17,
    deg At=2,
    deg As=16,
    deg Au=15.

For A1, the exact identity is

    A1=M^2*(b0^2-Delta*c^2-1)+2M*b0*H*Z+H^2*Z^2,
    b0^2-Delta*c^2-1=X^2+2acX-Hc^2-1.

The three terms have degrees at most 15,17,16. The degree-17 term is

    128*w^2*q0^10*Y^3*k0*t.

Thus the sum of squares has exact degree 34 and leading homogeneous form

    16384*w^4*(beta J)^20*Y^6*(eta+zeta)^2*t^2.

In particular, the coefficient of w^4*J^20*Y^6*eta^2*t^2 is 16384*beta^20, nonzero for the fixed positive beta. This symbolic argument proves the upper bound and its attainment, rather than inferring exactness from samples.

## Limits

This audit checks the new mathematical adapter. It imports the same coherent four-port native coefficient tuple, native-window compiler, K215 calibration and Pell representation/index lemmas as the source constructions. It is not a new independent proof of those dependencies and does not certify consistency or inconsistency. The new expression uses neither variable exponentiation nor extra hidden quantified registers.
