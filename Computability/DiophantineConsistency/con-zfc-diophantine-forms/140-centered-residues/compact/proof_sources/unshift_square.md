# Remove the auxiliary T shift for the doubled V-squared weights

This is a code-free ordinary proposal for the two V^2-weight branches.
It changes b=c(T+alpha)-R to b=cT-R, with T still strictly positive.
All other definitions and the complete coherent indexed coefficient tuple
are retained. No program, source generator, import, compilation, Lean or
rendering ran, and no new evaluator or numerical endpoint is supplied.
Deleting the private addition suggests83/436 and80/750; those are only
literal-layout predictions until actual complete graphs are materialized
and independently checked. The maintained85/328 page is unchanged.

The soundness proof must change: T-alpha may be nonpositive, and the old
early b>c bound is unavailable. An absolute auxiliary-trace bound replaces
it before transport. The argument below does not license an unshifted bV
weight. Any such extension requires its own additional pretransport proof.

## 1. Whole equation and exact scope

The unsheared inputs are J,F,alpha,i,T,w,Y,n,eta,zeta>0. The q-cube inputs
replace the independent Y by s>0 and define Y=q^3*s. The four fixed ports
beta,K0,MC,MF are exactly the complete directly indexed BFS943 tuple of
the pinned parents, including Start0/Forbidden1 and literal initializer4.
No individual coefficient is replaced. Put

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, mu=q^2+1,
    k=eta+zeta, c=k*Y+eta, A=mu*Y*(X+1)+1,
    Delta=A^2-1, H=4*A-5, V0=X*mu^2*Y^2,
    E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fsq=1+4*a*F0=(1+2*a)^2,
    Q=Delta*(Fsq-1)=4*Delta^2*U^2*G,
    b=c*T-R, V=Fsq*b-c, L=V^2,
    Kpos=X*(3*c-2*X)+2.

For the unsheared chart let

    P=q^3*h, M=P*mu^2*H,
    Z=P*mu^2*[H*(n-L*B)+Kpos]
      +H*[mu^2*(h*Y-q^3*B)-P*e].

For the q-cube chart let

    M=h*mu^2*H,
    Z=h*mu^2*[H*(n-L*B)+Kpos]-H*[mu^2*B+h*e].

In either case define RG=M^2*G and the complete polynomial

    N=Q*(Z^2-RG*V^2)+(RG-Z^2).

Every abbreviation is polynomial and adds no unknown. The proposal is
N=0 over the stated ten positive inputs. Its equivalent proof form is

    (Q-1)*Z^2-M^2*G*(Q*V^2-1)=0.

These are exactly the two pinned V^2 parents with only the displayed b
definition changed. BINDING records the entire actual T/Tp occurrence
sets, private addition and sole consumer; no diagram is emitted here.

## 2. Root recovery allows either sign of b and V

The unchanged unconditional bounds give q>=32,mu>=1025,k>=2,c>=3,
A>4,Delta>=3,U>=c^2,E>1,a>0,Fsq>c+1,Q>1,M>0. For integral b,
b=0 gives V=-c; b!=0 gives |V|>=Fsq-c>1. Thus Q*V^2-1>0 before
any transport sign.

The accepted product-square valuation argument applies unchanged:
Q is divisible by G and both Q-1,Q*V^2-1 are -1 modulo G. It recovers
G=g^2 with g>0 even if M shares prime factors. Coprime E,F0 then give
E=tau^2,F0=f0^2,g=tau*f0. Rational adjacent-Pell descent gives an integer
y>0 and signed integral carrier z=Z/M=epsilon*g*y with

    Q*V^2-(Q-1)*y^2=1, epsilon in {-1,1}.

The proof-defined doubled strong pair f=1+2a,I=2U*g satisfies
f^2=Fsq,f^2-Delta*I^2=1,c^2|I and Q=(Delta*I)^2. Its even strong
index is permitted by the retained normalized contracts.

At this point b=0 is impossible. It would give V=-c and

    y^2-c^2=(c^2-1)/(Q-1).

Since I>=c^2,Delta>=3, one has Q>=9c^4>c^2. The right side is strictly
between0 and1; the left side is an integer. This excludes that case
without assuming any sign of R,B,C or V.

## 3. Absolute trace bound before transport

Put D0=Delta*U^2. Since c>=3,U>=c^2,Delta>=3, D0>=243. As a=D0*E
and g^2=E*(1+a),

    a^2/g^2=D0*a/(1+a)>D0/2>9.

Thus a>3g. Also a>=c. For nonzero integral b,

    sign(V)=sign(b),
    |V|>=Fsq*|b|-c>=Fsq-c>a>3g,
    |V|>|b|.

Here Fsq=(2a+1)^2 and a>=c make Fsq-c>a and Fsq>c+1 explicit.
The adjacent norm gives y/|V|<sqrt(Q/(Q-1))<3/2, hence

    g*y<V^2/2=L/2.

No fifth-index argument, b>c, positive V or decoded rank has been used.

## 4. Signed folding and the negative-B contradiction

The retained strong/auxiliary all-index folding interface requires the
strong norm, c<=I,c^2|I, the adjacent norm and V=-c modulo f. It imposes
no sign on V. The last congruence follows from V=f^2*b-c for this new b
just as for the old shifted b. It gives c=psi_A(p) at an odd p>=1.

The first norm E=tau^2 gives k=2*psi_(2V0+1)(n0). As in the accepted
parent, n0=1 would give k=2 and c=2Y+1 strictly between1 and2A, which is
impossible. Therefore

    n0>=2, k>=8V0+4, c>kY>=k>8q^5, c>X, Kpos>0.

In particular kappa=Kpos/H>0. For rho=e/mu^2 the new exact identity is

    e=b-c*T+k-1<b,

because T>=1 and c>k. Thus rho<b/mu^2<|V|/mu^2. This is a one-sided
estimate and does not assume e or rho nonnegative.

Set t=B/h,W=1+h*L, and sigma=Y/q^3>0 in the unsheared chart, sigma=0
in the q-cube chart. The complete carrier in section1 gives

    z=n+kappa+sigma-W*t-rho,
    n=epsilon*g*y-kappa-sigma+W*t+rho.

If B<=-1 then W*t<=-L-1/h<-L, so

    n<L/2-L+|V|/mu^2<0.

The final inequality uses |V|>1 and mu^2>2. It contradicts the actual
positive n. Hence B>=0 and (K0+w)*C>=F>0 forces C>0.

## 5. Restore orientation, then all later interfaces

Only now invoke the unchanged mask conclusion3q<R<q^4-2. Since
c>8q^5>2R and T>=1,

    b=c*T-R>=c-R>0,
    V=Fsq*b-c>=Fsq-c>0.

This does NOT restore b>c: T=1 permits b=c-R<c. No later argument below
needs b>c. The old fifth-index bV proof is not invoked.

The complete later dependencies were audited as follows:

| Parent use | Exact license after this change |
| --- | --- |
| Early shifted bound b>c and positive V | Replaced by sections2–4; V>0 restored only after C>0. |
| rho<b/mu^2 | New identity b-e=cT-k+1>0. |
| Strong rank | Same f,I,c^2|I,c>2p and c>2R. |
| Signed auxiliary index | Same V=-c mod f and V=-R mod c; latter uses f^2=1 mod c. No alpha shift. |
| Rank p=R, parity q even/J odd | Same normalized rank and signed-index proof; all positive traces needed later are now restored. |
| Carrier integrality and mu denominator | Same integer z,integer L and W=1 mod h; only after parity use gcd(mu^2,PH)=1, or gcd(mu^2,hH)=1 in q-cube. |
| First-index/ratio and whole-product projection | Depend on A,X,Y,c,k,R, integral carrier and denominator conclusions; T and b>c are absent. |
| Remaining source fractions | Same kappa,sigma,t conclusions; q-cube has q^3|Y literally. |
| Fixed-minus parity/half-binomial/native reconstruction | Same restored strong/auxiliary residues and positive V; fresh unscaled source witnesses are reconstructed. |

More explicitly, the unsheared denominator proof gives mu^2|e followed
by H|P*Kpos. In the q-cube chart it gives H|h*Kpos, which implies the
weaker inherited H|q^3*h*Kpos. The whole-product projection cancels only2
through odd H, bounds the entire product and recovers X=2^R. The remaining
fractions restore the native arithmetic as in the accepted source. No
newT-alpha positivity is smuggled into any invocation of an old theorem.
The accepted complete indexed native/controller and C222/ZF-to-ZFC
contracts therefore supply a finite syntactic refutation.

## 6. Positive completeness and the actual witness maps

There is a simple pointwise map in one direction. From any positive zero
of the corresponding shifted parent, put

    T_new=T_old+alpha,

and fix all other independent inputs and every fixed port. Then
c*T_new-R=c*(T_old+alpha)-R, so b,V,L,Z,M,N are unchanged. The new T is
positive. This proves parent-zero to new-zero without a new Pell choice.
The formal inverse T_old=T_new-alpha is not claimed positive.

For a constructive zero directly from a finite refutation, retain the
whole canonical indexed family, including R>3q,R=3 modulo4 and, for
q-cube, q^3|Y. Choose the same fresh seed period modulo c^2*tau and double
the seed, as in the repaired parent. Its auxiliary construction gives

    S=Delta*I, V*=chi_S(R)/S, y=psi_S(R),
    T*=(V*+c+R*f^2)/(c*f^2).

Source61 section5 proves T* a positive integer under its stated generic
auxiliary hypotheses. Set the new T=T*, not T*-alpha. Then the new b,V
are exactly the parent's canonical b,V. Even the generic R=3 auxiliary
example T*=1 is positive here; it is not a counterexample to this unshifted
construction. The full native family still retains its actual R>3q bound.

Canonical g>kappa+sigma and t,rho>=0 allow the same positive carrier
n=g*y+W*t+rho-kappa-sigma. For q-cube sigma=0, equivalently keep the
already canonically sheared n. Every coordinate is positive and N=0.
Conversely section5 decoded a refutation from each new positive zero;
canonical predecessor witnesses can then be rebuilt if desired. This is
an existential equivalence, not a positive pointwise inverse on every
new tuple. It composes with the same ordinary no-zero/Con(ZFC) contract
without asserting either side separately.

## 7. Literal and degree boundary

The actual unsheared parent has T only in source row47, Tp=T+alpha; Tp
only feeds row48,cT=c*Tp. The q-cube parent has exactly the corresponding
rows48/49. BINDING pins the complete occurrence sets. Removing Tp and
feeding raw T to that one product is a private one-addition change; alpha
remains a live input through the unchanged C/R definitions. All other
literal definitions and coefficient payloads are intended unchanged.
The manual operation predictions are83=(50,18,15) and80=(48,18,14), in
product,sum,difference order. No graph was emitted or counted here.

For the unsheared branch c*alpha has degree3 below R's degree4. Its global
degree436 highest form is unchanged:

    2^14*q0^200*w^46*Y^104*i^20*k0^60
       *(q0-F)^4*(q0-F-alpha)^2.

For q-cube, the degree6 leading b becomes k0*q0^3*s*T instead of
k0*q0^3*s*(T+alpha). Its global degree750 highest form becomes

    2^14*i^20*q0^506*w^46*s^108*k0^64*T^4*(q0-F-alpha)^2,
    q0=beta*J, k0=eta+zeta.

The same selected coefficients2^14*beta^200 and2^14*beta^506 are nonzero.
These are ordinary degree arguments, not a finite-check acceptance or a
new projected metric. A later source packet must materialize full graphs,
bind every row/free-port identity and coefficient, verify the complete
highest forms and all live costs, exercise actual controls and reproduce
normal/optimized results after separate review/release. No bV extension,
compiler, source execution, Lean change or canonical page update is made.
