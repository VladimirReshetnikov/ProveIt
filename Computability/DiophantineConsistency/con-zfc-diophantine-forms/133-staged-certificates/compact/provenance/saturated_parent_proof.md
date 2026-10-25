# Coprime Pell saturation: complete ordinary positive-source equivalence

This packet reviews and binds the four main ten-positive equations of
ConZFC_Saturated_Pell_2026-10-24.zip. The archive is pinned in SOURCE_PINS.json;
its complete member inventory is retained. The four exported source graphs
and complete compact44 BFS tuple are copied exactly. This proof explains
both unbounded directions and the full native composition, independently
of finite diagnostic runs. It does not assume or prove Con(ZFC), add a Lean
endpoint, or identify differently specialized K constants.

## 1. Actual free-port formulas

All ten independent inputs are positive integers. The four fixed ports
satisfy beta>=31 odd,K0>0,0<MC<beta<MF<2beta. Set

    q=beta*J+1, C=q-F-alpha, X=wq,
    mu=q²+1, k=eta+zeta, c=kY+eta,
    A=mu*Y*(X+1)+1, Delta=A²-1, H=4A-5,
    V0=X*mu²*Y², E=1+V0*(V0+1)*k², U=i*c²,
    R=[(q-1)(q-F)+alpha](q²-1)+(MC+q*MF)J,
    e=k-R-1, Bt=(K0+w)C-F, T'=T+alpha, b=cT'-R,
    Df=1+Delta*U²E, Q=Delta²*U²E, delta=Q-1,
    V=Df*b-c, Dy=Q*V²-1, G=E*Df,
    Cg=(A+lambda)*U*E, Kpos=X(3c-2X)+2, L=kT',
    P=q³(q-1), M=P*mu²*H,
    Z=P*mu²[H(n+V+Cg-L*Bt)+Kpos]
       +H[mu²((q-1)Y-q³Bt)-P*e].

Here lambda is fixed0(sharp) or1(upper), never an input. The source's
Am1 is A-1, Ap1 is A+1, Dtau is E, Hp is H, Dnum is Dy and Mtot is M.
The entire finalizer is

    fs=delta*Z², fg=delta*M²*G, fy=M²*Dy,
    N=(fs-fg-fy)²-4fg*fy.

For the direct chart replace w by positive x, X=q+x,
B=(qK0+X)C-qF, P=q^4(q-1), and replace only the numerator by

    Z=P*mu²[H(n+V+Cg-L*B)+Kpos]
       +H[mu²(q(q-1)Y-q³B-(q-1)X)-P*e].

These formulas are identities over the free four-port polynomial ring.
The independent checker collects every local polynomial interface, covers
every actual gate, checks the entire two-root norm and binds all displayed
fractions by cross-multiplied polynomial identities. No numerical sample
or coefficient substitution is used as an identity proof.

## 2. Root recovery before any transport premise

Unconditionally E>1,Df>c+1,Q>1,M>0 and delta>0. Since b is integral,
V=-c ifb=0 and otherwise |V|>=Df-c>1. Thus Dy>0. Put
Y*=Dy/delta. The squared radicals G=E*Df and Y* cannot coincide: equality
would give Q(V²-G)=1-G, impossible modulo E because E divides Q and G.

A zero has (z²-G-Y*)²=4GY*, z=Z/M rational. The preceding obstruction
excludes z=0. Therefore [(z²+G-Y*)/(2z)]²=G, and the complementary rational
number has square Y*. A rational square root of the positive integer G is
integral. Since gcd(E,Df)=1, both factors are squares: E=tau²,Df=f².

The remaining rational positive y with QV²-(Q-1)y²=1 is integral. For
v=|V| and y=a/m in lowest terms, m² divides Q-1. The exact transformation

    v'=(2Q-1)v-2(Q-1)y, y'=(2Q-1)y-2Qv

keeps v' integral and the same norm, preserves the reduced denominator m
since2Q-1=1 modulo m, and has -v<v'<v forv>1, usingv<y<Qv/(Q-1).
The first coordinate cannot vanish. Reflect signs and descend on the
positive integer |v|; atv=1 the norm givesy=1, hence m=1.
The full signed factorization now gives z=eps_g*f*tau+eps_y*y.
Neither sign of Z nor sign of V was assumed.

## 3. Restore the old kernel and prove transport sign acyclically

Inside the proof put I=U*tau. It is positive, c² divides I, and

    f²-Delta*I²=1, Q=(Delta*I)², V=f²(cT'-R)-c.

These are the actual accepted strong/auxiliary interfaces, with the
proof-only old scale i_old=i*tau. The source61 folding lemma gives
c=psi_A(p) with oddp>=1. The unchanged first Pell equation gives
k=2psi_(2V0+1)(n0). Ifn0=1 thenk=2 andc=2Y+1 lies strictly between
psi_A(1)=1 andpsi_A(2)=2A, impossible. Thus

    k>=8V0+4, c>kY>=k>8q^5, Kpos>0, H>3X.

The unconditional mask estimates are

    R<q^4+(alpha+2)q²,
    |R|<q^4+Fq³+(alpha+2)q²,
    |R|/mu²<F+alpha+1.

Consequently b=c(T+alpha)-R>=1 and V>1 before any B sign premise.
Writeu=y-V>0 andrho=e/mu², still rational. The adjacent norm and
Delta*Df=Q+Delta<2Q-2 giveu<b/Delta. As c<2kY,
Delta>8Y,Delta>mu²,

    u<kT'/4+F+alpha+1, rho<k/mu²+F+alpha+1.

IfC>=1 the literal mask formula givesR>0, so the sharper bounds are
u<kT'/4 andrho<k/mu².

The centers satisfyg=f*tau<Cg and0<Cg-g<(lambda+1)UE<=2UE.
For the sharp center,

    C0²-G=U²E²-E, C0-g>UE/(4A)>X.

The last inequality is unconditional: U>=c²,k>=2,c>kY,
E>V0²k² and A<4muXY giveUE>16V0²Y² andUE/(4A)>Xmu³Y^5>X.
Thus eps_g*g-Cg+X/q^4<0 even beforeq divides X.

On the ordinary chart W=1+(q-1)L, t=Bt/(q-1), s=Y/q³>0 and
kappa=Kpos/H>0. The exact signed carrier yields

    n=(eps_g*g-Cg)+(eps_y*y-V)-kappa-s+Wt+rho<u+Wt+rho.

SupposeBt<=-1. IfC>=1, Wt<-L andn<kT'/4+k/mu²-kT'<0.
IfC<=0 thenBt<=-F andWt<-FL, giving

    n<kT'/4+k/mu²+2F+2alpha+2-FkT'<0.

For k>=8, the negative of this last upper bound increases in positive
F,T,alpha and has minimum3k/2-k/mu²-6>0. Both cases contradictn>0.
ThusBt>=0 andC>0. The direct chart usesW=1+q(q-1)L andB/[q(q-1)];
the additional+X/q^4 is already absorbed by the center gap. IfC<=0,
B<=-qF makes the same contradiction stronger. No carrier divisibility
or decoded source condition was used to prove either sign.

## 4. Ordered rank, parity, denominators and whole-product projection

Transport positivity gives3q<R<q^4-2. Nowc>2R andc>2p; the literal
source61 rank lemma givesf=chi_A(m),I=psi_A(m),pc divides m andm>2p.
WithS=Delta I, the signed-index lemma uses S²=Delta(f²-1),c divides S,
V=-c modulof andV=-R moduloc to recoverp=R. All its strict bounds hold.
The rank is odd. Only now does the usual mask parity forceq even,J odd.
Then gcd(mu²,q³(q-1)H)=1 (or q^4 on the direct chart), sinceH=-1
modulomu andgcd(q-1,mu)=1. The signed carrier is integral, so this
licensesmu² divides e. The old first-index congruence then gives
n0=(R+1)/2, followed by the same offset-free ratio and height bounds.

The integer center adds no nonintegral terms. It yieldsH dividesP*Kpos.
UseKpos=HXc-2Kquad and cancel only2 becauseH is odd. The unchanged
universal projection gives divisibility of the ENTIRE product

    P*(X-2^R)*(2^R X+1)

byH. The inherited strict whole-product height bound makes it zero,
soX=2^R. No unverified unit is cancelled modulo a compositeH. This
makesKpos/H integral. On the direct chart only now does the residual
carrier numerator moduloq implyq divides X. FromX=2^R andR>3q follow
q^4 divides X and positivew=X/q. The remaining fractions giveq³ divides
Y and(q-1) dividesBt. Fixed-minus parity, exact half-binomial rounding
and fresh UNscaled source61 witnesses then follow exactly as in the
accepted zero-offset proof. The reconstructed source parameter is
Y(X+1)+2, not the new scaledA. Its whole native calibration yields a
finite syntactic refutation.

## 5. Complete positive converse with a fresh strong period

From a refutation take canonical outer/first/main source data, including
E=tau²,c=psi_A(R),R=3 modulo4,R>3q, integerst>=0,rho>=0,s>0,kappa>0.
Choose the strong pair afresh: the determinant-one Pell matrix atA has
finite order moduloN0=c²*tau. At a positive multiple of that period,
I=psi_A(m)>0,f=chi_A(m)>0 andN0 divides I. Puti=I/(c²*tau)>0.
Then the literalU=I/tau, soDf=f²,Q=(Delta I)² exactly. This is a single
Pell period with prescribed divisibility, not simultaneous unrelated
Pell equations.

Source61 auxcomplete requires onlyA>=2,R>=3,R=3 modulo4,c=psi_A(R),
positivef,I withf²-Delta I²=1 andc divides I. It does not constrain the
chosen strong index or the parity ofI/c². Its explicit fresh witness is

    S=Delta I, Q=S², R=2v+1,
    V*=chi_S(R)/S=Q_v(S²), y=psi_S(R),
    T*=(V*+c+R f²)/(c f²).

Odd-index identities modulof² andc proveT* integral, withgcd(c,f²)=1.
Canonicalv>=2 andQ_v's recurrence giveV*>=(4Q-3)^v>=9Q².
Sincec<S,f²<Q,alpha<q<S, this givesT*>V*/S³>=9S>alpha.
Thus the actual inputT=T*-alpha is positive andV=V*.
Moreoveru=y-V*>V*/(4Q)>=9S²/4>4I².

NowUE=I*tau<I² becauseU>1, kappa<c<I, ands<Y<c<I. The positive
integer

    n=(g-Cg)+(y-V*)-kappa-s+Wt+rho

has total negative loss less than2UE+kappa+s<2I²+2I<4I²,
strictly belowu. Hence n>0 andZ/M=g+y, making one exact norm factor
zero. This constructs a complete positive ordinary zero for either center.
For direct choosex=X-q>0 and

    n_direct=n_ordinary+(W_direct-W_ordinary)t+X/q^4>0.

All kernels and centers agree, B=qBt, M_direct=qM_ordinary and
Z_direct=qZ_ordinary. The two-root norm scales byq^4 and vanishes.

## 6. Exact global degrees and complete leading forms

The source gate censuses are92,93,98,99; all inputs/ports/gates are live.
The exact degrees283,278,258,254 follow from the actual bound interfaces
and formal Laurent roots, as detailed in source/saturated_degree_proof.tex.
This formal-field argument concerns every input, not positive solution
values, and is independent of which signs are positive real roots.
ForZnorm=Z/M one hasZnorm=V+Cg+remainder with remainder degree<=4.
Choose formalg nearAUE andy nearV. The exact identities

    (AUE-g)(AUE+g)=U²E²-E,
    (y-V)(y+V)=(V²-1)/delta

give degrees(C0-g,C1-g,y-V)=(18,23,-6) ordinary and(17,21,-4) direct.
The exact four-factor norm isdelta² M^4 product(Znorm+sigma*y+rho*g).
The two large factors have leading2V, the next2g, and the lastUE
(upper) orUE/(2A)(sharp). Their full products are nonzero and give

    ordinary upper: 2^11 q0^149 w^29 Y^61 i^10 k0^32(q0-F)²,
    ordinary sharp: 2^10 q0^146 w^28 Y^60 i^10 k0^32(q0-F)²,
    direct upper: 2^11 q0^124 X0^29 Y^61 i^10 k0^32(q0-F)²,
    direct sharp: 2^10 q0^122 X0^28 Y^60 i^10 k0^32(q0-F)²,

whereq0=beta J,k0=eta+zeta,X0=q0+x on the direct chart. SelectingF²,
eta to the fullk0 exponent andx to the fullX0 exponent yields nonzero
coefficients2^11 beta^149,2^10 beta^146,2^11 beta^124,2^10 beta^122.
The independent checker binds actual homogeneous front components and
these entire leading polynomials. Exact univariate rays are additional
literal lower-bound controls, not the global degree proof.

## 7. Uniform arithmetic and WHOLE native composition

Sections1--5 are uniform in four freely named fixed ports satisfying the
stated box, plus a complete normalized native/source calibration for the
SAME tuple. Every use ofK0,MC,MF has been explicitly bound over the free
polynomial ring. The proof reconstructs fresh unscaled source witnesses
for soundness and uses the calibrated canonical family for completeness.
It never invokes a theorem about one K-specific polynomial by asserting
that its numerical K stayed equal.

For the exported four graphs, ALL four coefficient gzip files are exactly
those of sealed one-page-short10. Its complete BFS_SOURCE_TRANSFER theorem
supplies all430 state conjugacies,943 typed-color conjugacies, native
support/carry/copy interfaces and DC-dependent controller units46,4050,31053.
Its uniform native/controller proof provides precisely the cofinal canonical
rank and odd/square-scale promises needed above. This is a whole coherent
BFS tuple instance, not a splice of original and BFS ports. MF already
contains its source shift bybeta exactly once.

A second, separately pinned instance is the directly indexed BFS tuple of
research/indexed-tile-enumeration. Its ordinary proof rebuilds the entire
native tuple under a selector permutation fixingStart0/Forbidden1 and
rebuilds fresh native words and actual-rank controller; its NEW unit
residues23,3359,404489 give the same complete source interface. Applying
this packet's uniform arithmetic theorem to that whole regenerated tuple
is therefore licensed. No old/native-word map, equality of old/new
specialized polynomials or arbitrary one-port substitution is used. The
same actual free-port graph and beta-only nonzero leading coefficient
then give each of the four exact degrees at that new whole specialization.
The alternate binding is retained explicitly; the four primary exports
remain at the incoming complete old BFS binding.

Composing either WHOLE calibrated instance with the arithmetic theorem
proves positive-zero existence iff finite syntactic ZFC refutation in the
inherited calculus. Negation yields the ordinary arithmetizable consistency
equivalence. Finite programs verify its concrete premises and literal
identities; they do not replace this unbounded proof or create a Lean or
encoded internal-ZFC derivation. Canonical page changes belong to a
separate reviewed rendering task.
