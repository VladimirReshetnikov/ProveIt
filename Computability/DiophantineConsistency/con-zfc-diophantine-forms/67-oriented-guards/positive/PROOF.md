# One free scale and an index absorber: fourteen positive unknowns

## Result and scope

The supplied polynomial has fourteen strictly positive unknowns, exact total degree30, and87 live binary operations (47 multiplications,24 additions,16 subtractions). The equivalent five-equation system has residual degrees12,14,10,15,2 and78 shared arithmetic operations. This is a lower-degree/higher-cost tradeoff against the incoming fourteen-positive degree52/79 point, not domination. Compared with the integral-root fifteen-positive degree30/79 point, it saves one variable at the same degree and costs eight more operations. Compared with its degree24/90 point, it saves one variable and three operations at a higher degree. No global minimum is asserted.

The new construction composes two identified ingredients: the incoming Integral Root packet's monic-root carrier for q³|Y, and a strengthened adaptive U=4qY version of the earlier fourteen-variable index absorber for the deleted index quotient. The second scale is deliberately NOT freed: X=wq is retained. Simply placing both fractional offsets in one merged root does not recover each divisibility condition separately.

The whole fixed tuple is the Integral Root packet's source39/44 compact tuple with beta=2^590069−1, K0=K, MC, and MF=MF_source already shifted. Its four actual payloads and binding are copied unchanged. The ordinary native compiler/K215 refutation calibration, canonical ordinary-strong completeness, and Pell-rank/index results remain named inherited inputs, not conclusions of finite testing. The mathematical composition proves in ZFC that this equation has a positive zero iff there is a finite syntactic ZFC refutation. Negation is the requested equivalence to Con(ZFC); neither consistency nor inconsistency is proved. No new end-to-end kernel certificate is asserted.

## 1. Literal equation

Supply exactly

    J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,gamma > 0.

All other symbols are computed polynomial abbreviations:

    q=beta J+1, C=q−F−alpha, X=wq, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H=(a+2)²−1, ell=EkY,
    A=ell(ell+k)+1, G=Delta c²+1, b0=X+ac,
    R=((q−1)(q−F)+alpha)(q²−1)+(MC+q MF)J,
    U=4qY, v=k−R−1,
    Dstar=U b0+H(U gamma−v),
    Q=Delta(f²−1), I=i c²,
    V=f²(cT−R)−c,
    Nt=(K0+w)C+q−F−z(q−1).

The five residuals are

    A0=[q³(ell+r)+Y]²−q⁶A,
    A1=Dstar²−U²G,
    As=I²−Q,
    Aa=(V+u)²−Q u(2V+u)−1,
    At=Nt−1.

The single equation is

    P14=A0²+A1²+As²+Aa²+At²=0.

Every exponent is fixed and nonnegative. There is no division, root, bit operation or implicit existential in the actual polynomial. The JSON circuit is authoritative and uses all fourteen unknowns and four coefficient ports.

## 2. Soundness: recover scales before using the absorber

An integer zero of P14 makes each residual zero. Since q>0, A0=0 says that

    tau=ell+r+Y/q³

is a rational square root of the integer A. Therefore tau is an integer and q³ divides Y. Set s=Y/q³>0. This recovers the exact old scale Y=sq³ and a positive first Pell root tau=ell+r+s. Also X=wq was already defined. Thus none of the older scale-dependent inequalities is used prematurely.

At=0 gives the authentic transport equation Nt=1. The inherited whole-tuple interface gives q>=16, C>0, 3q<R<q⁴−2, E=XY>=q⁴>R+2. The first Pell equation is tau²−ell(ell+k)=1. With P0=2XY²+1, it supplies a positive index n with

    tau=chi_P0(n), k=2psi_P0(n).

The main residual yields g=Dstar/U, a rational square root of G, hence an integer. It is positive, since H<5a, b0>akY, and

    Dstar > U b0−Hk > ak(UY−5)>0.

Thus g=chi_(a+2)(p), c=psi_(a+2)(p) for a positive index p. Reduction modulo U gives U|H(k−R−1). No cancellation of H is made.

The adaptive modulus is U=4qY, not the inherited 4q⁴. Since Y=sq³, U>=4q⁴ and U divides4XY². Its crucial gcd bound remains gcd(U,H)<=3. Indeed H=4Y(X+1)+3 and gcd(Y,H) divides3. Every prime dividingq also dividesY, so only3 can divide gcd(qY,H). If3 dividesq, then27 dividesY and H=3 modulo27, giving valuation exactly1. If3 does not divideq, gcd(qY,H)=gcd(Y,H) divides3. Thus no unbounded factor is cancelled. The inherited absorber's remaining proof uses only these three properties, and applies unchanged. The first Pell recurrence gives k=2n modulo4XY², a multiple of U. Consequently, for mu=U/gcd(U,H),

    mu=U/gcd(U,H)>=4q⁴/3>R+1,  2n=R+1 modulo mu,
    n>=(R+1)/2>=25.

The main/first Pell comparison gives p>n. Hence p>=26 and c>(a+2)Delta², c>2p and c>2R. These are obtained before applying the ordinary strong-rank result; the absent index quotient is not assumed.

## 3. Strong and auxiliary reconstruction

As=0 is the ordinary-strong equation (i c²)²=Delta(f²−1), not the normalized strong equation. The inherited rank lemma applies with the strict bound just proved and yields a positive main Pell index m for f, with p|m, c|m, c²|(f²−1), and m>=c>2p.

Aa=0 is

    QV²−(Q−1)y²=1, y=V+u,

because (V+u)²−Q u(2V+u)=QV²−(Q−1)(V+u)². Although u>0, V is not assumed positive. In fact V=0 would make the displayed equation impossible since Q=I²>1. The equation gives y²=V²+(V²−1)/(Q−1)>=V². If V<0 and y<0, u=y−V>0 would imply |y|<|V|, a contradiction; y=0 is likewise impossible. Thus y>0.

Set T_old=fT>0. Then V=c(T_old f−1)−Rf² is exactly the inherited ordinary auxiliary expression. Its signed-index argument, with the already established rank hypotheses, gives p=R. The continued absorber proof then shows n<R; since 2n=R+1 modulo mu and |2n−R−1|<mu, it gives2n=R+1.

The first Pell recurrence now gives v=k−R−1=k−2n divisible by E and U. Its positive quotient h=v/E and gamma_old=gamma−v/U are exactly the witnesses reconstructed in the retained absorber proof, including gamma_old>0. The transformed main equation becomes g=X+ac+gamma_old H. Therefore all ordinary compiler equations hold with positive witnesses (J,F,alpha,z,f,h,i,T_old,s,w,tau,eta,zeta,y,gamma_old). The inherited compiler yields a finite ZFC refutation.

The strict positivity of h and gamma_old is not inferred merely from divisibility; it uses the retained absorber's final positive-gap estimate. The first root carrier only supplied a smaller subclass of its admissible positive tau witnesses and changes none of that argument.

## 4. Completeness and positive new coordinates

A finite refutation supplies canonical normalized compiler witnesses for the whole compact tuple. Convert its strong ordinate to ordinary form, i=Delta i0, exactly as in the retained ordinary completeness proof. The compact adapter supplies R=3 modulo4 and its required canonical Pell indices.

Apply the absorber's positive shift

    gamma=gamma_old+(k−R−1)/U>0.

The numerator is divisible by U from k−R−1=2(psi_P0(n)−n), n=(R+1)/2, and the recurrence modulo4XY². Supply the old Y=sq³ directly. The Integral Root positive-gap lemma proves tau>ell+s for these canonical witnesses (n>=3); hence r=tau−ell−s>0. Then A0=A1=0.

Choose the canonical auxiliary witnesses from the squared-modulus construction: the positive quotient T_old is divisible by f, so T=T_old/f>0, and y>V. Supply u=y−V>0. The complete proof of this existential witness replacement is copied as SQUARED_MODULUS_PROOF.md; it uses R=3 modulo4 and is not a claim that every older witness has this congruence. As=Aa=At=0 follows. Thus P14 has a positive zero.

## 5. Exact degree, with cancellation

Let q0=beta J, X0=wq0, E0=X0Y, c0=(eta+zeta)Y, H0=4E0, U0=4q0Y, and R0=q0³(q0−F). Their degrees are1,2,3,2,3,2,4.

Writing Z=UX+H(U gamma−v) gives the exact main identity

    A1=2UacZ+Z²−U²(Hc²+1).

Z has degree7: here the term −Hv has leading part H0R0, larger than H0U0gamma. Consequently A1 has degree14, with leading term

    H0R0(2U0 E0 c0+H0R0).

Both the cross term and Z² have degree14; neither is omitted.

The first residual has degree at most12 by

    A0=q⁶[r²+ell(2r−k)−1]+2q³(ell+r)Y+Y².

The strong and transport residual degrees are10 and2. The auxiliary residual has degree15: Q has leading form E0²f² and V has leading form −R0f². Its unique degree15 term is

    2E0²R0 f⁴u.

Therefore the polynomial has exact total degree30, with nonzero leading form

    4 w⁴(beta J)^10 Y⁴(beta J−F)² f⁸u².

The leading form is nonzero for the fixed positive beta. The separate certificate circuit implements the two displayed cancellation identities; it is not the87-operation primary evaluator.

## 6. Validation boundaries

The supplied check authenticates source pins and the whole coefficient payloads, verifies the exact universal cancellation and norm identities using sparse integer arithmetic, recomputes live operation counts, independently evaluates the literal formula, compares primary/certificate values, and checks degree30 over three prime fields using the actual coefficient bytes. Finite examples supplement but do not replace the universal scale, sign, index, compiler or completeness proofs above. The resulting ZFC equivalence is an ordinary mathematical composition with explicit inherited dependencies, not a freshly compiled proof-assistant endpoint.
