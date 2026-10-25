# Denominator engineering with partial normalization

## Results and exact scope

Six explicit integer polynomials have ten independently strictly positive integer unknowns. Their live binary-operation counts and exact total degrees are:

| Carrier and normalization | Squared weight V² | Product weight bV |
|---|---:|---:|
| Y=q³s, D=XY | 77 / 626 | 78 / 464 |
| Y=q³s, D=q⁴ | 78 / 622 | 79 / 460 |
| Y=q²s, D=q³Y | 79 / 518 | 80 / 384 |

The finite coefficient tuple is the entire indexed BFS943 tuple of the retained native/refutation calibration, not arbitrary ports satisfying only numerical bounds. The four complete integer payloads, finite reconstruction recipe, and ordinary source proofs are supplied. Their largest port has 592,884 bits. All other named expressions below are polynomial abbreviations, not quantified variables.

This is ordinary mathematics formalizable in ZFC, composed with named inherited calibration: each polynomial has a positive zero exactly when the inherited syntactic calculus has a finite ZFC refutation. Equivalently ZFC proves that absence of a positive zero is equivalent to Con(ZFC). No consistency proof, no unsolvability assertion, no new end-to-end proof-assistant certificate, and no global optimality claim is made.

Credit: `provenance/staged_denominator.md` already removed the artificial scale using D=Y² and recovered an index from a known divisor before recovering all of D. `provenance/unshift.md` and `unshift_general.md` supply the sign-free auxiliary shift removal and exclusion of both signed third auxiliary branches. Product-square extraction, Pell doubling, and q-cube normalization are inherited. The new claims are the cheaper-degree D=XY and D=q⁴ choices, and partial normalization Y=q²s with D=q³Y. The latter gives a lower-degree tradeoff at 80/384, with the same ten-positive domain and whole tuple.

## 1. Complete family

The independent coordinates are J,F,alpha,i,T,w,s,n,eta,zeta > 0. Fixed ports beta,K0,MC,MF obey beta odd, beta>=31, K0>0, and 0<MC<beta<MF<2beta. Set

    q=beta J+1, h=q-1, C=q-F-alpha, X=wq,
    k=eta+zeta, c=kY+eta, A=Y(X+1)+1,
    Delta=A²-1, H=4A-5, v=XY²,
    E=1+v(v+1)k²,
    R=[h(q-F)+alpha](q²-1)+(MC+q MF)J,
    e=k-R-1, B=(K0+w)C-F,
    U=ic², a=Delta U²E, F0=1+a, G=EF0,
    Fsq=1+4aF0, Q=Delta(Fsq-1),
    b=cT-R, V=Fsq b-c, K=X(3c-2X)+2.

Choose one of (Y,D)=(q³s,XY), (q³s,q⁴), (q²s,q³Y). Choose L=V² or L=bV. Define M=hDH. In the first two charts define

    Z=hD[H(n-LB)+K]-H[DB+he].                         (1)

In the partial chart define instead

    Z=hD[H(n-LB)+K]+H[h(Y²-e)-DB].                (2)

The complete polynomial is

    P=Q(Z²-M²GV²)+(M²G-Z²).                          (3)

It is equivalently (Q-1)Z²-M²G(QV²-1). For proof only put z=Z/M, kappa=K/H, rho=e/D, t=B/h, W=1+hL, and sigma=0 in the cubic charts, sigma=s/q in the partial chart. The exact rational carrier identity is

    z=n+kappa+sigma-Wt-rho.                           (4)

No divisibility is presumed in (4). In the cubic charts the positive integral quotient Y/q³ has been absorbed in n; the partial chart retains that quotient as a possibly nonintegral fraction.

## 2. Roots and main folding before signs

Every positive assignment has q>=32, X>=q, Y>=q, k>=2, c>k, A>4, Delta>=3, U>=c² and E>1. In particular a>c and Q>c². The exact identities

    Fsq=(1+2a)², Q=4 Delta² U² G, gcd(E,F0)=1           (5)

are independent of D, normalization, and T's sign shift. For any integral b, V is nonzero: b=0 gives V=-c, and otherwise |V|>=Fsq-c>1. Thus QV²-1>0 and M>0.

At P=0, (Q-1)z²=G(QV²-1). Because G divides Q, both other integer factors are -1 modulo G. Prime valuations show G=g² for a positive integer g, even though z is only rational and M need not be coprime to G. Coprimality in (5) gives E=tau² and F0=f0², g=tau f0. Now y=|z|/g is a positive rational satisfying

    QV²-(Q-1)y²=1.                                   (6)

The retained rational adjacent-Pell descent makes y integral. Explicitly, if y=r/m in lowest terms, m² divides Q-1. For |V|=v1>1 one has v1<y<Qv1/(Q-1). The norm-preserving map

    v2=(2Q-1)v1-2(Q-1)y,
    y2=(2Q-1)y-2Qv1

has nonzero integral v2 with |v2|<v1 and preserves the reduced denominator m of y2. Iteration after sign reflection reaches v1=1,y=1, so m=1. Thus z=epsilon gy is integral, with epsilon=+1 or -1.

The positive integers f=1+2a and I=2Ug satisfy

    f²=Fsq, f²-Delta I²=1, c²|I, Q=(Delta I)².          (7)

The signed all-index folding theorem in the retained `universal_pell.tex` applies to (6),(7), c<=I and V=-c modulo f, without assuming V positive. It gives c=psi_A(p), p odd and positive. The first norm gives k=2psi_(2v+1)(n0), n0>=1. If n0=1, k=2 and c=2Y+1 lies strictly between psi_A(1)=1 and psi_A(2)=2A, impossible. Hence

    k>=8XY²+4, c>kY>8XY³>=8q⁴.                       (8)

In particular c>X and K,kappa>0. None of these conclusions requires C>0, R>0 or a sign for b.

## 3. Unshifted transport, including the smaller weight

First b cannot vanish: otherwise (6) gives y²=c²+(c²-1)/(Q-1), strictly between consecutive integers. Thus sign(V)=sign(b) and |V|>|b|. Also

    a²-g²=E[Delta U²E(Delta U²-1)-1]>0,
    Fsq-c>3a>3g, y<(3/2)|V|.

Therefore gy<V²/2, enough for the squared weight.

For bV we must exclude main index p=3 with only Y>=q, not an artificial scale. Suppose c=4A²-1. If n0>=3 then kY>32X²Y⁵, while A<2XY (because X>=32,Y>=32) gives c<16X²Y², impossible. Thus n0=2 and k=8XY²+4. Put u=X+2-2Y. Expanding c=kY+eta gives

    eta=4Y²(Xu+1)+8Y(X+1)+3-4Y.                       (9)

If u<=-1, then

    eta<=-4Y²(X-1)+8Y(X+1)+3-4Y<0,

since Y(X-1)>2(X+1), valid for X,Y>=32. If u>=2, subtracting k from (9) gives eta-k>=4Y²+8Y(X+1)-4Y-1>0. Both contradict 0<eta<k. Thus u is 0 or 1, so 2Y-X is 2 or 1. But q divides both X,Y and q>=32. Contradiction. Consequently p>=5 and c>c3=4Delta+3.

Put S=Delta I; Q=S². Pell classification of (6) gives |V|=chi_S(j)/S for odd j. Even traces are +/-1 modulo S and cannot be divisible by S. The first odd index gives |V|=1, already excluded. At j=3, |V|=4Q-3, and respectively

    V= 4Q-3 => Fsq(b-4Delta)=c-c3,
    V=-4Q+3 => Fsq(b+4Delta)=c+c3.

But 0<c-c3<c+c3<2c<Fsq, so neither right side is a multiple of Fsq. Therefore j>=5 and |V|>=16Q²-20Q+5>8Q². Since Q>Fsq and Fsq>2c,

    |b|>(8Q²-c)/Fsq>8Fsq-1/2>4Fsq>4g.

So L=bV=|b||V|>0 and gy<3L/8<L/2. This argument handles both signs before any decoded source premise.

For either weight, e<b because b-e=cT-k+1>0. Thus rho<|b|/D. Every D in the family exceeds 2. If B<=-1 then Wt<-L and (4), with n>0, kappa>0, sigma>=0, implies

    n=epsilon gy-kappa-sigma+Wt+rho
      < L/2-L+|b|/D < 0.

For L=V² use |b|<|V| and |V|>1; for L=bV use |V|>1 and D>2. Contradiction. Thus B>=0, hence C>0. Only now invoke the outer mask estimate 3q<R<q⁴-2. By (8), c>2R, and b=cT-R>0, V>0. The normalized rank and signed auxiliary-index interfaces apply with c²|I, c>2R,c>2p and fixed-minus residues. They give p=R. Odd R then gives q even and J odd by the retained mask parity theorem. No bound containing an uncontrolled alpha was used before C>0.

## 4. Known divisors recover the first index

The recurrence at P0=2XY²+1 gives

    k=2n0 modulo 4XY².                               (10)

Also P0>A, because P0-A=Y(2XY-X-1)>0. If n0>=R, monotonicity in the Pell base and index gives k/2>=psi_A(R)=c, impossible. Thus 1<=n0<R.

In the cubic charts, integral z and (4) give D|hHe. For D=XY or q⁴, q⁴ divides D, while gcd(q,hH)=1 because h=q-1 and H=4Y(X+1)-1=-1 modulo q. Hence q⁴|e.

In the partial chart multiply (4) only by qhH. Its other fractions clear, giving D=q³Y | qhHe. Since q⁵ divides D and gcd(q,hH)=1, again q⁴|e. In all charts q⁴ divides 4XY²; indeed q⁷ divides XY² in the cubic charts and q⁵ divides XY² in the partial chart. Therefore (10) implies q⁴|(2n0-R-1). But 1<=n0<R gives

    |2n0-R-1|<R<q⁴.

Thus 2n0=R+1. Returning to the full recurrence (10) now gives 4XY²|e. Each chosen D divides 4XY²: trivially for XY; q⁴ divides XY² in the cubic chart; and for D=q³Y in the partial chart the quotient is 4w s. Hence rho=e/D is integral. Neither coprimality of Y and h nor cancellation of an arbitrary nonunit was used.

## 5. Whole-product projection and remaining fractions

Put R=2r+1, so r>=48. The retained uniform ratio lemma at scale one applies to A=Y(X+1)+1 and P0=2XY²+1. It gives

    xi < psi_A(2r+1)/psi_P0(r+1)
       < xi(1+1/[Y(X+1)])^(2r),
    xi=(X+1)^(2r)/X^r.

Together with Y<c/k<Y+1 this implies Y>X^r/3 and X^(r+1)<3Y(X+1)<H. With rho integral, (4) implies H|hK in the cubic charts. In the partial chart clear qh to obtain H|qhK. In both cases this implies the weaker inherited premise H|q³hK.

The universal projection identity (with H odd) gives H|q³h(X-2^R)(2^R X+1). The retained whole-product bound for X>=q>=32 and r>=48 bounds the absolute value of that entire product by X^(r+1)<H. Hence it is zero, so X=2^R. This uses the entire product, not illicit cancellation of its separate factors. Now kappa=K/H is integral.

In the cubic charts (4) gives Wt integral. Since W=1 modulo h, h|B. In the partial chart it gives sigma-Wt integral, or s/q-WB/h integral. Since gcd(q,h)=1, q|s and h|WB, hence h|B. Therefore in all charts t=B/h is a nonnegative integer and q³|Y. The retained fixed-minus parity theorem gives R=3 modulo 4. The same ratio and half-binomial rounding theorem, now with the restored native fractions, identifies the required half-binomial Y. The fresh source reconstruction at A_source=Y(X+1)+2 and the whole indexed native calibration give a finite syntactic ZFC refutation. A_source is not identified with our auxiliary base A.

## 6. Positive completeness

A finite refutation supplies the retained canonical outer data X=2^R, R=3 modulo 4, R>3q, q³|Y and t=B/h>=0 integral, with the half-binomial Y. In a cubic chart take s=Y/q³; in the partial chart take s=Y/q². Both are positive integers. Form A,P0 at scale one and set

    c=psi_A(R), k=2psi_P0((R+1)/2), tau=chi_P0((R+1)/2),
    eta=c-kY, zeta=k-eta.

The retained scale-one ratio/rounding theorem gives 0<eta<k. The exact recurrence gives 4XY²|e, so every selected rho=e/D is a nonnegative integer. Universal projection gives integral positive kappa<Xc.

Choose a positive multiple of a matrix period at A modulo c²tau, with seed pair (f0,I0), c²tau|I0. Set i=I0/(c²tau)>0. Then a=Delta I0²=f0²-1, F0=f0², G=(tau f0)², and the doubled pair is exactly f=2f0²-1,I=2f0 I0. The inherited auxiliary-completeness theorem supplies positive V,y and a positive integer

    T=(V+c+Rf²)/(cf²).

No subtraction of alpha is made; the actual canonical R>3q is retained. The literal b,V definitions and (6) hold. For either positive L define

    n=gy+Wt+rho-kappa-sigma.

In cubic charts sigma=0; in the partial chart sigma=Y/q³ is integral because canonical q³|Y. Also sigma<Y<Xc and kappa<Xc. Since I0>=c² and f0>(A-1)I0>2Xc, we have g=tau f0>kappa+sigma. Thus n is a strictly positive integer. Its carrier is z=gy, so (3) vanishes. This constructs every independent coordinate positively. It is a fresh canonical witness construction, not an unproved positive inverse shear between arbitrary tuples.

## 7. Exact operation counts and degrees

The literal source circuits are the canonical mathematical artifacts. Every binary product, addition and subtraction, including scalar products and squares, is charged. All ten inputs, four ports and all gates are live. `build.py` transforms frozen data only; `verify.py` checks independent algebraic cuts covering every row, whole leading homogeneous forms, fixed bytes, and deliberate corruptions.

Compared with the incoming 78/630 and 79/468 circuits, D=XY keeps the two-gate pair (D,V0)=(XY,DY) in place of (Y²,XY²), while unshift removes one addition. D=q⁴ adds one square q²*q². For the partial chart, Y=q²s changes one operand; D=q³Y adds one multiplication, and h(Y²-e)-DB uses one more operation than DB+he. Unshift saves one, for net plus one: 79/518 and 80/384.

Cubic common degrees are Q124,G78,V118,b6; M has degree13 for D=XY and11 for D=q⁴. For the partial chart Y3,c4,A5,Delta10,E18,U9,a46,Fsq92,Q102,G64,b5,V97,D6,M12. For the squared weight the uniquely dominant term is QZ², and for the product weight it is -QM²GV². Hence the exact degrees in the table follow once the displayed leading factors are nonzero; the checker proves this with complete sparse leading forms, not a sampled ray. Write q0=beta J,k0=eta+zeta,C0=q0-F-alpha. Cubic complete highest forms are:

    XY,V²: 2^14 q0^378 w^48 s^110 i^20 k0^64 T^4 C0²,
    q⁴,V²: 2^14 q0^378 w^46 s^108 i^20 k0^64 T^4 C0²,
    XY,bV: -2^10 q0^284 w^36 s^82 i^14 k0^46 T²,
    q⁴,bV: -2^10 q0^284 w^34 s^80 i^14 k0^46 T².

The partial-chart highest forms are

    partial,V²: 2^14 q0^272 w^46 s^110 i^20 k0^64 T^4 C0²,
    partial,bV: -2^10 q0^206 w^34 s^82 i^14 k0^46 T².

They are also supplied and verified in the finite checker and report section. These nonzero forms establish global degrees at the actual positive beta, not merely formal-port upper bounds.

The 79/518 squared partial point and the 78/622 q⁴ squared point are dominated by the 78/464 product point and are retained only as uniform-family controls. The other operation/degree points are local tradeoffs, not claims of a literature-wide minimum.

## 8. Boundary and rejected exploration

Finite audits establish literal algebra and artifacts, not the unbounded Pell/source theorems by testing finitely many zeros. Those theorems are identified in provenance. A tempting Y=qs,D=q⁶ chart at 81/410 or82/304 was rejected during this iteration: its recurrence modulus 4XY² is only visibly divisible by q³, so the q⁴ index argument fails. No such circuit is delivered or claimed. The accepted partial chart Y=q²s repairs exactly this issue.
