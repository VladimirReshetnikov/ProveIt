# A 24-, 25-, and 26-integer synthesis

## Status, scope, and exact statements

This is a new ordinary mathematical reduction, formalizable in ZFC, from the authenticated blank-machine Pell interface. It is not a new Lean/Rocq proof, a proof of Con(ZFC), or a global minimality claim. For a single coherent authentic coefficient quartet, the displayed equations have integer solutions exactly when the calibrated blank K215 refutation machine halts. Therefore ZFC proves that their lack of integer solutions is equivalent to Con(ZFC).

The six guarded source ports are J,F,alpha,z,eta,zeta. Replace each with its own disjoint positive surjection

    Pos(a,b,c)=1+a²+b²+c(c+1).

Set i=2r+1, s=2v+1, w=u². These substitutions use 21 unrestricted integers and 47 binary gates. The three constructions retain, respectively:

- 24 integers: h,T,t.
- 25 integers: h,T,t,gamma.
- 26 integers: h,T,t,gamma,f.

Every retained coordinate is unrestricted. The selected source quartet must always be complete; MF means the shifted high-mask port. The original package-06 quartet is a safe direct binding for the proofs below. The compact Wang943 quartet from the previous round is also admissible through its whole-tuple compiler transfer and the native mask population identity used by the odd-scale theorem. No mixing of coefficient ports is permitted. The new catalogue's T4 choices require their own complete audited binding, not just replacement of beta.

Exact literal circuits and verified ledgers:

| Construction | Integer unknowns | Degree | Binary gates | Multiplications | Add/subtract |
|---|---:|---:|---:|---:|---:|
| Sharpened pair norm (Section8) | 24 | 2240 | 165 | 96 | 69 |
| Threefold-separator comparison | 24 | 2256 | 165 | 96 | 69 |
| Small-weight norm | 25 | 920 | 131 | 70 | 61 |
| Ordinary two-root merger | 26 | 214 | 123 | 63 | 60 |
| Normalized two-root alternative | 26 | 236 | 123 | 64 | 59 |

All gates and all input ports are live. Comparisons are not arithmetic gates. Every abbreviation is expanded by the JSON straight-line circuits, which use only integer constants and binary +,-,*.

## 1. Common polynomials and signed pre-bootstrap

Define

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H=(a+2)²-1, P0=X+ac,
    ell=E kY=XkY², A=1+ell(ell+k), G=1+Delta c²,
    R=((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)C+q-F-z(q-1).

The authentic fixed coefficients satisfy beta>=15 and K0>=2 and the source mask bounds. If Nt is a unit, C<=-1 is impossible, since

    Nt=(K0+w)C+1-F-(z-1)(q-1)<=-2.

Thus C>=0. The authentic weak transport/mask bootstrap gives

    q>=16, q(q²-1)<R<q⁴-2.

These deductions require neither X>0 nor s>0. Since s is odd, Z0=|Y|>=q³. Since X>=0, |a|=(X+1)Z0>=q³. The signs of a,c,H are the sign of Y. Both signs satisfy

    k(Z0-1)<|c|<k(Z0+1), |c|>2, |H|>1,
    Delta>=(q³-1)(q³-3)>q⁴>R.

Also ell>=0 and A>=1, with A=1 exactly when X=0. In particular Delta is positive even for negative s and is 0 or 3 modulo four.

For the normalized strong quantities let

    I=i c², S=Delta I, D=1+Delta I², Q=S², d=Q-1,
    vaux=cT, b=c+RD,
    e=Q(D vaux²+b²)-1, Baux=2Q vaux b.

The nonzero odd i and |c|>2 give Q>2, D>Delta+|c|, and

    b>D-|c|>1,
    Q-b=(Delta-R)D-Delta-c>D-Delta-|c|>0.

Thus 1<b<Q, for either sign of s and including w=0 and T=0. This early strict interval replaces positive-only bounds in the older arguments.

## 2. The 24-integer polynomial and optimized norm circuit

Put

    W=vaux²+D+2b, P=HW, K=P+1,
    uweight=3P, Z=Ht+K P0.

For temporary formal square roots tau²=A and g²=G define

    F(tau,g)=[d(Z-uweight tau-Kg)²-H²e]²-H⁴ Baux² D.

Let N be the product of F over the four formal signs of tau and g. No roots are supplied or existentially quantified in the actual equation:

    Nk Nt(1+N)-1=0.                                      (24)

Here is the lower-cost pair-ring evaluator. In the quadratic algebra with g²=G, let x=Z+Kg, x²=x0+x1 g, and set

    Cpair=d(x²+uweight² A)-H²e,
    Jpair=4d² uweight² A x²,
    Zterm=H⁴ Baux² D.

The inner norm over tau is the identity

    Fpair=(Cpair²-Jpair-Zterm)²-4 Jpair Zterm.

Write Fpair=F0+F1 g and output N=F0²-G F1². The circuit computes Zterm as 4H⁴ p z0, where p=QD vaux² and z0=Qb². Thus it never computes Baux as a separate intermediate. This is a polynomial identity, including all repeated-root and zero-Baux cases.

The odd coefficient F1 is even: x1=2ZK is even; every subsequent odd coefficient stays even under sums and products in this pair algebra. Hence N is a square modulo four. At a zero of (24), the three integer factors are units; 1+N cannot equal -1. Therefore N=0 and Nk=Nt=epsilon in {1,-1}.

### 2.1 Every actual conjugate of the auxiliary root is bounded

Since A>=1 and G>1, a vanishing norm factor supplies real tau,g. Set

    y=(Z-uweight tau-Kg)/H.

If Baux is nonzero, f=(e-dy²)/Baux satisfies f²=D and

    dy²=e-Baux f=Q(vaux f-b)²-1.

Every actual conjugate f' is ±sqrt(D). All actual conjugates y' are real, since they lie in the totally real field Q(tau,g). Therefore

    |y'|<sqrt(2)(|vaux|sqrt(D)+b)
          <2(|vaux|sqrt(D)+b)<=vaux²+D+2b=W.

If Baux=0, then vaux=0 because Q and b are nonzero. Directly dy²=Qb²-1, which gives the same strict bound |y'|<2b<W. This case makes no division by Baux.

### 2.2 The zero-w boundary is handled before separation

Write P=HW. Both signs of H are allowed. Since |P|>4,

    |K|>=|P|-1>3|P|/4, |K|<5|P|/4.

Also sqrt(G)>2, so |K|sqrt(G)>|P|=|H|W.

If w=0, then tau²=A=1, so tau is already rational. An automorphism changing g to -g in

    Z=uweight tau+Kg+Hy

would imply |K|sqrt(G)<=|H|W, a contradiction. Thus g is rational, hence an integer. Section 2.4 below proves y and gamma integral even here. Then the main equation g=P0+H gamma with X=0 reduces modulo H to 0=1, because g²-Delta c²=1 and Delta=a²+H. This contradicts |H|>1. Therefore w>0 and X>=q.

### 2.3 Separation when w>0, including negative H and P

With X>=16 and Z0>=4096,

    |a+2|<(9/8)XZ0, |c|<(9/8)kZ0.

Thus

    sqrt(G)<|a+2||c|<(81/64)ell<(3/2)sqrt(A),
    sqrt(A)>8.

Consequently

    |K|sqrt(G)+|H|W
       <(15/8)|P|sqrt(A)+|P|
       <2|P|sqrt(A)<3|P|sqrt(A)=|uweight|sqrt(A).

Any actual automorphism flipping tau would contradict this inequality after subtracting its image of the displayed linear equation. Hence tau is rational, therefore an integer. A subsequent g flip contradicts |K|sqrt(G)>|H|W, so g is likewise an integer.

This argument uses only actual automorphisms. It makes no generic field-degree or root-independence assumption and covers square radicands and coincident quadratic extensions. Negative H,P,K require no special field argument because all separations use their absolute values.

### 2.4 Rational auxiliary saturation and gamma integrality

Use the elementary saturation lemma:

    If m>=2 and V are integers and y is rational,
    m²V²-(m²-1)y²=1 implies y is an integer.

A full proof is inherited from round3/audit/RATIONAL_AUXILIARY_PELL_SATURATION.md and reproduced in upstream package21. In brief, write y=a/b reduced. Then b² divides m²-1; both m and m|V| are integral x-coordinates on the Pell equation with coefficient (m²-1)/b². For its fundamental-unit sequence, x_j divides x_l only when l is an odd multiple of j. The corresponding y-coordinate divisibility forces b|a and b=1. The divisibility statement follows by reducing l modulo 2j and reflecting into 0<=r<=j, where 0<x_r<x_j for r<j.

Once tau,g are integral, y is rational. If Baux is nonzero, f is rational with integer square D and hence integral, so V=vaux f-b is an integer and the lemma applies with m=|S|. If Baux=0, apply it directly with V=-b. In both cases y is integral.

Define gamma=(g-P0)/H. The linear identity gives

    t=3W tau+K gamma+y.

Thus K gamma is integral, and H gamma is integral by definition. Because gcd(K,H)=1, gamma is integral.

Now T=0 would imply vaux=Baux=0 and

    (Q-1)(y²-b²)=b²-1>0.

Integral y then has |y|>=b+1. But Q-1>=b by 1<b<Q, so the left side is at least b(2b+1)>b²-1, contradiction. Therefore T and Baux are nonzero and the recovered f is well defined.

We have restored all normalized source relations with signed h,T,f,tau,y,gamma, odd i, square w, six positive guarded ports, and nonzero odd s. The odd-scale theorem discussed in Section 5 excludes s<0 and supplies the authentic blank compiler.

## 3. The 25-integer small-weight reduction

Retain gamma and the main norm

    Nmain=(P0+H gamma)²-Delta c².

Use the same normalized strong and auxiliary definitions, but put

    M=I²+T²,
    Caux=d(t²+M²A)-e,
    U=Caux²+D Baux²-4d²t²M²A,
    N25=U²-D(2Caux Baux)².

The equation is

    Nmain Nk Nt(1+N25)-1=0.                           (25)

The main negative unit is excluded modulo four since Delta is 0 or 3 mod 4. Also N25 is a square modulo four. Thus Nmain=1, N25=0, and Nk=Nt are common units. The main equation excludes X=0 modulo H before any deleted root is restored.

### 3.1 Main Pell rank at both signs of s

Let Z0=|Y|, E0=XZ0, B0=|a+2|. The main Pell classification gives |c|=psi_B0(p), |P0+H gamma|=chi_B0(p), p>=1. Since |c|>1, p cannot be 1.

If p=2, c=2(a+2), for either sign of Y. For the positive main root chi_B0(2),

    chi_B0(2)-ac=H+4,

so X=4 modulo H. But 16<=X<|H|, impossible. For the negative main root,

    4(-chi_B0(2)-ac)=-(4(a+2)-5)(4(a+2)+1)-1,

so 4X=-1 modulo H. Since 0<4X+1<|H|, this is likewise impossible. Therefore p>=3 and

    |c|>=4B0²-1>4E0²-1.

Together with |c|<k(Z0+1), this yields k>(7/2)X²Z0. In particular

    ell=XkZ0²>(7/2)E0³, A>ell².

The proof does not assume s>0, h>=0, or the existence of the eliminated first root.

### 3.2 Signed small-weight domination

Let lambda=(16/15)^4. The elementary estimates B0<(16/15)E0, |c|<(16/15)kZ0, R+1<E0, D<B0²I², and |c|/I²<1 give

    D c²/I²<lambda A,
    b²/I⁴<(4lambda/49)A.

Because M²>=4I²T² and M²>=I⁴, including at T=0,

    (D vaux²+b²)/M²
       <lambda(1/4+4/49)A <(9/20)A.

Since Q>=10, d>=9Q/10. Consequently

    dAM²>2Q(D vaux²+b²),
    Caux>Q(D vaux²+b²)+1>|Baux|sqrt(D).

If t=0, N25=(Caux²-D Baux²)²>0, contradiction. Thus t is nonzero. If T=0, then Baux=0 and N25=0 gives a rational root tau=Caux/(2dtM) with tau²=A, so tau is an integer. Then y=t-M tau is integral and satisfies the impossible gap equation from Section 2.4. Hence T and Baux are nonzero.

Now define

    f=-U/(2Caux Baux),
    tau=(Caux+Baux f)/(2dtM),
    y=t-M tau.

The resultant first gives f²=D, then tau²=A. Both rational roots are integers, and y is integral. Expanding yields dy²=e-Baux f and therefore the exact source auxiliary relation. The signed odd-scale compiler then applies as before.

## 4. The 26-integer two-root equations

Retain gamma and f. Define

    Q0=Delta(f²-1), d0=Q0-1,
    V=c(Tf-1)-Rf², e0=Q0 V²-1,
    U0=d0(t²+A)-e0,
    N26=U0²-4d0²t²A.

For normalized strong use Ns=f²-Delta I²; for ordinary strong use Ns=1+I²-Q0. In either case the single equation is

    Nmain Nk Nt Ns(1+N26)-1=0.                         (26)

The main and normalized negative units are impossible modulo four. For ordinary strong, Ns=-1 would give I²-Delta(f²-1)=-2. If Delta=0 mod4 this is impossible; if Delta=3 mod4, checking square residues 0,1 also gives no residue 2. Thus Ns=1 for both versions. The norm guard is a square modulo four, so N26=0 and Nk=Nt are common units.

The main equation again excludes X=0 and supplies the rank p>=3 bound of Section 3.1. In the normalized version,

    Q0=Delta² i² c⁴>A,

directly from Delta>(X Z0)² and |c|>k(Z0-1), or from the stronger ordinary inequality below.

In the ordinary version Q0=I²=i²c⁴. By k>(7/2)X²Z0>4X and Z0>=4096,

    c²>k²(Z0-1)²>(k²Z0²)/2>2XkZ0²=2ell.

Also ell>k>=2, so

    A=1+ell²+ell k<4ell²<c⁴<=I²=Q0.

Thus 1<A<Q0 in both versions. If t=0, N26=0 forces d0 A=e0, or Q0(A-V²)=A-1. This contradicts 0<A-1<Q0. Therefore t is nonzero, and

    tau=U0/(2d0 t), y=t-tau

are rational with tau²=A, so tau and y are integers. Expanding gives d0 y²=e0. These exactly restore the first and auxiliary source norms. The ordinary or normalized signed odd-scale theorem applies. This proof handles the previously missing zero-t branch without demanding positive t or positive s.

## 5. Excluding negative s and canonical completeness

The needed source theorem is pinned package23/proofs/ODD_SCALE_27_PROOF.md. Its negative-s exclusion applies to both ordinary and normalized strong equations and to signed roots, h,T,gamma. The newly reconstructed equations meet all of those hypotheses.

For clarity, the exclusion does not merely assert that negative s is unnatural. With Z0=-Y, B0=(X+1)Z0-2 and c0=-c, first and main Pell classification, the signed auxiliary step-down congruences, and no-wrap bounds recover the main rank p=R and index R=2r0+1. The Pell growth ratio then gives Z0>2^R. The two possible main-root signs respectively imply X+2^R=0 modulo H or X2^R=1 modulo H. The strict inequalities

    0<X+2^R<|H|, 1<X2^R<XZ0<|H|

exclude both signs. Hence s>0. The same rank argument forces the common index/transport units to +1. The existing signed blank compiler now recovers the exact native tableau and calibrated refutation machine.

Conversely, a canonical accepting blank tableau has q=2^t, with t odd after the established powers-of-five padding; R is odd, so w=2^R/q is a square. The population identity of package23 gives popcount(R)=3t+2. The half-binomial identity gives v2(Y)=popcount(R)-2=3t, so s=Y/q³ is positive and odd. The canonical normalized strong multiplier i is odd, as in package14. No new divisibility condition on this multiplier is imposed.

For the ordinary 26-integer variant use i_ordinary=Delta i_normalized. Canonical Y is even, so a is even and Delta=a²+4a+3 is odd. Thus i_ordinary is still odd. All other canonical witnesses are unchanged.

Define the new free coordinate by

    t=3W tau+K gamma+y                  for (24),
    t=M tau+y                          for (25),
    t=tau+y                            for (26).

These integers make the respective norm vanish. All remaining source factors are one, all six positive ports have Pos representations, and both odd parameters and the square scale have the stated integer representations. This proves completeness without an extra Pell period, H-divisible multiplier, or positivity assumption on t.

## 6. Uniform exact degree proofs

Use weight two on J,F,alpha,z,eta,zeta,w; weight one on i,s,h,T,t,gamma,f. The substitutions have precisely these leading weights. Let q0=beta J and k0=eta+zeta. Key degrees are

    a,H:11; c:9; ell:20; A,G:40; Delta:22;
    R:8; Nk:12; Nt:4; I:19; D:60; Q,d:82; b,W:68.

For (24), K,uweight have degree79 and Z has degree99. The four leading linear forms Z-uweight tau-Kg are scalar multiples -3,+3,-1,+5 of K_top ell_top. The H²e term has degree240, below d times the linear square, of degree280; H⁴Baux²D has degree424, below the preceding square of degree560. Therefore

    N_top=45⁴ d_top⁸(K_top ell_top)^16, deg N=2240.

The product degree is 2240+12+4=2256. After the actual substitutions, the coefficient of

    J_a^1578 h r^48 eta_a^224 u^194 v^209 z_a²

is +2^305 3^8 5^4 beta^789. It is nonzero uniformly for beta>0, and the exponent sum is2256. Thus the result is not merely an upper bound or a sampled generic degree.

For (25), M has degree38, e has degree218, and d M² A has degree198. Thus the unique highest part of Caux is -Q_top b_top², U has degree436 with top Caux_top², and N25 has degree872 with top U_top². The competing subtracted term has degree816. The main norm degree is32, not its naive bound40: the cancellation leaves highest term 8 gamma a_top² c_top. Hence the product degree is872+32+12+4=920. The coefficient of

    J_a^640 h gamma r^24 eta_a^98 u^70 v^84 z_a²

is +2^111 beta^320.

For (26), Q0,d0 have degree24, V has degree11, e0 has degree46, and U0 has degree64, uniquely from d0 A. Thus N26 has exact degree128. The strong factor has degree60 normalized or38 ordinary. Adding the main,index,transport degrees32,12,4 gives236 normalized or214 ordinary. The corresponding coefficients are

    [J_a^160 h gamma f⁴ r² eta_a^18 u^26 v^22 z_a²] = -2^27 beta^80,
    [J_a^144 h gamma f⁴ r² eta_a^18 u^22 v^20 z_a²] = +2^25 beta^72.

All displayed monomials use one coordinate from each relevant positive-surjection triple. These explicit nonzero coefficients prove exact degree for every authentic beta>0.

## 7. Verification and limitations

`build_odd_scale_family.py` and `check_odd_scale_family.py` were newly written locally. Imported programs were not executed. Earlier emitted circuits were read as inert JSON. The checker independently evaluates the 24-variable norm by four-factor multiplication in a rank-four free algebra, not by replaying the optimized pair formula as its reference. Each circuit passed120 signed integer formula comparisons, all-port/all-gate liveness, two exact modular degree/leading-coefficient checks, and guard parity. The common signed bounds were checked on2160 finite cases, including w=0, T=0, negative s and both signs of i.

These finite checks support arithmetic identities and ledger accuracy; they do not replace the unbounded Pell classifications, rank step-down, population identity, compiler correctness, machine calibration, or rational saturation proofs. No actual accepting K215 computation is produced or asserted.

## 8. A sharper 24-integer separator: degree2240 at the same165 gates

The strict inequality already proved in Section 2.3 gives

    |K|sqrt(G)+|H|W<2|P|sqrt(A).

Therefore replacing uweight=3P by uweight=2P preserves every soundness argument, with t=2W tau+K gamma+y in completeness. The separately frozen circuit is `integer24_sharp_pair_norm165_degree2240.json`; the previous 3P circuit remains for comparison and provenance.

One leading formal branch now cancels, which genuinely lowers the exact degree rather than merely weakening an upper bound. This can be computed in the formal Laurent-series field obtained by scaling every actual integer input by a common indeterminate. Choose the square-root branches with leading terms ell and ac. These formal expansions satisfy

    sqrt(A)=ell+terms of weighted degree at most2,
    sqrt(G)=ac+terms of weighted degree at most9,
    ac-ell=kY²+eta E+eta Y.

The last expression has unique highest part k_top Y_top² of degree16. The exceptional branch is

    Ht+K(P0+sqrt(G))-2P sqrt(A)
      =K[ac+X+sqrt(G)-2sqrt(A)]+2sqrt(A)+Ht.

Its unique top is 2K_top k_top Y_top², of degree95. The other three linear branches have degree99 and respective leading multiples -2,2,4 of K_top ell_top. In every branch the d times linear-square term still strictly dominates H²e, and its square strictly dominates H⁴Baux²D. Multiplying the four branch leaders gives

    N_top=2^20 d_top^8 K_top^16 ell_top^12 k_top^4 Y_top^8,
    deg N=2224.

This formal expansion is only a device to compute the leading polynomial form; the norm itself remains a literal integer polynomial with no division or algebraic-number input.

The product has exact degree2224+12+4=2240. The coefficient of

    J_a^1570 h r^48 eta_a^224 u^186 v^209 z_a²

is +2^325 beta^785, nonzero for every beta>0. Independent exact modular evaluations confirm this degree and coefficient. The sharper form is the preferred24-integer entry; its165 gates still consist of96 multiplications and69 additions/subtractions.
