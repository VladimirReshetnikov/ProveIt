# Ordinary-strong auxiliary quotient: full86,18 positive witnesses, exact degree131

This construction deletes one operation and one positive witness from the **ordinary**, `normalized=False`,87-operation source in [the transport quotient shear](complete86_transport_quotient_shear.md). The complete resulting polynomial uses **86=47M+39A**,18 strictly positive witnesses, and has exact total degree131 for every valid fixed compiler instance. Its positive integer zeros are in bijection with the entire positive zero set of that specific parent at the same ordinary input and fixed program numerals. The independent normalized85 construction is a different cost/degree point; no improvement below85 is claimed here.

The [standard-library helper](complete86_ordinary_auxiliary_projection.py) reads the authenticated saved JSON, emits the entire new source and paid product-minus-one finalizer in its [receipt](complete86_ordinary_auxiliary_projection.json), and executes no ancestor Python, compiler builder or historical suite. This is a bounded pinned-data CLI, not a maintained public API. All20 source/proof SHA256 pins are listed in both helper and receipt.

## 1. Actual source and paid change

All supplied witnesses and the ordinary input x are strictly positive integers. The six fixed numeral ports remain exactly `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`; they must satisfy the **whole inherited fixed-program recipe**, not merely positivity or the necessary inequalities used below. In particular B=Bm1+1 is a power of two at least16. The mathematical notation is

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=Y(X+1),
    A=a+2, Delta=A²−1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    K=k−hE, R=the retained packed index.

Registers `A,R10a,R10b,UM,R12,R14,r_lhs,index_difference` represent Delta,c,k,E,a,D,R,K respectively. In particular source register `A` is not the mathematical Pell parameter A.

The ordinary source retains

    Kaux=Delta(f²−1),
    Ns=(ic²)²−Delta(f²−1)+1,
    Na=Kaux(V²−y²)+y².

It replaces supplied o,j by positive T=`auxiliary_quotient` and computes

    V=c(Tf−1)−Rf².

The five paid rows are `Tf`, `Tf−1`, `c(Tf−1)`, `Rf²`, and their difference. The existing f² row is reused. They replace the two old V rows, three old linear-factor rows, and last factor multiplication: six operations become five, with the same three multiplications and one fewer addition/subtraction. The deleted factor was

    Nl=of−c−jc+K.

The new full polynomial is the product of seven retained factors minus1:

    Fchild=Nfirst*Nmain*Ninput*Na*Nk*Nt*Ns−1,
    Nk=K−R.

There is no omitted equality or uncharged finalizer. The new V depends on R, so the helper topologically reorders the literal rows. It checks all80 unchanged definitions, all81 retained expressions under the proved V cut, all old o/j consumers, and both entire finalizers. The free-coordinate order is exactly the parent's order with o removed and j replaced by T. Every declared coordinate and every one of the86 gates remains live.

## 2. Exact algebraic correction, with its domain

For an independent j, put o=cT−Rf. Then, as identities over every commutative ring,

    of−c=V,
    Nl−Nk=V+R−jc,
    Fparent(o=cT−Rf,j)+1−(Fchild+1)Nk
      =(Fchild+1)(V+R−jc).                         (1)

This includes c=0. For c≠0 over the rationals, set

    j=(V+R)/c=Tf−1−R(f²−1)/c.                      (2)

The correction becomes

    Fparent(restored)+1=(Fchild+1)Nk.               (3)

No division is an instruction in the child. Formula(2) is not an unconditional integer or positive map. Its integrality on zeros is a consequence of the **ordinary relaxed-rank theorem** below; the normalized85 polynomial expression for j cannot be substituted here. The receipt includes a positive off-zero tuple with nonintegral(2). Neither that tuple nor the finite component examples are presented as complete compiler zeros.

## 3. Packing and large main rank before restoring V or j

At a positive child zero, all seven integer factors are units. The main and input norms exclude−1 modulo4 since Delta≡0 or3. The ordinary strong factor also excludes−1: modulo4 it is a square plus1 if Delta≡0, and a sum of two squares if Delta≡3. Thus Ns=1 and Kaux=(ic²)². The auxiliary factor is then congruent to y² or V² modulo4, so Na=1 without knowing the sign of V.

The first factor is `tau²−u(u+1)k²`, u=XY²>1. Its negative-unit equation has the elementary strict descent used in [the85 mathematical proof](review_complete85_auxiliary_bezout_math.md): from uk<tau<(u+1/2)k, the positive coefficient `(2u+1)k−2tau` is smaller than k and preserves norm−1 after taking the nonzero absolute value of the other coordinate. Hence Nfirst=1. Write Nk=epsilon and Nt=nu. The other five factors are1, so nu=epsilon∈{−1,1}; neither sign is fixed yet.

With t=`transport_quotient`, the actual sheared transport is

    Nt=(Kconstant+w)C+1−F−(t−1)(q−1),
    C=q−F−Z−alpha−twice_cell_bits*x.

Its trailing part is nonpositive and Kconstant+w≥2. Thus C≤−1 would make Nt≤−2. Consequently C≥0 and F+Z<q. The exact unchanged packing uses the **shifted source mask** MF=MF0+B−1:

    G=q²−Z−qF,
    R=G(q²−1)+(MC+q(MF0+B−1))J.

The inherited mask bounds give

    (2q−1)(q²−1)<R<q⁴−q³,
    3q+1<R−2<R+2<q⁴≤E,
    a=E+Y>R+2, Delta>R>0.                          (4)

These are pretyping integer bounds; q is not yet assumed to be a power of two. They are exactly the bounds proved for this source in [the85 proof](review_complete85_auxiliary_bezout_math.md#2-unit-signs-and-the-untyped-packing-bounds). No old positive compiler zero is assumed.

The first positive norm has fundamental unit `2u+1+2sqrt(u(u+1))`, so

    tau=chi_P(n), k=2psi_P(n), P=2XY²+1, n≥1.

There is no smaller coefficient1 unit because its square would lie strictly between u² and(u+1)². Since P≡1 moduloE and Nk=epsilon,

    2n=R+epsilon+vE, v≥0,
    n≥(R−1)/2≥24.                                 (5)

The sign of v follows from0<R+epsilon<E. The main root D is positive by its source formula, hence D=chi_A(p), c=psi_A(p). Since P>A and c>k, p≤n would contradict monotonicity; therefore p>n. In particular

    c>A Delta², c>2p, c>2R.                        (6)

For the first inequality it already suffices that p≥6: `psi_A(6)=32A⁵−32A³+6A>A(A²−1)²` for A≥2. For the last, k=R+epsilon+hE>2R and c>kY. All of this precedes restoring the sign of V, the coordinate j or any auxiliary rank.

## 4. Ordinary rank supplies the missing integrality

Apply the generic middle argument of the pinned [relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md#the-relaxed-norm-forces-an-integral-pell-solution-at-a), with S=ic² and

    S²=Delta(f²−1), c=psi_A(p)>A Delta².

Its rank and divisibility argument is for arbitrary mathematical A≥2; the historical outer wrapper A=a+4 is not a premise of this middle lemma. It gives

    f=chi_A(m), S=Delta*psi_A(m), p|m, c|m,
    m≥c>2p.                                       (7)

Strong divisibility of the Pell sequence and p|m imply c|psi_A(m). Therefore

    c² | f²−1.                                    (8)

This is enough to make(2) integral. We do **not** infer c²|psi_A(m), which is a stronger normalized assertion and is not available for every ordinary tuple.

The ordinary size margin is also different from the normalized source:

    f²=1+i²c⁴/Delta≥1+c⁴/Delta.

By(6), c²>4Delta and c²>Delta+c. Hence f²>4c² and f²>Delta+c. Since Delta−R≥1,

    Kaux−Rf²−c=(Delta−R)f²−Delta−c>0.              (9)

For any integer H0>1, the equation `H0 V²−(H0−1)y²=1`, y>0, excludes V=0. If |V|>1, then y≥|V|+1, whence

    V²−1≥(H0−1)(2|V|+1), so |V|≥2H0−1.

Use H0=Kaux. Since T>0, the source gives V>−Rf²−c>−Kaux. This excludes the large negative branch. The cases V=±1 are excluded by V≡−c modulof and0<c−1<c+1<f. Thus V>0.

Now restore

    o=cT−Rf=(V+c)/f,
    j=(V+R)/c.

The first is an integer by its polynomial expression; the second is an integer by(8). Both are positive. In particular V=of−c=jc−R, and the restored linear factor is Nl=Nk=epsilon. At this stage the parent product equals epsilon; invoking its full zero theorem here would be circular.

## 5. Fix the index sign, then transfer both directions

The local fixed-minus auxiliary step-down is the one in the pinned [half-parameter proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md) and [the85 independent proof](review_complete85_auxiliary_bezout_math.md#5-the-auxiliary-congruences-identify-pr), with **S=ic²**, rather than the normalized Delta*ic². Briefly, the positive auxiliary solution has SV=chi_S(ell), with ell odd. The integer polynomial for chi_S(ell)/S gives, using S²=Delta(f²−1),

    chi_A(2ell)≡chi_A(2p) (mod f).

From f=chi_A(m), m>2p, strict nearest-multiple reduction yields ell≡±p modulom. The same odd polynomial, reduced modulo c with c|S and V≡−R, gives R≡±p modulo c. Both R,p lie in(0,c/2), by(6). Thus **p=R**. This uses the individual local equations; it does not invoke a complete coupled-kernel theorem whose product sign has not yet been restored.

Equation(5) now has v=0 because E>R+2 and n<p=R. If epsilon=−1, p=2n+1. Put Q=chi_A(2)=2A²−1>P. Pell duplication and monotonicity give

    psi_A(2n)=2A psi_Q(n)≥2A psi_P(n)=Ak,
    c=psi_A(2n+1)>Ak>k(Y+1),

contradicting the retained interval kY<c<k(Y+1). Hence epsilon=nu=1. All eight restored parent factors are1, and(3) gives a full positive parent zero. **Only now** is the parent's ordinary-input universal representation theorem inherited.

Conversely, every full positive ordinary parent zero has all factors1 and the rank conclusion(8). Its index/linear equations give `of+R=c(j+1)`. Multiplying this congruence by f modulo c gives c|(o+Rf). Thus

    T=(o+Rf)/c

is a positive integer. The new V is exactly the old of−c, so every retained factor remains1. The two formulas recover the original o,j,T uniquely. This proves a bijection of the complete supplied **positive integer zero sets**, with x and all other supplied coordinates fixed. There is no signed-zero theorem, unconditional positive-orthant map or uncorrected full-polynomial identity.

## 6. Exact whole-source degree131

All witnesses and ordinary x have degree1. The six fixed numeral ports have degree0. No unit equation, rank congruence or zero-only substitution is used in this degree calculation. The naive gate recurrence gives141; the two actual main/input norm cones use the all-value identity

    (X+ac+gamma)²−(a²+H)c²
       =(X+gamma)(X+gamma+2ac)−Hc².

For the input cone replace X,gamma,c by W,rho*H,kappa. Define

    Q0=Bm1*Jrep, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q0−F−Z−alpha−twice_cell_bits*x,
    T2=w*C1−transport_quotient*Q0.

The seven actual leading homogeneous forms, in final product order, are

| Factor | Degree | Leading homogeneous form |
| --- | ---: | --- |
| First |22| −w² k0² s⁴ Q0¹⁴ |
| Main |18| 8 gamma0 w² k0 s³ Q0¹¹ |
| Input |32| −4 delta² w⁵ s⁵ Q0²⁰ |
| Auxiliary |28| w² k0² s⁴ Q0¹⁴ T² f⁴ |
| Index |7| −h w s Q0⁴ |
| Transport |2| T2 |
| Ordinary strong |22| i² k0⁴ s⁴ Q0¹² |

Their full product is

    −32 Q0⁷⁵ h gamma0 delta² i² k0⁹ w¹² s²¹ T2 T² f⁴.    (10)

It has degree131 and is nonzero for every permitted fixed numeral specialization: Bm1>0, and T2 has the nonzero, otherwise unmatched coefficient−Bm1 of `transport_quotient*Jrep`. All remaining displayed factors are nonzero polynomials in independent supplied coordinates. Subtracting1 cannot alter this leader. The helper checks the entire120-monomial leading polynomial, not just the sum of degree estimates. Thus exact131 is uniform on the valid fixed-program family; it is not a claim about restricting the supplied variables to the zero set.

## 7. Reproducible checks and limits

The receipt includes the complete86-row source, full interface/ledger, source hash, all20 current dependency hashes, exact leading-form hash, both all-value local identities and both paid finalizer checks. Supplementary evaluations check48 full corrections, including16 rational cases and one c=0 case,336 retained factor values, and47 rational pullbacks with c≠0. The mod4 checks cover256 ordinary strong cases and64 auxiliary cases. Six ordinary Pell arithmetic fixtures test the rank-size premises, exact strong/divisibility equations, size margins and integral quotient formulas; they are explicitly **not** auxiliary-norm or full compiler zeros. No enormous positive universal witness is materialized.

The helper uses copied elementary sparse-polynomial and leading-form utilities from the prior independent85 source audit; this author packet does not present that reuse as independent review. It performs no imports or runtime execution of that audit or any ancestor module. The companion proof establishes the infinite-domain assertions; the finite fixtures do not replace it.

    python3 /absolute/path/complete86_ordinary_auxiliary_projection.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete86_ordinary_auxiliary_projection.json
