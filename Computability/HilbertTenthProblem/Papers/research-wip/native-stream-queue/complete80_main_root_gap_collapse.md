# A positive main-root gap gives an 80-gate candidate that admits every input

The complete candidate in the [receipt](complete80_main_root_gap_collapse.json) costs **80 = 45M + 35A**, retains **18 strictly positive witnesses**, and has exact degree **207**. It is **refuted as a replacement for the inherited fixed-program compiler**: every authentic fixed-program numeral tuple and every ordinary input x>0 have a full positive integer zero. In particular the empty-language compiler admits every input in this chart. This is not a new universal operation bound or a claim about all possible coefficient recipes.

The change replaces the positive gap between the main and input *projection quotients* by a positive gap between the two Pell roots. It retains the original outer slack, the first-index coordinate h, both ratio bounds, the input norm and the complete normalized auxiliary block. It is distinct from the existing 17-witness first-index-deletion80 and from the independent-gamma83 chart.

## 1. Literal complete source and full polynomial map

The authoritative parent is `complete84_scaled_strong_output.json`, SHA256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. The helper authenticates its complete trio and seven other proof/scope files; all ten exact hashes are saved in `PINS` and the receipt. They are read only as bytes, text or JSON. No predecessor program, historical builder or archived code executes.

Use a=R12, c=R10a, X=wn2, H=a4m5=4a+3, kappa=index_rhs and mu=exponent_rhs. Delete exactly these five old rows:

    cam2 = c*a
    D1 = X+cam2
    gamma_sum = rho+sigma
    gam = gamma_sum*H
    R14 = D1+gam.

Replace supplied sigma by a strictly positive `main_root_gap`, denoted d_gap, and insert the single addition

    R14 = exponent_rhs+main_root_gap.

The full DAG is reordered topologically. Every other producer, factor and finalizer is retained literally. The deleted private registers have no outside consumer; R14 still feeds the main square. The full80 array has no dead row or unused free port. The seven-factor producer core costs 73=39M+34A; the unchanged six multiplications and final subtraction cost 7=6M+1A.

Let D_old=X+a*c+(rho+sigma_old)H. The retained input root is mu=W+a*kappa+rho*H. Over **every commutative ring** the full polynomials obey

    P80(d_gap=X-W+a(c-kappa)+sigma_old*H) = P84.       (1)

Indeed the new R14 is then D_old and all retained rows agree inductively. This is a complete polynomial identity, not just a norm identity. On H!=0 the converse rational substitution is

    sigma_old=(mu+d_gap-X-a*c)/H-rho.                 (2)

No integer or positive inverse is asserted. The missing divisibility in (2) is substantive.

At a positive parent zero, the established parent theorem gives D_old=chi_A(R), mu=chi_A(u), and u<R, where A=a+2. Thus d_gap=D_old-mu>0, so every parent positive zero maps forward. That containment does not establish soundness of the larger chart.

The local-producer, joint-root and actual-modulus scouts were read to check scope. Their all-value root schedules or bounded independent-port obstructions do not cover this positive-coordinate projection. No earlier refuted outer-slack or upper-ratio chart is being renamed.

## 2. Authentic fixed numerals and legal mask words

Fix any authentic numeral tuple of the inherited compiler and any x>0. Retain its complete recipe unchanged. The contracts used below are

    B=2^d, d odd, ell=2d, b odd and b>=3, K=Kconstant>0,
    0<MC,MF0<B-1, MC=2 mod4, v2(MF0)=2,
    popcount(MC)+popcount(MF0)=d,
    MF_source=MF0+B-1.

These are actual contracts of the modified half-binomial compiler, not a claim that arbitrary numerals satisfying this short list encode a program. The six source coefficients remain B-1,K,ell,b,MC,MF_source. In particular MF0 is the native field mask, whereas the literal `MF` port is shifted.

Put u=ell*x+b and W=2^u. Choose a sufficiently large odd N (a sufficiently large power of five is allowed), and put

    t=dN, q=B^N=2^t, J=(q-1)/(B-1),
    Z=1, C=W+1, F=4,
    alpha=q-W-ell*x-6>0.                              (3)

Choose q>W+ell*x+6, so all displayed supplied outer coordinates are positive. The original, unweakened source computes

    marked_rhs=q-F-Z-alpha-ell*x=C,
    W=marked_rhs-Z=2^u.

The actual packed index is

    R=(q²-1-4q)(q²-1)+(MC+q*MF_source)J.              (4)

Define the authentic shifted masks

    TC=MC*J+1, TF=MF0*J-1.

The low word Z-1 is zero. Since J is odd and v2(MF0)=2, the lowest three bits of TF are 011, so F=4 has no common bit with TF. Thus both shifted mask conditions hold *exactly*, including the exceptional origin field test. The inherited inverse-population identity consequently gives

    popcount(R)=3t+2.                                 (5)

This use of the mask lemma does not assert that C is a valid computation. The transport multiplier has not been identified with a cyclic binary shift.

The source bounds give 3q+1<=R<q^4. They also follow directly from (4), q>=16, F=4 and the mask ranges. Modulo4, q=0, J=1 and MC=2, so R=3 mod4. In particular R>q>u. These are properties of the **actual packed index**, not a freely supplied main rank.

## 3. The now-free multiplier solves transport

Both u and t are odd. Hence

    gcd(2^u+1,2^t-1)=1.                               (6)

For example, a common odd prime would give an even order of 2 dividing odd t, a contradiction: that order divides 2u but cannot divide u. Therefore C is invertible modulo q-1.

Choose w satisfying

    w=4*C^(-1)-K mod(q-1),    w=0 mod(2q²),
    X=wq>=2^R.                                       (7)

The two moduli are coprime, and adding their product permits the last inequality. One explicit choice is

    r0=(4*C^(-1)-K)*2^(-1) mod(q-1), 0<=r0<q-1,
    w=2q²*(r0+(q-1)*2^R).

This is an existential arithmetic choice, not paid input preprocessing. It fixes X only after the finite outer words and their actual R are fixed.

The source transport quotient

    Ttransport=((K+w)C+q-5)/(q-1)                     (8)

is an integer by (7) and is strictly positive. It gives the literal retained factor

    (K+w)C+q-F-Ttransport*(q-1)=1.

The paid asymmetric w consumer is respected exactly. No old w=X/q³ coordinate is used. The crucial lost restriction is X=2^R; the chart permits the independent choice (7).

## 4. A half-binomial converse for every even X>=2^R

This section proves the needed extension directly; it does not apply an exact-power converse outside its hypotheses. Set r=(R-1)/2 and define the integer polynomial

    M_X=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j,
    Y=M_X/2,
    a=Y(X+1), A=a+2, Delta=A²-1, E=XY, P=2XY²+1.

M_X is even because X is even and the central binomial coefficient is even. From (5),

    popcount(r)=3t+1,
    v2(binom(2r,r)/2)=3t.

Since 2q³ divides X, every nonconstant term of M_X/2 is divisible by q³. Thus s=Y/q³ is a strictly positive integer. No assertion of the *exact* valuation of Y is needed; cancellation between these terms is harmless.

Write

    xi=(X+1)^(2r)/X^r=M_X+theta.

The sum of the lower-half binomial coefficients is less than 2^(2r-1), so X>=2^(2r+1) gives 0<theta<1/4. Also Y>=X^r/2. Define fresh Pell values

    c=psi_A(R), D=chi_A(R),
    k=2psi_P(r+1), tau=chi_P(r+1).

For z>=2, elementary recurrence induction gives

    (2z-1)^(n-1)<psi_z(n)<(2z)^(n-1) for n>=3.

(The upper bound is equality at n=2, which is not used.) Therefore

    c/k > (xi/2)*[(1+3/(2a))²/(1+1/(2XY²))]^r > xi/2,
    c/k < (xi/2)*(1+2/a)^(2r).

The last strict lower comparison uses 6XY²>a, which follows from X,Y>=2. Since 4r/a<1/2, the geometric-series binomial bound yields

    0<c/k-xi/2 < 4r*xi/a < 16r/(X+1) < 1/2.

Here R>=7, as is more than guaranteed by R>=3q+1; the last inequality holds for every r>=3 and X>=2^(2r+1). Combining this with theta/2<1/8 proves

    Y<c/k<Y+1.                                       (9)

Consequently eta=c-kY and zeta=k-eta are positive integers. They give the literal source identities k=eta+zeta and c=kY+eta. The two Pell norms are exactly1.

Because P=1 mod E, the recurrence gives psi_P(r+1)=r+1 mod E. Hence

    h=(k-R-1)/E

is an integer; strict Pell growth makes it positive. The retained first-index factor k-hE-R is exactly1. Thus no first-index or ratio condition has been dropped in this construction.

## 5. Positive input, root gap and auxiliary witnesses

Use the fresh A from Section4. Put

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa-u)/Delta,
    rho=(mu-a*kappa-2^u)/H, H=4a+3,
    d_gap=D-mu.

For odd u, the Pell expansion gives psi_A(u)=u mod Delta. Since u>=3 and A>=2, kappa>u, proving that delta is a positive integer.

For rho, set g_j=(chi_A(j)-a*psi_A(j)-2^j)/H. Its exact recurrence is

    g_0=g_1=0, g_2=1,
    g_(j+2)=2A*g_(j+1)-g_j+2^j.

It proves integrality and strict growth for j>=1; in particular rho=g_u>0. This argument uses no main projection quotient or main congruence. Since R>u, D>mu and d_gap is a positive integer. The actual input source computes kappa and mu, its norm is1, and the new main root mu+d_gap is D.

Complete the retained normalized auxiliary block canonically at these fresh A,c,R:

    m_aux=2cR, f=chi_A(m_aux), i=psi_A(m_aux)/c²,
    S=Delta*psi_A(m_aux)=i*Delta*c²,
    y_aux=psi_S(R), V=chi_S(R)/S.

The expansion of (D+c*sqrt(Delta))^(2c) shows c² divides psi_A(m_aux). Thus i is a positive integer and S²=Delta*(f²-1). For R=2j+1 with j odd, the odd Chebyshev quotient identities give

    V=Q_j(S²), Q_j(1-A²)=(-1)^j psi_A(R),
    Q_j(0)=(-1)^j R.

Since S²=-Delta=1-A² mod f and S=0 mod c, these prove

    V=-c mod f, V=-R mod c.

Also f²=1 mod c, and gcd(c,f)=1 by the strong Pell identity. Therefore

    Taux=(V+c+R*f²)/(c*f)

is a positive integer: divisibility holds separately modulo c and f, and the numerator is positive. The literal source recovers V=c(Taux*f-1)-R*f². Its auxiliary norm is1 and its scaled strong factor is Delta.

All **18 supplied witnesses** are now positive integers:

    J,F,alpha,Ttransport,f,h,i,Taux,s,w,tau,
    eta,zeta,y_aux,Z,delta,rho,d_gap.

The seven literal factors, in source order, are

    [1,1,1,1,1,1,Delta].

Their paid product minus Delta is zero. Every coefficient, ordinary input and retained obligation is the actual one of the candidate. Since the construction works for every x>0 on each authentic fixed program, the candidate cannot replace the universal84 on that recipe. No inference about an unrelated coefficient recipe is made.

## 6. Complete degree and evidence scope

With fixed compiler coefficients, let Q0=(B-1)J, k0=eta+zeta and

    a_top=w*s*Q0^4,
    C1=Q0-F-Z-alpha-ell*x,
    Ttransport_top=w*C1-transport_quotient*Q0.

The unchanged input root has degree19 and leader delta*a_top³. Therefore the new main norm has degree38 with leader delta²*a_top^6: its subtracted Delta*c² has only degree22. The other six complete factor polynomials are unchanged and have degrees22,32,60,7,2,46, summing to169. Their parent leaders are already authenticated. Dividing the parent's displayed product leader by its main leader 8*(rho+sigma)*a_top²*c_top and inserting the new main leader gives

    4 Q0^124 h delta^4 i^4 k0^12 w^22 s^34
        *Ttransport_top*Taux²*f².                     (10)

In particular the coefficient of

    J^125*h*delta^4*i^4*eta^12*w^22*s^34
        *transport_quotient*Taux²*f²

is -4*(B-1)^125, nonzero on every valid fixed slice. Thus the complete degree is exactly207. The final degree12 subtraction cannot cancel (10). The separate raw gate-propagation upper bound is213.

The fresh standard-library helper authenticates ten dependencies, reconstructs all80 rows, checks private consumers and all-row/all-port liveness, and saves the complete source and interface. It checks 48 signed/rational full-source forward maps, plus rational inverses where H!=0. Three independent full dense coefficient specializations attain all seven factor degrees and207 and match (10). These finite coefficient checks corroborate the uniform proof; diagnostic numerals are not promoted to actual compiler programs.

Separate bounded evidence includes12 exact arbitrary-X Pell ratio fixtures,45 positive input interfaces,22 outer arithmetic-mask/CRT fixtures, and18 half-binomial modular identities. The outer fixtures satisfy the stated arithmetic contracts but are explicitly **not compiled histories**. Their small representative w need not meet X>=2^R. The enormous actual compiler family in Sections2–5 is proved parametrically; no complete large positive zero is materialized.

No historical helper executes. Fresh normal and optimized exact receipt replays from `/` both pass. From any directory, use `--root` for the absolute native-stream-queue directory and `--expect` for this packet's receipt; `--output` emits a fresh deterministic receipt. All checks use explicit exceptions and remain active under optimized Python.

The independent-gamma83 language question remains unresolved: that chart retains a main projection congruence which the present80 deliberately omits. The counterfamily here does not transfer to that chart without a separate divisibility proof.
