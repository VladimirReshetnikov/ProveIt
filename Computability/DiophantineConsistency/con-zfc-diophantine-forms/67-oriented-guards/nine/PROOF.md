# Nine positive variables: positive signed kernels and a tunable norm

## Statement, domains, and status

Let F_r be the literal polynomial in `generated/split_108_order{r}_positive.json`, for r=-1,0,1,2,3,4. Its nine unknowns are b,g,h,s,w,C,i,j,n, all strictly positive integers. The theorem is

    ZFC proves: (there is no positive integral zero of F_r) iff Con(ZFC).

This is an ordinary mathematical composition of the explicitly inherited source/compiler and Jones ratio theorems, not a new end-to-end kernel certificate. All finite exponents and fixed leaves specify actual ordinary integer coefficients; circuit registers do not count as quantified variables. There is no claim of globally smallest polynomial.

The natural versions shift every positive coordinate except j by +1 and use j itself as the internal j0. Thus they provide the equivalent theorem over nine nonnegative integers. The positive version always sets j0=j-1; replacing j0 by j without this shift would need a separate cofinality argument and is not done.

The previous 1,910,404-degree/473-operation endpoint is improved on both metrics by r=-1: degree 1,731,700 and 462 operations. The higher-majorant family is a degree/cost tradeoff:

    r      degree        positive operations
   -1    1,731,700              462
    0    1,731,700              465   (dominated, retained as an audit)
    1    1,663,788              475
    2    1,595,876              478
    3    1,527,964              482
    4    1,494,006              487

## 1. Source encoding and exact coefficients

The source is the unchanged 31-coordinate/22-equation source in `data/parent_source.json`, SHA-256 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287. Use the complete old31 four-port tuple in `coefficients/old_tuple`, not a mixture of ports from other encodings. The four unsigned little-endian payloads have bit lengths 1064921,1070004,1064921,1064922; MF is already shifted. The compiler correctness dependency and tuple adapter are retained in `upstream/old_tuple_complete_proof.md`, with baseline source pins in `upstream/FREE_C_SOURCE_PINS.json`.

The new source certificate is `data/split108_code.json`, and its literal kernels are `data/split108_kernels.json`. Apply the invertible row operations rho14=r14+r2, rho15=r15+r3, then globally negate all rows. The independent source verification in the sibling `encoding/` package proves

    [T^q_j] (D2(T) U_y(T)^2 + D1(T) U_y(T)+D0(T)) = -2 rho_j(y),
    U_y(T)=sum_(i=1)^31 y_i T^w_i.

All 22,544 same-degree interaction checks are exhaustive. The global sign does not alter the common zero set. The weights have maximum W=108; kernel degrees are 1939,1842,1738, with positive leading coefficients 2,2,beta. The convolution height is Hc=1954, and maximum target is 1939. Every kernel coefficient has absolute value below M=2^2134927. Since each positive leading coefficient is at least 1, for B>2M each kernel is positive: the magnitude of its lower tail is less than M B^d/(B-1), while its leading term is at least B^d.

Set kappa=2134940, a=2^kappa=8192M, B=a b^2, and

    ell=sum B^w_i, Us=ell+g,
    Gs=(D2(B) Us+D1(B)) Us+D0(B), Targets=sum B^q_j,
    N0=B^109, Mask=N0-1-(b-1)ell,
    Sc=g+N0(2Gs+Targets), Tc=Mask+N0(B-2)Targets,
    L=b B^2064, c=2^16012039, N=c B^1090,
    R=L(Sc+Tc+1)-Sc-1,
    t=b B^108, Gcap=32t.

All these are polynomial abbreviations. Gs>0 unconditionally; hence Sc,Tc are nonnegative, and R,N satisfy the same coarse lower bounds used by the old ratio bridge. On the soundness branch g<4t, Us<6bB^108. The coefficient bound and Hc give 2Gs/B^1955 < 86 M b^2/(B-1)<1/32. The target and mask terms satisfy the same stronger bounds as the old source, so Sc+Tc<B^2064<=L. The sibling source proof gives the detailed binary extraction/no-carry argument.

For b=2^k, B=2^v, v=kappa+2k, the 22 target blocks and 31 low mask coordinates give

    popcount(R)=2195v-30k-22-carry_defect
               =2 log_2(N)-carry_defect.

Indeed 2log_2(N)=2(15kappa/2-11)+2180v=2195v-30k-22. The carry defect is nonnegative and vanishes exactly for the required bit containment. That containment is equivalent to the source common zero condition through the displayed coefficient-extraction identities. The b=1 all-ones spurious candidate is excluded by the inherited nonzero fifth source residual. Completeness is available for all sufficiently large powers of two and supplies g<t, hence 32g<Gcap. Soundness requires only 8g<Gcap. These are precisely the unchanged numerical bridge hypotheses.

## 2. Ratio registers and why C may remain free

The following definitions are shared by every r. Put

    U=N^2 w, Y=N^2 s, M0=RY,
    P=2 M0^2 U, K=R+1+h(P-1), A=M0(U+1), B1=2R+1,
    W1=bw, J=4A-5, Q=3W1 C-2(W1^2-1),
    D=(A^2-1)C^2+1, e=iJC, E=eDC,
    F=(A^2-1)E^2+1,
    G=A+F(CD+1-A), H=C+F(B1+j0 C),
    I=(G^2-1)H^2+1,
    a0=(P^2-1)K^2+1, a1=DFI,
    m=K^2(4t-g)-16t(C-KY)^2,
    Omega=Jm, E0=J(n+W1^2)+Q.

The integer m is the old margin divided exactly by 8. Unconditionally,

    E0=Jn+(J-2)W1^2+3W1 C+2 >0.

If m>0, then |C-KY|<K/2, so C>K(Y-1/2)>K and C>B1+W1. This recovers the old carrier range instead of assuming it in the polynomial. On this recovered range, the exact CRT substitution H=C+F(B1+j0 C) preserves the original ratio witnesses, because F=1 modulo both J and C. The explicit inverse to the old positive index is

    j_old=1+((F-1)/C)B1+F j0 >=1.

The old-to-new direction follows by taking the nonnegative quotient of (H_old-C)/F in its residue class B1 modulo C; carrier range B1<C guarantees j0>=0. Thus the inherited ratio theorem is exactly the condition

    a0 and a1 are integer squares, J divides Q, and m>0.

It yields b binary and the desired binomial divisibility, and conversely supplies all witnesses for a source solution with sufficiently large binary b. No new parity restriction on g or h, no extra divisor Q+H, and no substitution m ->2m-1 is required. The positivity-first argument below is essential to this strengthening.

## 3. A finite family of unconditional majorants

Always V0=PK, so V0^2-a0=K^2-1>0. The baseline r=-1 uses lambda=8 and

    T=e(8D^2-4D-1)G, V1=TH.

Its strict inequality V1>lambda sqrt(a1) follows from

    [e(8D^2-4D-1)]^2-64DF=(8D+1)e^2-64D>0.

For r=0,1,2,3,4, put s_r=128,64,8,4,1 respectively, lambda=2048/s_r, and

    Lm=CD+1-A, Nstar=2G+Lm,
    N1=2e^2 D(D-1)Lm+3C,
    N2=2e^2(D-1)Lm,
    N3=2e^2(Lm-C), N4=2e^2 C,
    (a_1,a_2,a_3,a_4)=(64,40,28,21),
    correction= lambda                         if r=0,
                (512/s_r)i+lambda              if 1<=r<=3,
                256i(e^2+2)+2048               if r=4,
    T=e[((1024D^2-512D-128)/s_r)Nstar
         -sum_(j=1)^r (a_j/s_r)N_j]+correction,
    V1=TH.

Every quotient in this display is a fixed integer coefficient, not division by a variable. To prove V1>lambda sqrt(a1), let

    X=e^2 D^3(D-1),
    t_r=(1024D^6-512D^5-128D^4
           -sum_(j=1)^r a_j D^(4-j))/s_r.

The exact polynomial t_r^2-(1024/s_r)^2 D^11(D-1) has only positive nonzero coefficients for every r. Also t_r>0 for D>=1, since 512+128+64+40+28+21<1024. Therefore t_r/D^4>(1024/s_r)D^2 sqrt(1-1/D).

The exact remainder identities Nstar=D^j N_j+r_j have

    r1=3-A,
    r2=3CD+3-A,
    r3=2e^2(A-1)D^2+r2,
    r4=2e^2(1-A-C)D^3+r3.

For A>=3,C,i>=1, D>=A^2, eA/D<9i/2, eC/D<3i/2. The first three truncations have only one possibly negative remainder, r1, whose adverse contribution before dividing by s_r is <288i. The selected correction 512i/s_r+lambda is sufficient. For r=0 there is no remainder. For r=4 the full adverse contribution is less than 252ie^2+(765/2)i, dominated by the selected correction minus lambda.

Finally DF=X+D, G=(X/D)Lm+CD+1 and strict square-root concavity give

    lambda sqrt(DF)G
      <(lambda/2)eD^2 sqrt(1-1/D) Nstar + lambda v,
    v=(CD+1)/(2eD sqrt(1-1/D))<1.

Combining these inequalities proves T>lambda sqrt(DF)G, uniformly, even for arbitrarily large i. Since G^2 H^2-I=H^2-1>=0, V1>lambda sqrt(a1). This is a finite algebraic proof, not an asymptotic expansion. The order4 ancestor and its detailed estimates are retained in `upstream/HIGHER_MAJORANT.md`; the finite identities for all orders are checked by `check_ring.py`.

## 4. Single equation, both directions

Put b1=lambda^2 a1 and

    Theta=E0-Omega(V0+V1),
    F_r=(Theta^2-Omega^2(a0+b1))^2-4Omega^4 a0 b1.

This is the requested single ordinary Diophantine equation F_r=0.

If m=0, F_r=E0^4>0. Otherwise the real four-root factorization at a zero supplies signed roots u0^2=a0,u1^2=b1 with

    E0/J = n+W1^2+Q/J = m(V0+V1+u0+u1).

Both unconditional strict majorants make the right-hand parenthesis positive. E0/J>0, so m>0 follows before any integrality argument. Recover the carrier bounds of Section2. They give

    a1 > C^2 A^4 > K^2 P^2 > a0,

using A^2>P,D>C^2,F>=A^2,G>=A,I>=G^2 and C>K. Hence x=u0+u1=Theta/Omega is a nonzero rational number. The identity 2xu0=x^2+a0-b1 makes u0 rational; u1 is rational as well. A rational square root of an integer is integral, and u1/lambda is likewise an integral square root of a1. The factor identity now forces J|Q. The inherited numerical ratio theorem and Section1 conclude that the source has a zero, hence ZFC has a finite syntactic refutation.

Conversely, the inherited bridge gives positive witnesses with m>=1, square a0,a1, and J|Q. Preserve C and apply the exact index change. Take positive roots u0,u1 and set

    n=m(V0+V1+u0+u1)-W1^2-Q/J.

This is integral and strictly positive: W1^2+Q/J<2D, while V1>lambda sqrt(DF)G>2D. For the latter, F=(D-1)D^2e^2+1>D, G>=1 and lambda>=8. Thus the same n makes F_r vanish. Negation proves the stated Con(ZFC) equivalence.

## 5. Degree certification and reproducibility

The primary circuit uses only +,-,* with literals and the four coefficient payloads. `generated/LEDGER.json` lists exact live operation counts. Degree certificates are separate polynomials equal to D^16 F_r; they are not the delivered primary equation.

Let delta0=V0^2-a0 and delta1=V1^2-b1. With

    Bsmall=E0^2-2E0 Omega(V0+V1)+Omega^2(delta0+delta1),

one has exactly

    F_r=Bsmall^2+4Omega^2 V0 V1 Bsmall
          +4Omega^4(delta0 V1^2+a0 delta1).

For r>=0 set Rnum=e sum_(j=1)^r (a_j/s_r)r_j D^(4-j)+correction D^4,
q_r=t_r^2-(1024/s_r)^2D^11(D-1). Then

    D^8(T^2-lambda^2 DFG^2)
      = e^2 q_r Nstar^2
        +(1024/s_r)^2D^8[X Lm^2-4DG(CD+1)]
        +2e t_r Nstar Rnum+Rnum^2,
    D^8 delta1=H^2 D^8(T^2-lambda^2 DFG^2)
                 +lambda^2 DF D^8(H^2-1).

These resolve the apparent leading cancellations. The baseline uses its simpler displayed defect instead. The circuit propagates a multivariate degree upper bound and an exact diagonal leading polynomial in a,c,beta,K0,MC,MF. All final leaders are positive monomials, so the upper bounds are attained for the actual fixed tuple. Subtract 16deg D to recover the primary exact degree. The JSON degree files distinguish the primary leader from the certificate leader.

Run build_nine.py, check_ring.py and check_nine.py. The latter authenticates inherited payloads, verifies DAG acyclicity/liveness and operation counts, and compares independent literal evaluation with every primary and certificate circuit modulo three primes on both domains. The source proof and tests are in the sibling encoding package. These finite audits test implementation and exact identities; they are not substituted for the unbounded mathematical proof above.
