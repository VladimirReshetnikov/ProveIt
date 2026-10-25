# A free-scale carrier: fifteen unrestricted integers, degree 44

## Result and exact boundary

The division-free polynomial in `equation.json` has fifteen unrestricted integer variables, exact total degree 44, and 111 live binary arithmetic gates. Its zero existence is equivalent to finite syntactic refutation of ZFC through the unchanged authenticated source34 compiler. Consequently ordinary ZFC proves that absence of its integer zeros is equivalent to syntactic Con(ZFC).

The new step releases the scale variable Y, previously written qv, while compensating for loss of early CRT coprimality. A strengthened budget forces the requisite scale magnitude first. A slightly stronger whole-product bound then recovers the power-of-two property before the full scale congruence. The recovered projection then licenses cancellation in the integers; no coprime CRT claim is needed. This is an ordinary reduction, not a consistency proof, global optimum claim, encoded object-language ZFC derivation, or new end-to-end proof-assistant certificate.

The immediate arithmetic dependencies are the pinned predecessor's `lowdegree/PROOF.md` Sections 3–5, `source/CENTERED_BUDGET_PROOF.md` Sections 2–6, and `source/SIGNED_QUADRATIC_PROOF.md` Sections 2, 4, 5. These supply the signed Pell rank and auxiliary step-down, signed ratio growth, centered half-binomial extraction, and canonical source family. The present proof identifies every changed hypothesis and restores a literal predecessor zero before invoking its soundness theorem. Completeness uses the canonical family, not a claim that every arbitrary predecessor zero lifts unchanged.

## 1. The full polynomial

All inputs are unrestricted integers:

    j,C,z,h,r,v,w,T,c,n,f,y,p1,p2,p3.

All following names are polynomial abbreviations, not extra witnesses. The fixed six coefficient integers are exactly the authenticated predecessor payloads; MF is already shifted.

    J=6j+1, qm=beta J, q=qm+1, W=12w+4,
    X=qW, Y=v, F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-Yk, L=E(Yk),
    I=(2r+1)c^2, Q=Delta(f^2-1), V=f^2(cT-R)-c,
    q3=q^3, M=2q3, U=MH, Klo=2X^2-3Xc-2,
    Z=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    B0=k^2(q^2-Derr)-4q^2 eta^2,
    budget=Y^2 B0-k^2 q^8,
    pos=1+p1^2+p2^2+p3(p3+1).

The residuals and final polynomial are

    A=(Z+Uk)^2+4U(LZ-U),
    B=f^2-Delta I^2-1,
    Caux=V^2-(Q-1)y(2V+y)-1,
    G=budget-pos,
    P=A^2+B^2+Caux^2+G^2.

The literal evaluator uses the pointwise-identical schedules Klo=X(2X−3c)−2 and budget=(Yk)²(q²−Derr)−q²[4(Y eta)²+(k q³)²], reusing Yk and q³. B0 is a proof abbreviation, not a materialized DAG register. Powers use multiplication; the circuit has no division gates.

## 2. Early integrality without a coprimality assumption

The authentic beta is 2^1064921−1, odd and 1 modulo 3. Thus q is even and 2 modulo 3. It is nonzero since beta>1 and beta J=−1 is impossible. H is odd and nonzero, so U is nonzero on every assignment.

At a zero, all four residuals vanish. Put t=Z/U in Q. Then A=0 is the monic equation

    t^2+2(2L+k)t+k^2-4=0.

Hence t is integral by the rational-root theorem. Modulo 2, t+k is even. Put s=(t+k)/2; the carrier identity gives

    s^2+(2s-k)L-1=0,
    (s+L)^2=1+L(L+k).

Thus the ordinary first Pell root is integral. Also U|Z, whence

    M | H(Y-q^3),     H | M Klo.

At this point gcd(H,q)=1 is NOT asserted. In particular, the first divisibility does not yet imply M|Y−q³. But H is odd and q even, so its 2-primary part does imply Y even. Consequently a is even and Delta is odd, as needed for the normalized strong-kernel restoration in the inherited signed rank argument.

For K=X(X+2ac)−1, the universal identity

    2K-Klo=HXc

and oddness of H yield H|q³K. This weakened main projection is retained until Section 5.

## 3. Stronger budget supplies the early magnitude

The positive polynomial pos represents every positive integer and is strictly positive on all integer triples. Hence budget>0. If k=0 then budget≤0, so k≠0. Also Y≠0. We have

    Y^2 B0 > k^2 q^8 > 0,

and therefore B0>0. Since B0≤k²q², cancellation of the positive k²q² gives

    Y^2>q^6,     |Y|>|q|^3.

The standard budget argument now gives, writing q0=|q|, x=|X|, m=|Y| and K0'=|k|,

    Derr<q^2, |eta/k|<1/2,
    F,C,alpha=q-F-C have q's common strict sign,
    K0'(m-1/2)<|c|<K0'(m+1/2),
    sign(c)=sign(kY).

The authentic masks then give

    q0≥16, q0(q0^2−1)<R<q0^4−2,
    x≥4q0≥64, m>q0^3, |E|>4q0^4>3R+1.

Thus all numerical hypotheses used by the predecessor's signed Pell bootstrap hold. The only previously supplied facts about the literal cubic scale used before projection were m≥q0³ and parity Y even. Both have now been established without CRT coprimality.

## 4. Main-root recovery and signed indices

This section uses exactly the inherited signed Pell arguments, with their hypotheses verified above. Set Bp=|a+2|, c0=|c|, and I0=|2r+1|c0². Then Bp≥3, Delta=Bp²−1, I0≥c0, and B=0 gives f0=|f| with

    f0^2−Delta I0^2=1,     f0>2I0.

With S=Delta I0, the auxiliary residual gives Q=S² and

    S^2V^2−(S^2−1)(V+y)^2=1.

Odd-index classification and folding modulo f0, using V≡−c modulo f0, recover an integer square root of 1+Delta c². Explicitly, the odd auxiliary index gives psi_Bp(ell)≡±c0 modulo f0. Fold ell to 0≤p≤m0, where f0=chi_Bp(m0) and I0=psi_Bp(m0). Since psi_Bp(p)+c0≤2I0<f0, the congruence forces psi_Bp(p)=c0.

The first Pell classification and this main classification yield

    |k|=2 psi_Pp(n0), c0=psi_Bp(p), Pp=|2XY²+1|>Bp.

The centered interval implies p>n0. The congruence k=R+1+hE and |E|>3R+1 give the same signed first-index lower bound as before. The strong-rank lemma and auxiliary step-down, with V≡−c mod f0 and V≡−R mod c0, give p=R. The negative first-index branch is impossible and no-wrap gives 2n0=R+1. Hence R=2s0+1 with s0≥24.

The inherited sign-uniform ratio argument needs x≥64, m≥6 and the above classifications and interval, not a literal expression for Y. It yields

    m>(x−3)^s0/2−1,
    |H|>x(x−3)^s0.

No main projection or power-of-two assumption was used here. Delta odd, proved in Section 2, also licenses the old normalized-coordinate change (Delta(2r+1)−1)/2 when that inherited interface is used.

## 5. The stronger whole-product bound and late scale recovery

Let sigma=sign(c), x0=sigma X. The ordinary signed polynomial Pell projections modulo odd H, with p=R odd, give

    2^R K ≡ (x0−2^R)(2^R x0+1)  (mod H).

Since H|q³K, we have

    H | q³(x0−2^R)(2^R x0+1).

We now prove the larger modulus bound rather than cancel a nonunit. As x≥64 and s0≥24,

    (x/32)^s0 ≥ (x/32)^24 ≥ x^4,

because x^20≥64^20=32^24. Consequently

    |H|>x(x−3)^s0 ≥ x(x/2)^s0 ≥16^s0 x^5.

Since q0≤x/4 and R=2s0+1,

    q0³ 2^(2R+2)x² ≤(x³/64)16^(s0+1)x²
                            =(1/4)16^s0 x^5 < |H|.

The absolute value of the whole displayed divisible product is strictly less than q0³2^(2R+2)x², by |x0|=x and elementary triangle bounds. It must therefore be zero. Its factor 2^R x0+1 is odd and cannot be zero, so x0=2^R.

Moreover X=q(12w+4) is 2 modulo 3, and R is odd, so sigma=+1 and X=2^R. More importantly, the now-zero whole product and the Pell projection congruence give H|2^R K. Since H is odd, H|K and hence H|Klo. Thus

    g=Klo/H in Z.

Substitute Klo=Hg into U|Z and cancel the nonzero integer H from that divisibility. This gives

    M | Y−q³,    v_scale=(Y−q³)/M in Z,
    Y=(2v_scale+1)q³.

This cancellation is in the integers, not cancellation of a nonunit modulo H. Although q|X=2^R also makes q a signed power of two, that fact and CRT coprimality are not needed for this scale-recovery step.

This is precisely the required cubic scale, recovered only after the signed bootstrap. The source's surviving first-index sign branch gives k>0, then c>0 and sign(c)=sign(kY) give Y>0. Its centered half-binomial extraction consequently applies unchanged, including 0<eta/k<1/4.

## 6. Complete soundness map

Given any new zero, the preceding proof produces all divisions as integers. Define the fifteen-variable degree-48 predecessor's variables by retaining j,C,z,h,r,w,T,c,f,y and setting

    v_old=Y/q,
    n_old=t−g−v_scale.

The predecessor computes Y_old=qv_old=Y and has M_old=2q², U_old=M_old H. Its numerator therefore satisfies

    Z_old/U_old=n_old+Klo/H+(v_old−q²)/(2q²)
               =n_old+g+v_scale=t.

Thus its centered first carrier vanishes. Its strong and auxiliary rows are identical. The old base budget B0 is a positive integer by Section 3. Choose any integers p1_old,p2_old,p3_old representing B0 as 1+p1_old²+p2_old²+p3_old(p3_old+1), and use them in its guard. Such integers exist by the three-square theorem; a terminating enumeration provides a fully specified choice if desired.

This is a literal predecessor zero, not merely a list of heuristic sign properties. Its inherited native/compiler/refutation theorem gives a finite syntactic refutation of ZFC.

## 7. Complete canonical completeness map

Conversely assume a finite syntactic refutation of ZFC. Use the exact authentic canonical compiler family of `CENTERED_BUDGET_PROOF.md`, Section 6, and its predecessor carrier completeness map. This family has q>0, X=2^R, R=2s0+1≥49, Y=(2v_scale+1)q³ and

    Derr≤q²/2,     0<eta/k<1/4,
    B0>q²k²/4,
    Y=Mbin/2≥X^s0/2.

Here X≥4q and s0≥24, so Y>2q³. Therefore

    Y² B0−k²q⁸ > k²q²(Y²/4−q⁶)>0.

Let t be the centered integral first carrier coordinate of that canonical predecessor zero, and g=Klo/H. Set the new v=Y and

    n=t−g−v_scale.

All other arithmetic inputs are retained. Then Z/U=t, so the new carrier vanishes, and the strong and auxiliary rows are unchanged. Represent the new positive budget by the three private Pos coordinates. This constructs a new integer zero.

The two constructions establish equivalence of zero existence. They are not claimed to be inverse bijections on arbitrary zero sets, since the new guard is genuinely stronger and the converse uses the canonical source family.

## 8. Exact degree and cost

The register degrees are

    q:1, X:2, Y:1, F:2, R:5, E:3, a:3, H:3,
    Delta:6, k:5, L:9, I:3, Q:8, V:7, M:3, U:6,
    Klo:4, Z:7, B0:14, budget:18.

The four residual degrees are 22,12,16,18. Only 4ULZ contributes in degree 22 to the first residual. Here Z0=U0 n+4q0³X0², so the degree-44 top form is 16U0²L0²Z0². Its coefficient of n² is 16U0⁴L0². With

    q0=6 beta j, X0=12q0 w, Y0=v,
    R0=−q0³(12wC−q0z), U0=8q0³X0Y0,
    L0=X0Y0²R0,

we obtain the exact fixed-coefficient witness

    [j^26 w^6 v^8 z^2 n^2] P=2^54 3^32 beta^26>0.

The exponents sum to 44. All other squared rows have smaller degree. Thus degree 44 is attained for the actual fixed constants. The literal DAG uses 63 multiplications, 26 additions and 22 subtractions, 111 total. Compared with the retained 15-variable degree-48/108-gate endpoint, this is a strict degree improvement at a three-gate cost, not Pareto domination. The same elementary Klo factorization also reduces that old evaluator to 107 gates, giving an apples-to-apples four-gate cost; the mathematical improvement is degree, not evaluation cost.

Finite tests authenticate every coefficient byte, check every named register independently, verify the algebraic identities, prove the top coefficient symbolically, check the strengthened bounds on diagnostic grids, and reject modified gates. They do not certify the unbounded inherited compiler theorem; that remains the clearly identified ordinary proof boundary.
