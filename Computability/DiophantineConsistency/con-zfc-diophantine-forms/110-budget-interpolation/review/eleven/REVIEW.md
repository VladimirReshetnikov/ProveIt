# Independent review of the eleven-integer parity/interpolation construction

## Verdict and limits

**PASS. No blocking defect found in the new ordinary mathematical reduction or in the three supplied literal circuits.** The final primary equation has eleven unrestricted integer coordinates, exact total degree **2240**, and **206** live binary arithmetic operations. Its auxiliary-centered and uncentered companions have exact degrees **2272** and **2912**, with **204** and **200** operations respectively.

These are exact metrics of the supplied circuits with their six authentic fixed coefficient payloads. They are not arithmetic-circuit lower bounds or claims of global optimality. The consistency equivalence is an ordinary mathematical composition with the explicitly inherited native compiler and finite-syntactic-refutation calibration. This review does not repeat every inherited compiler/runtime proof, establish consistency, or provide an end-to-end proof-assistant or object-ZFC certificate. Finite executable checks are not substituted for the universal arguments below.

The reviewed final architecture is the parity version with I=2src², Dg=1+4(3Budget−4)s², non-main radical coefficients 1,2,4,8 in strong/auxiliary/first/guard order, and the reversible carrier shear (2Q−1)V+4Ltau. The earlier degree4512 and degree4384 variable-weight proposals are superseded, not endpoints covered by this verdict.

## 1. Zero-coordinate and reality bootstrap

The affine restrictions and actual beta imply q even, q=2 modulo3, |q|≥16, X=2 modulo3 and |X|≥64. The fixed odd multiplier in Y makes |Y|≥4096. Hence a=(X+1)Y has large absolute value, H=4a+3 is nonzero and Delta=(a+2)²−1>1. Therefore Dm,Df and Dt are positive on every integer assignment, before any native or Pell decoding.

Q=(Delta I)² never equals1. If I=0 then Da=1. If I≠0, c≠0 and |I|≥2c²; Df>|c|+1. With the integer b=c−R+4IT, either b=0 and |V|=|c|≥1, or |V|≥Df−|c|>1. Thus Cy and Da are positive in the nonzero-I case. No sign of R is needed here.

At S=IH⁵=0, every scaled radicand except A0 vanishes and the complete norm is exactly (A²−B²Dm)^16. The carrier shear also vanishes after multiplication by S. The homogeneous quintic has no zero in a real extension of degree at most two: its quadratic factor is positive on the real line and its cubic factor is irreducible of degree three. Consequently A±B√Dm cannot vanish and the zero-S slice contains no norm zero. This proves s,r,c,I,S all nonzero before they are used in divisibility or sign arguments.

A vanishing complex factor can now have only one possibly imaginary term, the guard term 8S√Dg. Its coefficient is nonzero. Thus Dg≥0. If Budget≤1, then Dg≤−3; therefore Budget≥2. The centered budget yields Derr<q², |eta/k|<1/2 and k≠0. Since the two cone constants are at least8, the disk inequality restores the common nonzero sign of F,C,alpha,q. It also gives sign(c)=sign(kY) and |k|(|Y|−1/2)<|c|<|k|(|Y|+1/2). It does not imply the earlier determinant guard or eta>0, and the proof correctly does not use either yet.

## 2. Early projection, the main congruence, and parity separation

Projection onto the rational squareclass of a rational linear combination of square roots of integers keeps only its integer square roots. This remains valid when irrational terms share a squareclass and cancel. If d=√Dm were irrational, projection of the actual vanishing factor would force S|A, hence H|A. But a,H,Delta are0 modulo3, b0=2, u=1 and Dm=1, so A=1 modulo3. Since 3|H, this is impossible. Thus the actual signed main root d_s is integral.

A second rational projection gives S|(A+B d_s) even before the other roots are separately known to be rational. The latter equals Phi_H(d_s−b0+HT), and H⁵ divides it. If p^e divides H exactly and the argument had p-adic valuation b<e, its leading fifth power would be the unique term of valuation5b. Every other homogeneous term has strictly larger valuation. This contradicts divisibility by p^(5e), proving H|(d_s−b0) and integral gamma. The proof works for negative H and signed roots.

After subtracting the integral main-root contribution and dividing by S, the remaining signed sum is f+2ytilde+4tau+8g. All four radicands are positive odd integers: I is even, so Df=1 modulo4 and Q=0 modulo4; hence Da=(Q−1)(QV²−1)=1 modulo4. X is divisible by8, so Dt is odd; Dg=1 modulo4 and cannot be zero.

For any positive odd integer radicand, its coefficient of the corresponding squarefree radical is an odd integer. In any nontrivial squareclass, the participating signed coefficients therefore have distinct 2-adic valuations among0,1,2,3. The term of least valuation cannot cancel. Linear independence of distinct squarefree radicals excludes every nontrivial class. Thus all four base roots are rational, and their integer radicands make them integral. No magnitude ordering or hidden independence assumption on the original radicands is used.

The rational auxiliary ordinate y=ytilde/(Q−1) satisfies QV²−(Q−1)y²=1. For a lowest denominator b, the equation gives b²|(Q−1). The adjacent-coefficient Pell transformations preserve the norm, integer V and the reduced denominator, while strictly reducing |V| when |V|>1. Taking absolute values after each step is harmless. At |V|=1 the ordinate is±1, proving b=1. This is a universal descent, not a conclusion from finitely many Pell samples.

## 3. Nonodd strong rank and the centered signed-kernel splice

The restored relations have rho=Delta I, rho²=Delta(f²−1), c²|I, V=fo−c and V=cj_aux−R. The explicit factor changes in j_aux are correct for I=2src²: 4Delta s²r²c³(c−R)+8src DfT. All divisions used in the proof are justified integer quotients; no new quantified coordinate is introduced in the circuit.

The inherited common-sign packing and first/main Pell classifications apply to the weaker centered interval. They give |c|=psi_B0(p), |k|=2psi_P0(n), p>n≥24 and |c|>2p,2R before strong-rank recovery. The normalized strong Pell equation directly gives |I|=psi_B0(m), |f|=chi_B0(m). Strong divisibility first gives p|m. Writing m=pv, composition yields psi_B0(m)/|c|=v chi_B0(p)^(v−1) modulo |c|. Since |c|² divides I and the chi coefficient is a unit modulo |c|, |c| divides v. In particular p|m, |c||m and m>2p. No oddness of I/c² or rho/c² is needed.

The auxiliary classification has an odd index: an even-index chi at base |rho| is±1 modulo |rho|, whereas its abscissa |rho V| is0. The two odd-quotient identities then give the signed residue of psi_B0(ell) modulo |f| and the residue ell=±R modulo |c|. Squaring the first residue and using the doubled chi identity permits the inherited signed abscissa step-down with m>2p. It gives ell=±p modulo m, hence R=±p modulo |c|. The strict bounds p,R<|c|/2 force p=R.

The first-index congruence then unwraps to2n=R+1. The signed ratio and main-root congruence prove X=sign(c)2^R with R odd, without assuming positive X,Y,k or an odd strong multiplier. X=2 modulo3 selects X=2^R and c>0; the remaining first-index sign gives k>0 and then Y>0.

Only now is the centered half-binomial argument used. Its uniform ratio error is strictly between0 and1/8, while the fractional binomial tail contributes strictly between0 and1/8. Thus c/k lies strictly between Mbin/2 and Mbin/2+1/4. The centered interval |c/k−Y|<1/2 and integral Y force Y=Mbin/2. Consequently0<eta/k<1/4 and the original interval guards are restored at the same outer coordinates.

The draft's fresh odd-witness restoration avoids an otherwise genuine parity gap. After the above conclusions, A0=a+2 is even, R and c are odd, and Istar=psi_A0(Rc) is an odd multiple of c². Therefore rho_star=Delta Istar has an odd quotient by c². Choosing Vstar=(-1)^(t+1)Q_t(rho_star²), t=(R−1)/2, gives Vstar=−c modulo fstar² and Vstar=−R modulo c for every odd R, not only R=3 modulo4. The regenerated o,j,r,y restore the exact original odd kernel while keeping k,eta and all native coordinates fixed. This justifies application of the inherited Q41/compiler calibration. The invalid direct expression (2Delta sr−1)/2 is explicitly not used.

## 4. Quintic, full residue interpolation, and completeness order

For pi(x)=(x²+31)(x³+x+1), the discriminant of the irreducible cubic is−31. At each odd prime other than31, either the cubic has a simple root or its irreducible Frobenius3-cycle makes−31 a quadratic residue, supplying a simple quadratic root. At31 the cubic root3 is simple. At2,−31=1 modulo8 has compatible odd square roots to every2-power. Hensel lifting and finite CRT prove intersectivity for every nonzero modulus. The derivative5x⁴+96x²+2x+31 is everywhere positive, and the stated exact positivity certificate proves B>0. The zero-free quadratic-field property used in the initial bootstrap is independent of intersectivity.

The full residue lemma fixes I=psi_A0(n0) divisible by4Nc² before a residue class for T is requested. The valuation bound v_p(I)≥v_p(n0), including the even-A0 doubling formula at2, yields gcd(4n0f,4I²)|4I. The corrected period modulo f² is lambda=4n0f, not4n0. The quadratic-ring identity alpha^(4n0)=1−4f alpha^n0 modulo f² and its f-th power prove this period.

CRT therefore permits L0=R modulo lambda and L0=R−4Ia modulo4I² for every a modulo I. Its index is3 modulo4. The odd Chebyshev quotient identities, including Q_m(X)=(-1)^m(2m+1) modulo4X, give V0=−c modulo f² and V0=−R+4Ia modulo4I². With c=R modulo4 and f odd, the numerator V0+c−f²(c−R) is divisible by4If², and dividing gives T=a modulo I. This proves the complete residue claim with I,f fixed independently of a.

Canonical Budget is greater than q²k²/4≥64, so Budget=1 need not be represented. D=3Budget−4 is positive and2 modulo3, hence nonsquare. Squaring a positive Pell unit gives g²−4Ds²=1 with s>0. The interpolation lemma with N=2s then supplies I divisible by8sc², so r=I/(2sc²) is integral. Only after I,f,r are fixed is an intersective root of pi(a+gamma) modulo I selected. Interpolation supplies T,y in that class. Finally n is the indicated integer norm carrier minus the center shear. The witness order is noncircular; none of these new choices changes the native coordinates or the budget.

## 5. Exact circuit and degree evidence

The independent program imports no author builder or checker and uses explicit exceptions, so optimization cannot disable its checks. It expands all32 formal sign factors and checks the resulting20,349 generic coefficients against each literal DAG. It also checks50,51 and52 front-register cuts, respectively, including the full expanded quintic coefficients; every input and arithmetic gate is live, and all gate references are acyclic. It authenticates the six exact payloads against both centered source copies and every retained source pin.

The radicand degrees are70,182,88,102,94. The uncentered norm therefore has degree at most16·182=2912. For the centered cases put Ua=S(2Q−1)V and Ut=4SLtau. The exact identities are

    4S²Da−Ua²=S²(−V²−4Q+4),
    16S²Dt−Ut²=16S²(1+Ltau k).

Their correction degrees are118 and92, while deg Ua=91 and deg Ut=51. Over the formal Laurent field obtained by scaling all variables by a common parameter, the corresponding root deviations have degrees at most27 and41. This is algebraic degree bookkeeping, not an analytic approximation at actual witnesses.

For auxiliary centering,16 conjugate factors have degree91 and the remaining16 degree51, giving2272. With both centers,16 factors have degree91,8 have degree51, and the last8 have degree47, dominated by the uncentered guard radical. The strong radical has degree44, main degree35 and remaining center degree at most41. Hence the primary degree is at most16·91+8·51+8·47=2240. Its top form is

    (4S_top Q_top V_top)^16 (8S_top Ltau_top)^8
        (64S_top² Dg_top)^4,

which is nonzero. Independently selecting its maximal T power gives coefficient 2^2592·3^1460·beta^1176 at j^1176 w^280 v^296 h^16 s^120 r^112 c^224 T^16, agreeing with the separate author certificate. The exact input-degree cuts, correction identities and this coefficient are verified independently.

As separate exact lower-bound certificates, finite differences on a different fixed-coefficient line modulo1000000007 give nonzero leading coefficients834245546,450453128 and112701963 in degrees2912,2272 and2240. Together with the proved upper bounds these certify exact total degree, not a heuristic numerical guess. Both normal and Python -O receipts retain the line, input hashes and counts.

## 6. Diagnostics, negative controls, and reproducibility

Run from the bundle root:

    python review/eleven/independent_review.py
    python -O review/eleven/independent_review.py

The executable diagnostics check intersectivity modulo every integer1 through512, small Pell valuation instances, and complete interpolation residue quotients for fixed strong witnesses with51-digit and103-digit I values. These finite tests supplement the unbounded proof rather than replacing it.

Negative controls exhibit the failure of4n0 as a period (A=2,n0=2,f=7 gives alpha^8=(1,35) modulo49, while alpha^56=(1,0)); cancellation with even radicands or repeated2-adic weight valuations; the necessity of removing the main root before the parity lemma; failure of the cubic factor alone modulo2; a centered disk point with negative determinant; impossibility of the even guard at Budget=1; nonintegral rational ordinates for arbitrary Pell coefficients; and the invalid old odd-coordinate formula for an even incoming multiplier. They are counterexamples to relaxed shortcuts, not claimed zeros of the full calibrated polynomial.

The completed local theorem is therefore a substantial new tradeoff relative to the cited twelve-integer interpolation precursor, with the explicitly stated inherited mathematical calibration and formalization boundary preserved.
