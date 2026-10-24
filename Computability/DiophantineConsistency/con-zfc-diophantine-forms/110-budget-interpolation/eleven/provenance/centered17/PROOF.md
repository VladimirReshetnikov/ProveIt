# Normalized strong-Pell congruence packing: 18 integers, degree 88

## Result and exact inherited boundary

The packet `normalized18_degree88.json` specifies a single, fixed ordinary integer polynomial in 18 unrestricted integer unknowns. It is the sum of the squares of six explicitly inlined residuals and has exact total degree 88. Its fixed ports are the complete source34 mixed-parity-unrounded-1064921 tuple beta, K0, MC, MF, together with the already-established determinant scales cone_A=2^1113 and cone_B=2^666104. MF is already shifted. No coefficient is reselected and no compact44 compiler theorem is applied to this different tuple.

The polynomial has an integer zero if and only if the pinned wave11 nineteen-integer polynomial does, equivalently if and only if there is a finite syntactic ZFC refutation under the parent's explicit compiler/calibration theorem. Thus, relative to that same ordinary mathematical theorem, ZFC proves that absence of an integer zero is equivalent to Con(ZFC). This is not a consistency proof, a newly kernel-checked compiler theorem, a global minimality claim, or a pointwise equivalence preserving every parent witness.

The exact inherited source is `upstream/joint19_degree88.json`. Its source34 signed power argument and simultaneous canonical completeness are copied in `upstream/WAVE11_GUARDS_PROOF.md`, Sections 4 and 5, and `upstream/RESIDUE_PROOF.md`. The new proof below replaces the ordinary strong-rank step with a proved normalized rank lemma, then restores the original odd-scale source. The generic positive auxiliary lemma reproduced below is coefficient-independent. Its use does not import the different compiler tuple discussed elsewhere in `upstream/package61_report.tex`.

## 1. Literal equation

The unknowns, all in Z, are

    J3,F,alpha,z,f,h,r,v_scale,w3,tau,y,gamma,T,c,
    pair_root,pair_pos1,pair_pos2,pair_pos3.

Define the following polynomial abbreviations; they are not extra unknowns:

    q=beta(3J3+1)+1, W=4(3w3+1), X=qW,
    Y=(2v_scale+1)q^3, E=XY, a=(X+1)Y,
    C=q-F-alpha, H=4a+3, Delta=a^2+4a+3,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)(3J3+1),
    k=R+1+hE, eta=c-kY, zeta=k-eta,
    V=f^2(cT-R)-c, Q=Delta(f^2-1),
    d=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    b=eta zeta, Ppos=1+pair_pos1^2+pair_pos2^2+pair_pos3(pair_pos3+1).

The six residuals are

    A0 = tau^2-E(c-eta)(k+E(c-eta))-1,
    A1 = (X+ac+gamma H)^2-Delta c^2-1,
    At = (K0+W)C-F-z(q-1),
    Ns = f^2-Delta((2r+1)c^2)^2-1,
    Aa = QV^2-(Q-1)y^2-1,
    Ag = d b-(pair_root^2-d-b+1)^2-Ppos.

The defining polynomial is A0^2+A1^2+At^2+Ns^2+Aa^2+Ag^2. It contains no division, variable exponent, positivity convention, hidden register, or quantified coefficient.

The old coordinates o and j were used to impose V=fo-c=cj-R. A normalized Pell pair makes it possible to impose both congruences using one T. The stronger modulus f^2 in V is needed for canonical completeness; it is not asserted that every old auxiliary witness already had this stronger modulus.

## 2. Elementary Pell facts used by the new step

For A>=2 write Delta=A^2-1 and define chi_A(n),psi_A(n) by

    (A+sqrt(Delta))^n=chi_A(n)+psi_A(n)sqrt(Delta).

Equivalently both obey u_(n+2)=2A u_(n+1)-u_n, with chi initial values 1,A and psi initial values 0,1. Integer coefficients, the Pell norm, addition identities, and composition all follow by multiplication in Z[sqrt(Delta)].

For clarity the classification and divisibility used here are not being inferred from finite tests. The least positive integer-coordinate norm-one unit for discriminant A^2-1 is A+sqrt(Delta): any positive ordinate is at least 1, forcing its abscissa to be at least A. Given another positive unit, divide by a suitable power of this least one until the quotient lies in [1,A+sqrt(Delta)). The quotient still has integer coordinates and norm one. If it exceeded 1 its two coordinates would be positive, contradicting minimality. Thus every positive solution is (chi_A(n),psi_A(n)) for a positive integer n. The same argument for discriminant u(u+1), u>=1, gives least unit 2u+1+2sqrt(u(u+1)): ordinate 1 is impossible since u(u+1)+1 lies strictly between u^2 and (u+1)^2; ordinate 2 gives abscissa 2u+1. This proves the consecutive-product classification used by the source.

The norm gives gcd(chi_A(n),psi_A(n))=1. Addition gives

    psi_A(n+t)=chi_A(n)psi_A(t)+psi_A(n)chi_A(t).

Consequently gcd(psi_A(n),psi_A(n+t))=gcd(psi_A(n),psi_A(t)); Euclid's algorithm proves

    gcd(psi_A(m),psi_A(n))=psi_A(gcd(m,n)).

Strict growth follows from the positive-unit formula. In particular psi_A(p)|psi_A(m) implies p|m.

### Normalized rank lemma

Suppose c0=psi_A(p)>2 and positive f,I satisfy f^2-Delta I^2=1 and c0^2|I. Then f=chi_A(m), I=psi_A(m) for some m, and pc0|m, hence c0|m and m>2p.

Indeed classification supplies m; strong divisibility gives p|m. Write m=pv and D=chi_A(p). Composition gives I=c0 psi_D(v). Since D^2-1=Delta c0^2, the binomial expansion in Z[sqrt(D^2-1)] gives

    psi_D(v)=v D^(v-1) modulo c0.

As D is invertible modulo c0 and c0 divides psi_D(v), c0|v. This proves the lemma. No oddness of I/c0^2, D, Delta, or the auxiliary square root is needed for this implication.

### Odd quotient identities and auxiliary recovery

For nonnegative v there are integer polynomials Q_v(x) with

    chi_Z(2v+1)=Z Q_v(Z^2),
    Q_v(0)=(-1)^v(2v+1),
    Q_v(1-A^2)=(-1)^v psi_A(2v+1).

Here Q_0=1, Q_1=4x-3, and Q_(v+1)=(4x-2)Q_v-Q_(v-1). The odd subsequences of the Pell recurrence prove all three identities, including both evaluations. These identities are valid polynomials, not facts restricted to sampled integer inputs.

Let R>=3 with R=3 modulo4, c=psi_A(R), and f,I>0 satisfy f^2-Delta I^2=1 and c|I. Put S=Delta I and Q=S^2. Write R=2v+1 with v odd. Then

    Vstar=chi_S(R)/S=Q_v(S^2), ystar=psi_S(R)

are positive integers with Q Vstar^2-(Q-1)ystar^2=1. Moreover S^2=Delta(f^2-1)=1-A^2 modulo f^2 and c|S, so the quotient identities give

    Vstar=-c modulo f^2, Vstar=-R modulo c.

The strong norm gives f^2=1 modulo c, hence gcd(c,f^2)=1. Therefore

    T=(Vstar+c+R f^2)/(c f^2)

is a positive integer, and Vstar=f^2(cT-R)-c. This proves the required auxiliary completion for every such f,I. No stronger congruence on an arbitrary preexisting y is assumed.

## 3. Soundness on every signed zero

At a zero all six residuals vanish. The exact joint-sign lemma in the copied wave11 joint proof gives d>0 and eta zeta>0. Briefly, the positive Ppos forces d b>(pair_root^2-d-b+1)^2, so d,b have the same nonzero sign; if both were negative, the square would be larger than d b. Thus both are positive. The determinant argument gives that F,C,alpha have the same nonzero sign. These arguments require no source equations or prior orientation.

Everything in the source signed-power proof before its strong-rank paragraph is unchanged. In particular, writing q0=|q|, U=|X|, Z=|Y|, M=|E|, K=|k|, c0=|c|, B=|a+2|, P=|2XY^2+1|, its explicit estimates give

    q0>=16, q0(q0^2-1)<R<q0^4-2,
    U>=4q0>=64, Z>=q0^3>=4096, M>3R+1,
    K(Z-1)<c0<K(Z+1), B>q0^4>R, P>B>=2.

The source's first and main Pell classifications give K=2psi_P(n), c0=psi_B(p), and p>n. The first-index congruence gives either n>=(R+1)/2 or n>R; in particular p>n>=24 and c0>2p,2R. These are deductions from A0,A1 and the guards, not assumptions about canonical witnesses.

Now put i=2r+1. The new normalized norm gives

    |f|^2-(B^2-1)(|i|c0^2)^2=1.

The normalized rank lemma applies with I=|i|c0^2 and gives |f|=chi_B(m), pc0|m, and m>2p. Also

    Q=Delta(f^2-1)=Delta^2 i^2 c^4=S^2,
    S=Delta |i|c0^2>=2, c0|S.

The packed V gives V=-c modulo |f|. Since f^2=1 modulo c0, it also gives V=-R modulo c0. Thus all hypotheses of the source's signed auxiliary-index step hold, with this S. The auxiliary step requires S>=2 and c0|S, not odd S. To recall its exact mechanism: Pell classification gives an odd index ell with |V|=Q_v(S^2); the two quotient evaluations above give psi_B(ell)=+/-c0 modulo |f| and ell=+/-R modulo c0. Squaring the first congruence and using chi_B(2ell)=1+2Delta psi_B(ell)^2 gives chi_B(2ell)=chi_B(2p) modulo chi_B(m). The signed abscissa step-down proved in `upstream/package61_report.tex`, Lemma `lem:stepdown`, yields ell=+/-p modulo m. Since c0|m and 0<p,R<c0/2, these congruences force p=R.

For explicitness the step-down itself uses only addition and growth: modulo chi_B(m), shifting an index by 2m or reflecting about m changes the sign. Reduce to a signed chi_B(s), 0<=s<=m. The negative sign cannot equal chi_B(k), 0<k<m, since 0<chi_B(s)+chi_B(k)<=2chi_B(m-1)<chi_B(m); the endpoint s=m is zero modulo the modulus. The positive sign gives s=k by strict growth. Thus the original index is +/-k modulo2m.

The remainder of the source signed-power argument is unchanged, because its only strong-Pell input was precisely the rank/congruence conclusion just established. It yields R odd and X=e 2^R with e=sign(c). Its quantitative step is Z>2^R, obtained from the first/main Pell growth ratio and the explicit inequalities U>=64, Z>=4096. The main-root congruence modulo H then selects X=e2^R. Finally beta=1 modulo3 gives q=2, W=1, X=2 modulo3. Since R is odd, e=-1 is excluded. Hence

    X=2^R.

We now, and only now, restore the ordinary odd-scale parent. Since q|X and |q|>=16, q is even. Therefore Y and a=(X+1)Y are even, Delta is odd, and

    r_old=(Delta(2r+1)-1)/2

is an integer. Put

    o=f(cT-R),
    j=f^2 T-Delta(2r+1)^2 c^3 R-1,
    I_old=Delta(2r+1)c^2=(2r_old+1)c^2.

For N=Ns the universal polynomial identities are

    V+c-fo=0,
    cj-V-R=R N,
    I_old^2-Delta(f^2-1)=-Delta N,
    k_old:=1-V+jc+hE=k+R N.

Thus these are exact old source coordinates at N=0. The original auxiliary row is the new auxiliary row minus Delta N(V^2-y^2), hence vanishes too. All other rows, eta and the joint guard agree. Restoring these two removed coordinates and r_old therefore gives an actual zero of the pinned nineteen-integer parent. Its authentic compiler/calibration theorem gives a finite refutation.

There is no circular use of the old odd-scale theorem: normalized rank and signed auxiliary recovery occur first; even q and odd Delta follow from the recovered power; only then is the ordinary odd-scale source restored.

## 4. Simultaneous canonical completeness

Given a finite refutation, take the same canonical source34 family used in `upstream/WAVE11_GUARDS_PROOF.md`, Section5. It simultaneously has q=2^t with t odd, R=3 modulo4, X=2^R, c=psi_(a+2)(R), the odd Y scale, both affine residue restrictions, and the determinant inequality. Its determinant bounds survive every allowed rank-tuning dummy change, as that source proves. Thus no incompatible canonical families are spliced together.

Keep these outer coordinates, including h,k,c,a,tau,gamma and the native compiler witnesses. Since q is even, A=a+2 is even. Put p=R. Modulo2 the recurrence gives psi_A(odd)=1, so c is odd; chi_A(odd)=0, so D=chi_A(p) is even. Choose

    m=pc, f=chi_A(m), I=psi_A(m).

Composition gives I=c psi_D(c). Since D^2-1=Delta c^2, the binomial congruence from Section2 gives psi_D(c)=c D^(c-1)=0 modulo c. Hence c^2|I. Both m and c are odd, so I=psi_A(m) is odd and the integer I/c^2 is odd. Therefore

    r=(I/c^2-1)/2

is an integer, and Ns=0. This supplies the required normalized odd scale while changing no outer source coordinate.

Apply the coefficient-independent auxiliary completion from Section2 to this selected f,I and R. It gives T>0 and y>0 satisfying Aa=0 and V=f^2(cT-R)-c. These choices still change none of k,eta,zeta or the determinant. The inherited first/main norms and native transport therefore continue to hold. Both d and eta zeta are positive, so the joint-sign representation supplies pair_root and the three Ppos coordinates, exactly as in the source proof. All six residuals vanish.

The only divisions in this paragraph are proof-only witness-selection formulas whose integrality has been proved. The literal polynomial still contains only additions, subtractions, multiplications and fixed nonnegative powers.

## 5. Exact degree and coefficient binding

The residual degree bounds, checked from the fully inlined ordinary polynomials, are 34,14,2,18,26,44. In particular V has degree6, Q degree14, k degree7, eta degree11. The top forms are

    X_top=36 beta J3 w3,
    Y_top=54 beta^3 J3^3 v_scale,
    eta_top=-h X_top Y_top^2
           =-2^4 3^8 beta^7 h J3^7 w3 v_scale^2.

Since zeta=k-eta has top form -eta_top, b_top=-eta_top^2. Consequently Ag has top form -eta_top^4, and its square is the only degree88 contribution. Therefore the coefficient of

    h^8 w3^8 v_scale^16 J3^56

in the final polynomial is exactly 2^32 3^64 beta^56>0 on the authentic fixed tuple. This proves exact degree88, not merely a gate-degree upper bound.

The fixed tuple and determinant scales are byte-for-byte copied from the wave11 binding and authenticated by compressed/raw SHA-256, bit lengths and integer recipes in the checker. The binding retains two unused cone alternatives for source authenticity, but the packet declares exactly six fixed ports, not eight.

## 6. Reproduction and scope of certificates

Run `python build.py`, `python check.py`, and `python -O check.py`. The independent checker does not import the builder, SymPy, or an external algebra system. It verifies literal closed declarations, all six independently reconstructed expressions, universal restoration identities in an exact sparse integer-polynomial ring, exact homogeneous leading components, the nonzero selected degree88 coefficient, byte-exact source pins and coefficient payloads. Modular canonical-parity diagnostics and a few actual auxiliary completions are supplementary only.

The unbounded proof is Sections2–4 together with the precisely named inherited signed-power, simultaneous canonical, native compiler, and finite-refutation calibration theorems. Finite checking is not offered as a substitute for those theorems. No Pell classification, strong divisibility, or new canonical flexibility is being inferred from enumeration.
