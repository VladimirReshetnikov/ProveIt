# A first-root CRT carrier: fifteen integers, degree 56, 110 operations

## 0. Result and inherited boundary

The complete polynomial in `specification.json` and `equation.json` has fifteen unrestricted integer variables, exact total degree 56, and 110 live binary arithmetic operations. It has an integer zero if and only if the retained `source/normalized17_degree48.json` does. The latter source's ordinary native/compiler/refutation theorem consequently supplies the same equivalence, provable in ordinary ZFC, between absence of zeros and syntactic Con(ZFC). No consistency proof, global optimum, new encoded object-language ZFC derivation, or new end-to-end proof-assistant certificate is claimed.

The fixed coefficients are the identical six authenticated source34 integers, with MF already shifted. The new step is to let the already-present first Pell square root carry both the scale congruence and the quadratic main projection. There is no radical norm in the final polynomial, no extra quantified register, and no private positivity convention.

## 1. Literal polynomial

All fifteen coordinates are unrestricted integers:

    j,C,z,h,r,v,w,T,c,n,f,y,p1,p2,p3.

The following are polynomial abbreviations, not variables:

    J=6j+1, qm=beta J, q=qm+1, W=12w+4,
    X=qW, Y=qv, F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-Yk, L=EYk,
    I=(2r+1)c^2, Q=Delta(f^2-1), V=f^2(cT-R)-c,
    M=2q^2, U=MH, Klo=2X^2-3Xc-2,
    Z=Un+M Klo+H(v-q^2),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=k^2(q^2-Derr)-4q^2 eta^2,
    pos=1+p1^2+p2^2+p3(p3+1).

Set

    A=Z^2+(2Z-Uk)UL-U^2,
    B=f^2-Delta I^2-1,
    Caux=V^2-(Q-1)y(2V+y)-1,
    G=budget-pos.

The single equation is

    P=A^2+B^2+Caux^2+G^2=0.

Every abbreviation is fully specified by a division-free DAG. The name Caux is unrelated to the free native coordinate C. All divisions used below occur only in proofs of integral witness maps.

## 2. Early monic integrality and coprime CRT

The authentic beta is odd and is 1 modulo 3. Hence q is even, q=2 modulo 3, and q is nonzero. Also H is odd and H=3 modulo q. Therefore H and M=2q^2 are coprime, and U=MH is nonzero. These facts hold on every signed assignment before any row or guard is used.

At an integer zero all four rows vanish. Put t=Z/U in Q. The first row gives

    t^2+(2t-k)L-1=0,

which is monic over Z. The rational-root theorem implies t is an integer. Equivalently, (t+L)^2=1+L(L+k), and a rational square root of an integer is integral. No real-root separation, positivity, magnitude, or nonzero-v hypothesis enters this step.

Thus U divides Z. Reduction modulo M and H, with coprimality, gives

    v=q^2(2v0+1),    v0=(v-q^2)/M in Z,
    H divides Klo.

In particular v is nonzero and Y=(2v0+1)q^3 has exactly the old scale. Let

    K=X(X+2ac)-1.

The exact identity 2K-Klo=HXc, together with odd H, gives H divides K. Also the integral centered first coordinate t satisfies the original first Pell row. This licenses the cubic scale before the signed Pell bootstrap and before recovering the omitted main root.

## 3. The budget gives precisely the signed hypotheses needed

Since pos is strictly positive for all integer triples, G=0 gives budget>0. Exactly as in `source/CENTERED_BUDGET_PROOF.md`, Section 2, this implies

    q,k nonzero, Derr<q^2, |eta/k|<1/2,
    F,C,alpha=q-F-C have q's common strict sign,
    |k|(|Y|-1)<|c|<|k|(|Y|+1), sign(c)=sign(kY).

Here cone_A,cone_B are at least 8. The source's native packing estimates now give, with q0=|q| and x=|X|,

    q0>=16, q0(q0^2-1)<R<q0^4-2,
    x>=4q0>=64, m=|Y|>=q0^3, |E|>3R+1.

In particular c is nonzero and large. Write c0=|c|, B0=|a+2| and I0=|2r+1|c0^2. Then B0>=3, Delta=B0^2-1, I0>=c0 and, from B=0,

    f0=|f|, f0^2-Delta I0^2=1, f0>2I0.

These deductions use only common signs and the weaker centered interval. They do not assume eta>0 or eta(k-eta)>0. The copied centered-budget proof explicitly verifies that these are the exact interval and sign hypotheses used by the signed rank argument; positivity of eta is recovered only later.

## 4. Recover the omitted main Pell square before projection

Let S=Delta I0. The strong row gives Q=S^2, with S>=2. Put y0=|V+y|. The auxiliary row is exactly

    S^2 V^2-(S^2-1)y0^2=1.

Therefore V is nonzero, and the standard Pell classification gives

    S|V|=chi_S(ell), y0=psi_S(ell)

for some positive integer ell. Since S divides chi_S(ell), reduction of the recurrence modulo S forces ell odd. For ell=2h+1, the integer polynomial identity

    chi_Z(2h+1)=Z Q_h(Z^2),
    Q_h(1-B0^2)=(-1)^h psi_B0(2h+1)

and S^2=Delta(f0^2-1) give

    psi_B0(ell)=+c0 or -c0 modulo f0.

Here V=-c modulo f0, so both signs of V and c are accounted for. Classify the strong pair as f0=chi_B0(m0), I0=psi_B0(m0). Folding the index ell modulo 2m0 and reflecting it about m0 reduces its ordinate modulo f0, up to sign, to psi_B0(p), 0<=p<=m0. Since

    0<=psi_B0(p)<=I0,    I0+c0<=2I0<f0,

the congruence forces psi_B0(p)=c0. Thus p>=1 and 1+Delta c^2 has an integer square root.

This is the main-root recovery from Section 2 of `source/SIGNED_QUADRATIC_PROOF.md`, restated to make its order explicit. It does not use the missing gamma or assume a main congruence.

## 5. Signed rank and whole-product projection

The first Pell row and the main ordinate recovered in Section 4 give

    |k|=2 psi_P(n0), c0=psi_B0(p),
    P=|2XY^2+1|>B0, p>n0>=24.

The signed first-index congruence and packing bounds are the same as in `source/BUDGET_PROOF.md`, Section 3. The normalized strong-rank lemma from `source/PROOF.md`, Section 2, gives c0|m0 and m0>2p. The auxiliary congruences

    V=-c modulo f0,    V=-R modulo c0

hold because f^2=1 modulo c0. The signed auxiliary step-down consequently gives p=R. The negative first-index branch is impossible, and the no-wrap estimate gives 2n0=R+1. All these steps precede any use of a main projection.

For completeness, the quantitative projection bound used here is the one proved in `source/SIGNED_QUADRATIC_PROOF.md`, Sections 4--5. With R=2s+1 and s>=24 it gives

    m>(x-3)^s/2-1,
    |H|>x(x-3)^s>2^(2R+2)x^2.

Its hypotheses are only the signed first/main classifications, normalized strong rank, recovered cubic scale, packing bounds, |c/k|<m+1, and sign facts above. The centered budget supplies all of them; this does not invoke eta(k-eta)>0. The original source explicitly identifies that weaker interval as sufficient.

Let A0=a+2 and sigma=sign(c). Since R is odd, c=sigma psi_A0(R). The signed polynomial Pell congruences modulo odd H give

    chi_A0(R)-a psi_A0(R)=2^R modulo H,
    chi_A0(R)+a psi_A0(R)=2^(-R) modulo H.

Put x0=sigma X. The already-proved H|K implies

    H divides (x0-2^R)(2^R x0+1).

The absolute value of this entire product is less than 2^(2R+2)x^2<|H|. Hence the product is zero. Its second factor is odd and cannot be zero, so x0=2^R. No cancellation of a nonunit modulo a composite H is made.

Set d=sigma chi_A0(R). Then d^2=1+Delta c^2 and

    H divides d-X-ac.

Thus gamma=(d-X-ac)/H is an integer and restores the omitted main row.

## 6. Complete two-way maps to the seventeen-coordinate source

### New to old

Keep f,h,r,w,T,c,y and the three private Pos coordinates. Set

    J3_old=2j, F_old=F, alpha_old=q-F-C,
    z_old=z, v_scale_old=(v-q^2)/M,
    tau_old=Z/U, gamma_old=(d-X-ac)/H.

All are integers by the preceding proof. The source's native transport row vanishes identically by the definition of F. Its R agrees by the exact identity

    (q-1)(q-F)+(q-F-C)=q(q-F)-C.

Its first, strong, centered auxiliary and budget rows are precisely the restored rows above; its main row vanishes by the selected d. Consequently this is a literal zero of `source/normalized17_degree48.json`. Only now is its complete centered-budget/native/compiler/refutation theorem invoked. In particular the source handles late positive eta recovery, using its nearest-half-binomial theorem.

### Old to new

Take any integer zero of the retained seventeen-variable source. Its proved signed power theorem gives X=2^R and hence q even. As beta is odd, Jnative=3J3_old+1 is odd, so J3_old is even; set j=J3_old/2. Set

    C=q-F_old-alpha_old,  v=q^2(2v_scale_old+1),

and retain z,h,r,w,T,c,f,y,p1,p2,p3. The source's transport row ensures our computed F equals F_old. If d=X+ac+H gamma_old, its main row gives d^2=1+Delta c^2. The identity

    (X+ac)^2-(1+Delta c^2)=K-Hc^2

therefore gives H|K, hence H|Klo. Choose the unrestricted integer

    n=tau_old-Klo/H-v_scale_old.

Then Z/U=tau_old, so the carrier row vanishes. All other rows are unchanged. This restores a new zero from every old zero, not merely from canonical witnesses.

These maps establish equivalence of integer-zero existence, not a pointwise equality of the complete polynomials or a bijection of zero sets.

## 7. Exact degree and evaluator cost

The register degree bounds are

    q:1, X:2, Y:2, F:2, R:5, k:5, a:4, H:4,
    Delta:8, L:11, I:3, Q:10, V:7, U:6, Klo:4, Z:7.

The four rows have degree bounds 28,14,18,16. The first row has unique degree-28 leading contribution -U0^2 k0 L0. Writing

    q0=6 beta j, X0=12q0 w, Y0=q0 v,
    U0=8q0^2 X0Y0,

and selecting the h term k0=hX0Y0+R0 shows

    [j^30 w^10 v^12 h^4] P = 2^62 3^40 beta^30 > 0.

The exponent sum is 56. No other squared row has degree 56. Thus 56 is the actual degree after all six enormous coefficient ports are fixed, not a generic or syntactic estimate.

The DAG contains 110 live binary arithmetic operations: 63 multiplications, 24 additions, and 23 subtractions. Literal scalar multiplication and squaring are charged. It declares exactly fifteen integer inputs and six fixed coefficients; named registers are free aliases for already-counted nodes. Independent exact register-cut checks, source/constant pins, attained-degree tests and bad-mutation rejection are provided separately. They certify transcription and finite algebra, not the inherited unbounded compiler theorem.
