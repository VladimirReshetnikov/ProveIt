# Normalized centered budget: 17 integers, degree48, 110 gates

## 1. Result and semantic boundary

The literal packet `normalized17_degree48.json` gives a single ordinary integer polynomial in 17 unrestricted integer variables, exact degree48. Its six residuals are squared and summed. The complete fixed compiler tuple and two determinant-scale numerals are unchanged from `normalized18_degree88.json`; they require 615883 uncompressed numeral bytes. No new scale or independently adjustable coefficient is introduced.

This composes the normalized congruence packing proved in `PROOF.md` with the centered sign-budget theorem in `upstream/CENTERED_BUDGET_PROOF.md`. The latter is the complete source for the centered half-binomial and guard-restoration argument, not an unproved claim that a disk inequality implies the old determinant inequality. In fact the new budget need not imply that determinant. Soundness restores the pinned centered-budget eighteen-variable source, and then its original common-sign Q41 interface. Completeness reselects normalized strong and auxiliary witnesses in the same canonical compiler family. Therefore the new polynomial has a zero exactly when there is a finite syntactic ZFC refutation, under the same explicit inherited source34 compiler/calibration theorem. This does not assert a pointwise lift to the determinant-guard parent, nor a new proof-assistant certificate.

## 2. Literal polynomial

Use the seventeen variables

    J3,F,alpha,z,f,h,r,v_scale,w3,tau,y,gamma,T,c,
    pair_pos1,pair_pos2,pair_pos3.

Put, as ordinary polynomial abbreviations only,

    qm=beta(3J3+1), q=qm+1, W=12w3+4, X=qW,
    Y=(2v_scale+1)q^3, E=XY, a=E+Y,
    C=q-F-alpha, H=4a+3, Delta=a^2+H,
    R=(qm(q-F)+alpha)(q^2-1)+(MC+q MF)(3J3+1),
    k=R+1+hE, eta=c-kY, L=EYk,
    V=f^2(cT-R)-c, Q=Delta(f^2-1),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=k^2(q^2-Derr)-4q^2 eta^2,
    pos=1+pair_pos1^2+pair_pos2^2+pair_pos3(pair_pos3+1).

The six residuals are

    B0 = tau^2+(2tau-k)L-1,
    B1 = (X+ac+gamma H)^2-Delta c^2-1,
    Bt = (K0+W)C-F-z qm,
    Ns = f^2-Delta((2r+1)c^2)^2-1,
    Ba = V^2-(Q-1)y(2V+y)-1,
    Bg = budget-pos.

The final polynomial is B0^2+B1^2+Bt^2+Ns^2+Ba^2+Bg^2. All expressions are completely inlined in the packet. The two centered roots restore by integral polynomial translations

    tau_old=tau+L,       y_old=y+V.

Their exact identities are

    (tau+L)^2-L(L+k)-1 = B0,
    QV^2-(Q-1)(y+V)^2-1 = Ba.

Both substitutions are coordinate bijections for fixed remaining arithmetic variables. Thus these centerings impose no extra residue, sign, or canonical hypothesis. The shared aliases qm=q-1, a=E+Y, Delta=a^2+H and L=EYk merely reduce evaluator cost; they denote the same polynomials as before.

## 3. Soundness and the precise order of deductions

At a zero, budget=pos>0. With A=cone_A,B=cone_B>=8, the elementary budget argument gives

    q,k nonzero,
    (AF-q)^2+(BC-q)^2<q^2,
    0<F/q+C/q<2/A+2/B<1,
    F,C,alpha all have q's nonzero sign,
    |eta/k|<1/2.

The sign assertions follow from 0<AF/q<2 and 0<BC/q<2 and are valid also for q<0. The last assertion and c=kY+eta imply

    |k|(|Y|-1)<|c|<|k|(|Y|+1),
    sign(c)=sign(kY).

These are exactly the weaker interval and sign facts needed in the source's signed rank/bootstrap calculation. They do not assert eta>0 yet.

Translate the roots as above. Up through the first/main index bounds, the centered-budget proof's Section3 applies unchanged: with U=|X|,Z=|Y|,K=|k|,B0=|a+2| and c0=|c|, one obtains U>=64,Z>=4096, K=2psi_P(n), c0=psi_B0(p), p>n>=24, c0>2p,2R. Replace that proof's ordinary-strong rank paragraph by the normalized rank lemma proved in `PROOF.md`, Section2. Because Ns=0,

    |f|^2-Delta(|2r+1|c0^2)^2=1,
    |f|=chi_B0(m), pc0|m, m>2p,
    Q=(Delta |2r+1|c0^2)^2.

The packed V gives V=-c modulo |f| and V=-R modulo c0. Therefore the same signed auxiliary step-down gives p=R. This uses neither oddness of the auxiliary square root nor the still-unproved eta>0. All remaining hypotheses of the signed power-recovery paragraph have been checked, so it yields X=sign(c)2^R, R odd. The affine residue X=2 modulo3 forces

    X=2^R.

As q divides X and |q|>=16, q is even. Therefore Y,a are even and Delta is odd. Now the following proof-only restoration is integral:

    r_old=(Delta(2r+1)-1)/2,
    o=f(cT-R),
    j=f^2 T-Delta(2r+1)^2 c^3 R-1.

The universal identities already checked in `PROOF.md` show

    V=fo-c=cj-R,
    k=1-V+jc+hE,
    ((2r_old+1)c^2)^2=Delta(f^2-1).

Together with y_sign_parent=y+V and tau_sign_parent=tau, these yield an actual zero of `upstream/centered_budget18_degree48.json`, after renaming the three private Pos coordinates. The first root in that source is already centered; no second translation of tau is performed. Its budget is unchanged, because F,C,q,k,eta are unchanged. Its auxiliary norm agrees because ((2r_old+1)c^2)^2=Q.

The centered-budget source theorem can now be applied. Its Section4 proves the uniform Pell ratio estimate and centered half-binomial extraction that recover eta>0 and k-eta>0. Its Section5 restores the original Q41 positivity guards and square coordinate and invokes the authentic compiler/calibration theorem. Hence a finite refutation exists.

This order avoids both possible circularities: the ordinary odd-scale source is not invoked until Delta is proved odd, and positivity of eta is not invoked until the centered half-binomial theorem proves it. It also does not assume budget>0 implies the old determinant>0.

## 4. Completeness using the same canonical family

Start with the authentic canonical family of the centered-budget theorem. Its same native coefficient witnesses satisfy Derr<=q^2/2, and its explicit half-binomial Y gives 0<eta/k<1/4. Thus budget>q^2 k^2/4>0 before any new private Pos representation is chosen. These properties survive the permitted canonical rank tuning, as the source proves.

Keep all outer coordinates. In particular q is even, A=a+2 is even, R=3 modulo4 and c=psi_A(R) is odd. Select

    f=chi_A(Rc), I=psi_A(Rc).

The proof in `PROOF.md`, Section4, gives c^2|I and odd I/c^2, hence r=(I/c^2-1)/2 is integral. The generic positive auxiliary reconstruction proved there then supplies T and y_old with

    V=f^2(cT-R)-c,
    QV^2-(Q-1)y_old^2=1.

Set y=y_old-V and tau=tau_old-L. Both are integers and satisfy the two centered rows identically. None of these fresh Pell witnesses changes F,C,q,k,eta, the native transport, the main norm, or the budget. A three-square Pos representation of that positive budget supplies pair_pos1,pair_pos2,pair_pos3. All six residuals vanish.

Thus completeness does not require a stronger arbitrary-source congruence for f or y, and does not splice the canonical witnesses of different coefficient tuples.

## 5. Degree48 and literal binary evaluator

The six residual degrees are bounded respectively by 24,14,2,18,21,24. Let

    q*=3 beta J3, X*=36 beta J3 w3,
    Y*=54 beta^3 J3^3 v_scale, k*=h X* Y*.

The first row's leading form is -h^2 X*^3 Y*^4. The budget row's leading form is -4h^2 q*^2 X*^2 Y*^4. Their squares have different w3 exponents. No other row has degree24. Hence

    [h^4 w3^6 v_scale^8 J3^30] P17
        =2^20 3^36 beta^30>0.

This proves exact degree48 on the authentic fixed coefficient slice.

The literal common-subexpression DAG `normalized17_degree48_dag.json` evaluates this exact polynomial in **110 live binary operations: 59 multiplications, 28 additions, and 23 subtractions**. Multiplication by every literal and fixed numeral is charged. The six fixed coefficient numerals and small integer literals are leaves; no variable or numerical operation is hidden in a register definition. This is a reproducible evaluator cost, not an arithmetic-circuit lower bound.

`check_budget.py` is independent of the builder and uses exact sparse integer-polynomial arithmetic. It validates every named DAG register at a direct-dependency cut, each residual at register cuts, and the sum-of-squares finalizer at residual cuts. Induction through this acyclic graph proves equality to the completely inlined polynomial without expanding the huge final sum. All 110 gates and all declared input leaves are verified live. The exact degree coefficient is checked separately by homogeneous-component arithmetic.

Run `python build_budget.py`, `python check_budget.py`, `python -O check_budget.py`. The source18 packing checker remains runnable separately. Finite Pell diagnostics supplement, but do not replace, the unbounded proofs and inherited native compiler/calibration boundary.
