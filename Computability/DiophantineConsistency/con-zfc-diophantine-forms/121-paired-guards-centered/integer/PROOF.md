# Two-group coprime projection over eleven unrestricted integers

## Result and boundary

The five nondominated endpoints here have (exact total degree, live binary arithmetic operations)

- (688,124), (728,120), (820,119), (964,118), (1632,112).

Every endpoint has exactly eleven unrestricted integer unknowns and the same six completely instantiated numeral coefficients as the preceding package. The 820/119 and 964/118 equations are new two-group coprime reductions. The other three are exactly the preceding mathematical polynomials, with smaller evaluators. No ten-integer construction, degree improvement below 688, global optimum, proof of consistency, new Lean/Rocq certificate, or new internal object-ZFC derivation is asserted.

The equivalence with finite syntactic ZFC refutation uses the same retained ordinary native/compiler/refutation calibration as the preceding package. Every unbounded lemma used below is identified and retained locally. The finite circuit, coefficient, degree, and identity audits do not themselves certify these unbounded theorems.

## 1. Common explicit definitions

The independent variables are j,C,z,h,r,v,w,T,c,n,s, all ranging over Z. The fixed integer payloads beta,K0,MC,MF,cone_A,cone_B are authenticated in coefficients/BINDING.json, with their finite reconstruction in coefficients/recipe/. In particular beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104, and MF is already shifted.

Define polynomial abbreviations

    J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=(2v+1)q^3,
    E=XY, a=E+Y, A=a+2, H=4a+3, Delta=A^2-1=a^2+H,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2,
    D=3Budget-4, ell=XY^2, L=ell k,
    Dt=1+L(L+k)=1+ell(ell+1)k^2,
    Dg=1+4D Dt s^2,
    P=Dt Dg=Dt+D(2s Dt)^2,
    Dm=1+Delta c^2.

Dg is useful for proofs but is not evaluated as a separate circuit register. The second expression for P saves a gate when 2s is already used elsewhere.

For the NEW two-group pair define

    Ib=s r c^2 Dm, I=2A Ib=2s r c^2 A Dm,
    Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1, Da=delta Cy,
    K=X(3c-2X)+2, S=I H^5,
    zc=HT+K, Ac=(zc^2+3H^2)(zc^3-19H^3), Z=Sn-Ac.

No displayed abbreviation introduces a variable. The two new equations are

    Nint = (Z^2-S^2 Df Da-4S^2 P)^2-16S^4 Df Da P = 0,

    Nrat = (delta Z^2+4delta S^2 P-S^2 Df Cy)^2
           -16delta^2 S^2 P Z^2 = 0.

They are literal integer polynomials. Nrat has no actual division. The first equation is the product of all four conjugates

    Z +/- S sqrt(Df Da) +/- 2S sqrt(P).

For delta !=0, the second is delta^2 times the product of all four conjugates

    Z +/- S sqrt(Df Cy/delta) +/- 2S sqrt(P).

These are explanatory identities, not extra operations or implicit witnesses. The checker proves both identities by exact free-ring expansion, including the identity between the two denominator-clearing arrangements.

## 2. Nonzero bootstrap and positivity

The fixed payload and affine restrictions give q even, q=2 mod3, |q|>=16, |X|>=64, |Y|>=4096, |a|>=63*4096. Therefore A and H are nonzero, H odd, and Delta>1. We have Dt>=1 because ell(ell+1)>=0. Also Dm>=1 and Df>=1.

The elementary intersective polynomial

    pi(t)=(t^2+3)(t^3-19)

has no rational root and has a root modulo every positive integer. Its full prime-power/CRT proof, including p=2,3,19, is retained in source/PRIME_TWELVE.md Section2. For nonvanishing alone, t^2+3 has no real root and t^3-19 has no rational root.

If I=0, then S=0, Q=0, delta=-1, and both new equations specialize to Ac^4. But Ac=H^5 pi(T+K/H) is nonzero. Thus I!=0 at every zero. Consequently s,r,c are nonzero. Since A and Dm are nonzero integers, |I|>=c^2. We get Q>1 and delta>0. Also Df>|c|+1. If b=c-R+4IT=0 then |V|=|c|>=1; if b!=0 then |V|>=Df-|c|>1. Hence Cy>0 and Da>0.

A zero makes one of the four complex conjugate factors zero. If Dg<0 then P<0, while Df Da>0 and Df Cy/delta>0. The P radical would be the sole nonzero imaginary contribution, impossible because S!=0. Dg is odd, so Dg>0. If Budget<=1, D<=-1 and Dg=1+4D Dt s^2<=-3, again impossible. Thus Budget>=2.

The established centered-budget implication now gives k!=0, Derr<q^2, |eta/k|<1/2, and the common strict sign of q,F,C,q-F-C. Explicitly 0<cone_A F/q<2 and 0<cone_B C/q<2, and the payload bounds give F/q+C/q<1. Setting m=|Y|, K0'=|k|, C0=|c| gives

    K0'(m-1/2)<C0<K0'(m+1/2), sign(c)=sign(kY).

No eta>0 premise is used at this stage.

## 3. Two squareclasses, followed by two coprime factorizations

I is even, hence Df=Da=1 mod4, delta odd, and P odd. For Nint a vanishing factor divided by S gives a rational signed sum

    sqrt(Df Da) + 2 sqrt(P).

For Nrat multiply the analogous rational sum by delta to obtain

    sqrt(Df Da) + 2delta sqrt(P).

Both underlying integer radicands are positive and odd. If two odd-integer radicals share a nontrivial squareclass, their coefficients after extracting odd square factors have distinct 2-adic valuations: 0 and 1. They cannot cancel. Distinct squarefree radicals are linearly independent over Q. Thus in either equation both Df Da and P are integer squares. This argument does not presume pairwise coprimality between the two groups.

Within the guard group,

    gcd(Dt,Dg)=gcd(Dt,1+4D Dt s^2)=1.

Within the strong/auxiliary group, compute modulo Df:

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm, Da=A^2 Dm.

Since A Dm divides I, Df=1+Delta I^2 is coprime to each of A and Dm. Consequently gcd(Df,Da)=1. The product-square and positivity facts now show that EACH of Df,Da,Dt,Dg is a square. Write their integer roots f,ytilde,tau,g.

Put y=ytilde/delta in Q. Then QV^2-(Q-1)y^2=1. The adjacent-coefficient Pell descent in source/centered11-proof.md Section4.2 proves y is an integer: if y has reduced denominator b then b^2 divides Q-1, and the norm-preserving descent decreases |V| while retaining that denominator until |V|=1, where it is 1. The proved prerequisites are Q>1 and integer V.

The integral factor equation is therefore

    Z/S= +/- f delta y +/- 2tau g       (Nint),
    Z/S= +/- f y       +/- 2tau g       (Nrat).

Thus S divides Ac in either case.

## 4. Scalar main projection and signed soundness

First H^5 divides Ac=Phi_H(HT+K), where

    Phi_H(z)=z^5+3H^2 z^3-19H^3 z^2-57H^5.

If p^e exactly divides H and b=v_p(HT+K)<e, the leading term has valuation 5b, strictly lower than each other term. This contradicts p^(5e)|Ac. Therefore H|K. The universal identity

    K=HXc-2Kquad, Kquad=X(X+2ac)-1

and oddness of H give H|Kquad.

The recovery of the omitted main Pell root precedes orientation and is unchanged, because we have recovered exactly the same strong and auxiliary norms and V residues. For completeness of the dependency chain, let B0=|A|, C0=|c|, I0=|I|. Then B0>=3, 0<C0<=I0 and

    |f|=chi_B0(m0), I0=psi_B0(m0), |f|>2I0.

Let rho=(B0^2-1)I0. The auxiliary equation classifies rho|V|=chi_rho(nu), |y|=psi_rho(nu). Its index nu is odd since even-index chi_rho is +/-1 modrho. Using V=-c modf, the odd quotient-polynomial identity yields psi_B0(nu)=+/-C0 mod|f|. Fold nu modulo2m0 and reflect to 0<=p<=m0. Since psi_B0(p)+C0<=2I0<|f|, the congruence cannot wrap and gives C0=psi_B0(p), p>=1. This is the absolute signed folding proof in source/signed-quadratic-proof.md Section2; it needs no oddness of I/c^2.

Apply only the PRE-PROJECTION signed-rank argument in source/centered11-proof.md Section5.2. All its hypotheses have now been supplied: common-sign packing, the centered C0/|k| strip, the main classification, the first/strong/auxiliary norms, c^2|I, and both residues

    V=-c modf, V=-R modc.

The latter follows from V+R=Delta I^2(c-R)+4I Df T. The nonodd strong-rank step there is expressly proved by Lucas composition, not by an invalid odd normalization. It gives p|m0 and C0|m0, and the auxiliary step-down gives p=R. Combined with the first norm it gives

    R=2t+1, t>=24, |Y|>(|X|-3)^t/2-1.

The signed whole-product proof in source/signed-quadratic-proof.md Section5 then gives

    |H|>2^(2R+2)|X|^2,
    H | (sign(c)X-2^R)(2^R sign(c)X+1).

The product has absolute value less than |H| and its second factor is odd/nonzero, so sign(c)X=2^R. The centered orientation and uniform half-binomial argument in source/centered11-proof.md Sections5.2-5.3 gives X,c,k,Y>0 and 0<eta/k<1/4. Section5.4 regenerates fresh odd strong/auxiliary witnesses and an actual old signed Q41 zero, rather than claiming the incoming even multiplier was odd. The retained ordinary native/compiler/refutation calibration gives a finite syntactic ZFC refutation.

This proves soundness for both new equations, with every change of multiplier licensed before use of the inherited lemmas.

## 5. Completeness, with fixed-witness order

Begin with the canonical outer witness supplied by a finite syntactic refutation in the retained source theorem. Its centered half-binomial values have Derr<=q^2/2, 0<eta/k<1/4, Budget>q^2 k^2/4>=64, and Dt=tau^2>0. Moreover Dt=1 mod3 because ell=XY^2 is 0 or2 mod3. Thus D Dt=(3Budget-4)Dt is positive and 2 mod3, hence nonsquare.

Ordinary Pell existence supplies g0^2-D Dt u0^2=1 with positive g0,u0. Square the unit to set g=g0^2+D Dt u0^2 and s=g0 u0. Then g^2=1+4D Dt s^2=Dg and P=(tau g)^2.

A and Dm are now positive fixed outer integers. Use the FULL-RESIDUE theorem in source/centered11-proof.md Section6 with N=2s A Dm. It chooses ONE positive strong pair I,f with

    8s A Dm c^2 | I,

such that, for that same I,f, every class modulo I contains an auxiliary T with our exact V formula and an integral norm root y. Define r=I/(2s A Dm c^2), an integer. This realizes exactly our I=2s r c^2 A Dm.

The canonical projection gives H|Kquad, hence H|K. Write kappa=K/H. Intersectivity of pi supplies an integer residue a0 with pi(a0+kappa)=0 modI. Only now choose T=a0 modI from the fixed-pair interpolation theorem. It follows that Ac/S=pi(T+kappa)/I is an integer. Set

    n=Ac/S+f delta y+2tau g       (Nint),
    n=Ac/S+f y      +2tau g       (Nrat).

These integers make the indicated conjugate factor vanish. The order is outer data, guard Pell s/g, fixed strong I/f/r, intersective residue, auxiliary T/y, then n. There is no circular dependence or varying strong pair after the residue is selected.

Both equations therefore have an integer zero exactly when the retained source endpoint has a finite syntactic ZFC refutation. Composing the named ordinary calibration gives the same claimed ZFC-provable equivalence of universal nonvanishing and Con(ZFC), subject to the explicit formalization boundary above.

## 6. Optimized previous endpoints

For optimized_guard_fused11_direct and optimized_guard_fused11_aux replace our I by 2s r c^2 and keep all corresponding downstream definitions. Write

    Z=S(n+Cshift)-Ac,
    u=S^2 Df, b=4S^2 Da, e=16S^2 P,
    Cshift=0 (direct), or (2Q-1)V (auxiliary-centered).

Evaluate the SAME octic as before by

    p=Z^2 b, t=u e,
    N=[(Z^2+b-u-e)^2-4(p+t)]^2-64pt.

The complete eight-conjugate identity proves equality with the preceding symmetric evaluator. Computing P=Dt+D(2sDt)^2 instead of materializing Dg saves another gate. Thus the prior soundness/completeness proof is literally unchanged; the full text is retained at source/PROOF.md Sections1-4.

For optimized_fused11_rational and its integral comparison companion instead use

    I=2s r c^2 P Dm A,
    Nrat_all=delta Z^2-S^2 Df P Cy,
    Nint_all=Z^2-S^2 Df P Da,
    Z=Sn-Ac.

These are exactly source/PROOF.md Section5, using P both in I and the output. All four factors Df,Dt,Dg,Da remain pairwise coprime, by the same congruences and I divisibility. The previous full ordinary proof applies without alteration. The live evaluator saves two operations, giving 1632/112 and 1892/112; the latter is dominated and retained only for comparison.

## 7. Exact degrees and audit boundaries

For the new pair:

    deg I=24, deg S=54, deg Df=60, deg Q=72,
    deg V=85, deg Cy=242, deg Da=314, deg P=94, deg Ac=35,
    deg Z=55.

The integral expression has unique maximal term (S^2 Df Da)^2, degree 964. The rational expression has unique maximal term (S^2 Df Cy)^2, degree 820. The checker propagates exact leading monomials through every actual gate, with fixed numerals retained as symbolic independent ports until their authenticated positivity is applied. The output leader is a nonzero monomial with coefficient consisting only of signed powers of 2,3,beta. Thus these are exact total degrees, not numerical samples.

For the inherited centered octic, the universal identity

    4S^2 Da-[S(2Q-1)V]^2=S^2(-V^2-4Q+4)

gives omega=Z^2-b degree126. The balanced inner expression is identically (omega-u-e)^2-4(ue+b(u+e)), whose unique leader is -4be of degree344. Its square has degree688; the remaining product has degree614. This exact cancellation cut is checked separately before being used to audit the actual balanced DAG. Direct degree728 and all-fused1632/1892 are unchanged and their actual gate leaders are also checked.

Two dominated diagnostic pair variants center by A I V and by lambda V, where lambda=(2Delta+1)Ib. Since Df-lambda^2=1-Ib^2, exact degrees become796 and772. Their operation costs122 and124 make them dominated, so they are not reported as new frontier points. They remain as explicitly proved, audited comparison circuits.

Every addition, subtraction and multiplication, including squares and scalar products, costs one. Leaves and reuse are free. Literal DAGs contain no division, roots, variable exponents, oracle, or variable coefficient port. The audit independently binds every live mathematical register in a free polynomial ring, multiplies all4/8 radical conjugates, proves the exact cancellation identities, authenticates retained proof dependencies and six actual coefficient payloads, rebuilds all six finite numeral recipes, verifies topology and liveness, counts gates, and certifies exact leading monomials. It contains no removable assert statements and passes with python -O.

## 8. Directions tested but not claimed

A fixed quadratic carrier t^2+1 cannot simply replace the intersective quintic: every strong ordinate is forced divisible by c^2, and one cannot assume those mandatory primes split in Q(i). The automatically soluble variable carrier t^2-(1+I^2) degenerates at I=0, exactly the branch the current carrier must exclude. Forcing a Pell positivity ordinate s to be odd is not justified by taking powers of a unit; some Pell equations have only even such ordinates. Fusing the strong radicand with the positivity guard lowers a naive degree estimate but introduces a circular choice of I and s under the available interpolation theorem. None of these possibilities is counted as a result here.
