# Independent adversarial audit of the combined Diophantine reductions

## Verdict and boundary

PASS for the mathematical reductions reviewed below, subject to the same actual fixed Start-only compiler contract and ZFC-recognizer calibration as the parent construction. No counterexample or remaining proof gap was found in these reductions after the proof-order qualifications below were enforced. This is an independent mathematical review, not a new end-to-end Lean/Rocq check. In particular, arithmetic tests do not prove the compiler theorem or Con(ZFC).

Reviewed artifacts:

- `pell/START_ONLY14_PROOF.md`: 14 positive variables, a 75-operation degree-293 polynomial, or five comparisons using 69 operations and maximum degree 244.
- `quadratic/LOW_DEGREE_PROOF.md`: 33 positive variables / 24 quadratics; 25 positive variables / 16 cubics; 20 positive variables / 11 quartic-or-lower equations. Their squared sums have exact degrees 4, 6, and 8 respectively.
- `pell/POSITIVE_GAP_SHEARS.md`: ordinary-strong compact polynomial 69 operations / degree 99, six-comparison system 61 operations / maximum degree 28; two positive-gap shears give 71 operations / degree 83 and six comparisons in 63 operations / maximum degree 22.
- `integers/SIGNED_DOMAIN_PROOF.md`: only nine original coordinates require positivity. The signed-root extension below further gives a 32-unrestricted-integer-variable version of P14.

The actual four fixed numerals must come from the appropriate audited compiler recipe. Port names and elementary mask bounds alone do not license changing from one machine/compiler to another. Coefficient-generation and raw-machine-calibration audits are separate.

## 1. Ordinary strong rank: valid, but not by naive cancellation

Write A=a+2, Delta=A^2-1, c=psi_A(p), I=i*c^2. The equality

    I^2=Delta*(f^2-1)

alone does not imply f=chi_A(m), Delta divides I, or c^2 divides f^2-1. For example A=7, Delta=48, f=2, I=12 satisfies I^2=Delta*(f^2-1), whereas 48 does not divide 12 and 2 is not a positive chi_7 value. The reviewed proofs correctly use the independently established large main Pell coordinate

    c>A*Delta^2.

I checked the full generic recovery argument in `diophantine_zfc_review/Papers__1980__PELL_RELAXED_AUXILIARY_PROOF.md`, rather than merely accepting its conclusion.

Factor Delta=d0*s0^2 with d0>1 squarefree. Choose the least positive integer-coefficient Pell unit F+y0*sqrt(d0). There is e>=1 with

    A=chi_F(e), S=psi_F(e), Delta=(F^2-1)S^2,
    psi_F(ep)=S*c.

The ordinary strong equality yields an integral solution in the smaller squarefree field: s0 divides I and d0 divides I/s0, so I/(d0*s0) is integral. Thus for some n>0,

    |f|=chi_F(n), I=(F^2-1)S*psi_F(n).

Set T0=(F^2-1)S and g=gcd(n,ep). Strong divisibility of psi gives h0=psi_F(g). Since c^2 divides T0*psi_F(n), one obtains

    c <= gcd(c^2,T0*psi_F(ep)) <= T0*h0,
    h0>=c/Delta.

If g<ep, then 2g<=ep, while Pell doubling gives

    2h0^2<psi_F(2g)<=S*c<A*c.

This contradicts h0^2>=c^2/Delta^2>A*c. Hence ep divides n. Writing n=e*m proves

    |f|=chi_A(m), p|m, I=Delta*psi_A(m).

For m=p*b, expansion modulo c^2 gives

    psi_A(pb)/c = b*chi_A(p)^(b-1) mod c.

The ordinary equation yields c|Delta*b. Also psi_A(p)=p*A^(p-1) mod Delta, so gcd(c,Delta)=gcd(p,Delta) divides p. Therefore c|m. In summary:

    |f|=chi_A(m), p|m, c|m, I=Delta*psi_A(m), m>=c>2p.

Only now infer

    f^2-1=I*psi_A(m)=i*c^2*psi_A(m),

so c^2 divides f^2-1. This is the correct order for reconstructing

    o=cT-Rf, j=Tf-1-R*(f^2-1)/c.

In the positive auxiliary presentation, of=V+c>0 and jc=V+R>0 then prove o,j>0. No unproved division or assumption Delta|i is needed.

The pre-rank size condition is available independently: first/main Pell classification gives k=2psi_P(n), c=psi_A(p), P=2XY^2+1>A, and p>n. The index congruence and 0<R+epsilon<E yield n>=(R-1)/2>=24, hence c>A*Delta^2 and c>2p. None of this uses f,V, a decoded computation, or the desired exact index p=R.

## 2. Signed auxiliary roots do not invalidate index recovery

The normalized strong equation gives |f|=chi_A(m), psi_A(m)=i*c^2 directly. Strong divisibility and expansion modulo c^2 give p|m and c|(m/p), so m>=c>2p. The ordinary version uses the preceding rank lemma. In either case the auxiliary square rho^2 satisfies

    rho^2=Delta*(f^2-1), c|rho, f^2=1 mod c.

The norm

    rho^2 V^2-(rho^2-1)y^2=1

allows V and y to have either sign, but neither can be zero. Put v=|V| and sigma=sign(V). Its Pell classification is

    rho*v=chi_rho(ell), |y|=psi_rho(ell).

Divisibility of the first coordinate by rho forces ell odd. For ell=2u+1 use the integral quotient polynomial Q_u:

    chi_Z(2u+1)=Z*Q_u(Z^2),
    Q_u(1-A^2)=(-1)^u psi_A(ell),
    Q_u(0)=(-1)^u ell.

The defining V=c(Tf-1)-Rf^2 gives V=-c mod |f| and V=-R mod c even when f,T are signed. Consequently

    (-1)^u psi_A(ell)=-sigma*c mod chi_A(m),
    (-1)^u ell=-sigma*R mod c.

Squaring the first congruence and using chi_A(2j)=1+2Delta*psi_A(j)^2 gives chi_A(2ell)=chi_A(2p) mod chi_A(m). The step-down lemma gives ell=+p or -p mod m, hence mod c. Combining with the second congruence gives R=+p or -p mod c. Because 0<R,p<c/2, p=R. The sign sigma is harmless; no positive o,j or V is assumed in this signed argument.

For completeness, the relevant step-down lemma itself has a short direct justification. Modulo M=chi_A(m), addition identities give chi_A(n+2m)=-chi_A(n) and chi_A(2m-n)=-chi_A(n). Reduce an index to plus or minus a representative r between 0 and m. For 0<k<m, chi_A(r)=chi_A(k) mod M forces r=k in the equal-sign case, by strict growth. The opposite-sign case cannot satisfy chi_A(r)+chi_A(k)=M because both terms are at most chi_A(m-1) and 2chi_A(m-1)<M. The endpoints r=0,m likewise cannot match chi_A(k). Thus the plus congruence implies n=+k or -k mod 4m, and in particular mod 2m. With n=2ell and k=2p this gives the asserted conclusion by dividing an integer equality by two, not by inverting 2 modulo an even modulus.

After p=R, E>R+2 suffices to exclude a wrap in 2n=R+epsilon+vE. If v>=1, then 2n>2R, contrary to n<p. The epsilon=-1 case would give p=2n+1; Pell duplication and chi_A(2)>P imply c>A*k>k(Y+1), contradicting kY<c<k(Y+1). Hence epsilon=1 and 2n=R+1. A product's remaining transport sign is then also +1.

## 3. The 14-variable norm elimination is valid only with the correct proof order

Let

    d=1+Delta*i^2*c^4, Q=(Delta*i*c^2)^2=Delta*(d-1),
    b=c+R*d, u=c*T,
    Astar=Q*(d*u^2+b^2-y^2)+y^2-1,
    Bstar=2Q*u*b, Hnorm=Astar^2-d*Bstar^2.

For positive T, Bstar>0. Hnorm=0 gives a rational f=Astar/Bstar with f^2=d. A rational number with integral square is integral, so this really restores an integer f, not merely a rational auxiliary variable. Its sign is undetermined.

The exact identity

    Q*(u*f-b)^2-(Q-1)*y^2-1
    =Astar-Bstar*f+Q*u^2*(f^2-d)

restores the auxiliary norm, with V=u*f-b=c(Tf-1)-Rf^2. It is invalid to apply the old theorem requiring all-positive auxiliary witnesses at this stage. Instead use Section 2 to recover p=R with signed f,T,V, then use only the first/main ratio and projection arguments to obtain X=2^R and the half-binomial extraction. These arguments do not use auxiliary signs.

The population/mask decoder can then recover C=1 mod 4, and hence R=3 mod 4. Only after this may the canonical positive auxiliary family be regenerated. For example use m=2cR and

    f_new=chi_A(m), i_new=psi_A(m)/c^2,
    rho_new=Delta*psi_A(m),
    V_new=chi_rho_new(R)/rho_new,
    y_new=psi_rho_new(R).

The required c^2 divisibility follows by expanding the main unit to the power 2c. R=3 mod 4 yields V_new=-c mod f_new and V_new=-R mod c. Then o_new=(V_new+c)/f_new is an integer. Since gcd(f_new,c)=1 and

    f_new*(o_new+R*f_new)=V_new+c+R*f_new^2=0 mod c,

T_new=(o_new+R*f_new)/c is integral too. All these regenerated witnesses are positive. This is an existence-preserving reconstruction, not a bijection preserving the original i,T,y.

The pre-decoding boundary C=0 was checked: transport initially gives only C>=0 for product unit signs. The weaker bounds q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2 suffice for E>R+2. C>0 is used only after the transport sign becomes +1. No premature strict budget or parity hypothesis is required.

## 4. Signed h and gamma are actually forced positive

Only nine supplied ports need positivity:

    J,F,alpha,z,i,s,w,eta,zeta.

First, k=R+epsilon+hE>0 and E>R+2 imply h>=0. If h=0, then 2<k=R+epsilon<q^4<=XY^2. The first Pell norm at u0=XY^2 has positive coefficients 2, 8u0+4, ... and no coefficient strictly between 2 and u0. This contradiction proves h>0. Equivalently, one can use the elementary consecutive-square gap established in the signed-domain proof.

The main norm initially gives |D|=chi_A(p), not D>0. Section 2 recovers p=R using |D|. Put r=(R-1)/2. The lower ratio uses only these Pell magnitudes and gives

    a>X^(r+1)/3>X*2^R,

where X>=16 and r>=24 make (X/4)^r>6. Put e_R=chi_A(R)-a*psi_A(R). Its recurrence gives e_R=2^R mod H, H=4a+3, and

    e_R*(chi_A(R)+a*c)=1+H*c^2=1 mod H.

If D=-chi_A(R), the definition D=X+a*c+gamma*H forces chi_A(R)+a*c=-X mod H. Hence H divides X*2^R+1. But 0<X*2^R+1<a+1<H, impossible. Thus D>0. The usual projection now gives X=2^R exactly. Finally

    e_R=2c-psi_A(R-1)>c>X,

so gamma=(e_R-X)/H>0. This proves the signed-gamma extension noncircularly; merely taking |D| in its defining affine equation would not have been valid.

All added quadratic registers can be signed because their gate equations uniquely force their intended values. Positive completeness witnesses remain available, and signed soundness decodes the same computation. No coordinatewise absolute-value bijection is claimed for V,T or the full derived register tuple.

## 5. Further audited improvement: P14 also allows T to be signed

The possible denominator failure T=0 must not be ignored. It is, however, excluded by an independent gap argument before restoring f.

Under the same nine positive ports and signed h,T,tau,y,gamma, the unit-sign arguments still give Hnorm=0 and the two Pell norms. All packing bounds remain valid. Since Delta>R and c>=3,

    d=1+Delta*i^2*c^4>Delta+c,
    Q-b=(Delta-R)d-Delta-c>0.

Thus 1<b<Q. If T=0, then Bstar=0 and Hnorm=0 forces Astar=0, namely

    Q*b^2-(Q-1)*y^2=1.

For any solution of this norm with b>1, writing y0=|y| yields y0>=b+1 and

    b^2-1=(Q-1)(y0^2-b^2)>2b(Q-1).

Therefore b>2(Q-1), hence b>=2Q-1, contradicting b<Q. Consequently T is nonzero and Bstar is nonzero. Rational-root reconstruction is valid without T>0; the signed proof of Sections 2-4 then applies.

P14 therefore has the same existence predicate with exactly nine positive and five unrestricted signed variables. Substituting

    Pos(x,y,z)=1+x^2+y^2+z(z+1)

for those nine positive variables gives 9*3+5=32 unrestricted integer variables. Pos is always positive; Legendre's three-square theorem applied to 4n-3 proves it represents every n>=1. Its evaluation costs 3 multiplications and 4 additions, so the transformed literal P14 uses 138=71M+67A operations. The original degree-293 leader contains h and gamma to first power and no T,tau,y, so after the nine quadratic substitutions its exact degree is 2*293-2=584. The nonzero leading-form argument is uniform for beta>0.

This new 32-variable integer result is an existence equivalence, not an assertion that every signed auxiliary witness can be made positive by changing only its sign.

## 6. Low-degree lifts and positive-gap shears

The ordinary 33-variable quadratic system correctly replaces the normalized strong variable relation I=i*Delta*c^2 by I=i*c^2 and uses I^2=Delta*(f^2-1). It is not a same-i algebraic identity. Completeness maps i_normalized to Delta*i_normalized; soundness uses Section 1. Its degree-four sum of squares is literal, with 24 terms.

The 25-variable cubic system is a genuine positive-zero bijection with normalized34. The key nontrivial substitution is tau=L0+t with L0=E(c-eta)>0. The first norm gives tau>L0, so t>0; conversely tau=L0+t restores a positive root. Its other eliminated registers are positive by direct definitions, transport C>0, and the auxiliary gap. The cubic first norm is t^2+L0(2t-k)=1. No degree-four multiplication is hidden in an uncharged variable.

The 20-variable octic alternative is likewise a positive-zero bijection with ordinary33. Although its deleted R is written k-1-hE and is not visibly positive, the retained packing equality makes R>0. The elementary pre-rank bootstrap gives c>A*Delta^2 and f>2c before V0=Tf-1 and g=y^2-V^2 are restored positive. Thus positivity is not justified circularly by invoking the full old system before its hypotheses hold. All eleven residuals have degree at most four; the first contains -beta^3 J^3 s, and no other residual contains s, proving exact degree eight of its squared sum.

For the two positive-gap shears in the compact ordinary polynomial, tau=L+t and y=V+e, the reverse proof correctly first restores y_old=|V+e|. Its nonzero value follows from the auxiliary norm and Qordinary=I^2>1. All old supplied witnesses are then positive, so the ordinary theorem proves V>1, whence V+e>0. This supplies a genuine positive-zero bijection and avoids assuming the sign of V+e off the zero set.

## 7. Independent arithmetic checks

I ran a separately authored inline Python audit reading only inert JSON; no received source script was imported or executed. It checked gate dependency order, uniqueness, all witness/fixed-port/gate liveness, and exact operation inventories for six compact circuits. Results are saved in `arithmetic_checks.json`:

- P14: 75=44M+31A; system: 69=40M+29A.
- Ordinary: 69=39M+30A; system: 61=34M+27A.
- Ordinary two-gap shear: 71=39M+32A; system: 63=34M+29A.

For each P14 artifact, 60 independently generated signed assignments also verified its complete output against a separately typed direct formula, including the cross-term identity. These finite checks supplement, not replace, the exact proofs above. The supplied symbolic degree witnesses were inspected; they are nonzero for every admissible beta>0, not merely for generic coefficients.

## 8. Claims that must not be made

- Do not treat ordinary strong equality alone as integral Pell classification.
- Do not reconstruct a Bezout quotient by division before its divisibility proof.
- Do not invoke an all-positive auxiliary theorem on the first signed root produced by a norm elimination.
- Do not use R=3 mod 4 before obtaining it from the decoded masks in the signed extension.
- Do not allow signed T in P14 without excluding T=0.
- Do not infer a compiler theorem from circuit identities or finite arithmetic tests.
- Do not describe these counts as a global minimum. They compare different domains, degrees, circuit costs, and coefficient-height conventions.
- The statement that ZFC proves the equivalence is a formalizability claim for these ordinary mathematical proofs and the inherited calibrated compiler. It is not a claim that a new complete theorem has already been kernel-checked, nor a proof of Con(ZFC).
