# A Pell descent removes the denominator guards

## Result and exact domain

The delivered equation is one integer polynomial in twelve strictly positive integer unknowns:

    j, F, alpha, t, T, X, Y, r, eta, zeta, n, gamma.

Its exact total degree is 82. The literal division-free evaluator in equation.json uses 102 live binary arithmetic operations: 57 multiplications, 26 additions, and 19 subtractions. Fixed integer leaves and register reuse are free; scalar multiplication and squaring are charged. These counts do not represent bit complexity.

It improves the inspected package61 twelve-positive-variable degree118/104-operation construction to degree82/102. This is a reduction of 30.5085% in degree and two operations. It does not change the nine-positive-variable bound, establish a global minimum, or supply a new end-to-end Lean/Rocq certificate.

The fixed coefficient tuple is the complete compact44 tuple, with beta=2^590069-1. The mapping and exact bytes are in native/ACTIVE_BINDING.json. K0 is its K port and MF is its already shifted MF_source port. No extra shift is applied. Each other symbol below is a polynomial abbreviation and introduces no unknown.

## 1. Complete equation

Define the retained carrier registers by

    J=6j+1, q=beta J+1, C=q-F-alpha,
    E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a²+H=(a+2)²-1,
    ell=EkY, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    v=k-R-1, U=q⁵,
    Dstar=U b0+H(U gamma+q⁴X-v),
    W=(q-1)k+1, M=q³(q-1),
    Bt=(q K0+X)C-qF,
    Z=M(ell+k+r)+(q-1)Y-q³W Bt,
    A0=Z²-M²[ell(ell+k)+1],
    A1=Dstar²-U²(1+Delta c²).

Define the new registers by

    f=t+1, rho=f²-1, d=Delta c⁴, Q=Delta rho,
    V=f²(cT-R)-c,
    h(z)=(1-Q)z²+2(1-Q)Vz+V²-1,
    aN=h(n), bN=2(1-Q)(n+V),
    AN=d aN+(1-Q)rho,
    N=AN²-d bN² rho.

The single equation is

    P12=(1+A0)(1+A1)(1+N)-1=0.

The evaluator reuses s=V+n and writes h(n)=s²-Q(s²-V²)-1. This is exactly the same polynomial. All exponents are fixed nonnegative integers.

## 2. The new rational-integrality lemma

**Lemma.** Let Q>1 be an integer. If V is an integer, y is rational, and

    QV²-(Q-1)y²=1,

then y is an integer.

**Proof.** Changing signs lets us suppose V>0 and y>0; V=0 or y=0 is impossible. Write y=a/m in lowest terms with m>0. Since (Q-1)a²/m² is integral, m² divides Q-1. In particular m divides Q-1.

If V=1, the equation says y²=1, hence y=1 and m=1. If V>1, define

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first number is an integer because m divides Q-1. Direct expansion, using (2Q-1)²-4Q(Q-1)=1, proves

    Q(V')²-(Q-1)(y')²=1.

Moreover y>V, since (Q-1)(y²-V²)=V²-1>0. Also QV>(Q-1)y: both sides are positive, and their squared difference is QV²+Q-1>0. These two strict inequalities give

    -V < V' < V.

The new norm excludes V'=0. Finally y' has the same reduced denominator m as y, because 2Q-1 is congruent to 1 modulo m and its other summand is an integer. Replacing V',y' by their absolute values and applying strong induction on the positive integer V reaches the case V=1 without changing m. Thus m=1. This proves the lemma.

This argument is specific to the adjacent coefficients Q and Q-1 and the unit right-hand side. No coprimality hypothesis involving a second equation is needed. No finite Pell search is used as a proof.

## 3. Exact elimination of two rational coordinates

Let d,rho,Q>0, Q>1, and let V,n be positive integers. Define h,aN,bN,AN,N as above. Since n+V>0 and Q>1, bN is nonzero.

If N=0, set the proof-only rational numbers

    i=AN/(d bN), u=n-i.

Then d i²=rho. Dividing the defining equation for AN by d gives

    aN+(1-Q)i²=bN i.

Expanding h(n-i) shows h(u)=0. Put y=V+u. The latter equality is

    QV²-(Q-1)y²=1.

The lemma proves y is an integer. Therefore u=y-V and i=n-u are integers. This is the crucial step: the polynomial resultant alone would supply only rational coordinates.

Conversely, d i²=rho and h(u)=0 with n=i+u imply N=0. The exact identity is

    N |_(rho=d i²) = d² h(n-i)h(n+i).

For the positive source lift, suppose V>1. The norm gives |y|>|V|. Thus i_positive=|i| is positive because rho>0, and u_positive=|y|-V is positive. The same strong equation and auxiliary norm hold with these positive coordinates.

## 4. Why the source carriers justify the lemma without circularity

For any positive input, f=t+1>=2, Delta>0 and rho>0, hence Q>1 and d>0. Because beta and J are odd, q is even. Consequently A0 and A1 are squares modulo4; bN is even, so N is also a square modulo4. At a zero of P12, each of its three integer factors is a unit. A negative unit would require a residual equal to -2, which is 2 modulo4 and cannot be a square modulo4. Hence

    P12=0  iff  A0=A1=N=0

on the positive domain.

The following carrier consequences are proved in the retained package61 PROOF13.md/PROOF14.md and report, independently of its strong and auxiliary equations. Their logical order matters:

1. A0=0 makes Z/M a rational square root of ell(ell+k)+1, hence an integer. Reducing M|Z modulo q³ gives q³|Y. Reducing modulo q-1 gives q-1|Bt. With s=Y/q³ and b=Bt/(q-1), the identity Z/M=ell+k+r+s-Wb and the bound |Z/M|<ell+k give b>0. Therefore Bt>0 and C>0.
2. The authenticated whole-tuple mask bounds then give q>=16 and 3q<R<q⁴-2. The imposed J=6j+1 gives the same q=2 modulo3 restriction used in the parent. Since q³|Y, gcd(q,H)=1.
3. Before q|X has been recovered, Dstar>Uac-Hk>k(UaY-H)>0. Thus A1=0 gives a positive integer main root D=Dstar/U satisfying D²-Delta c²=1.
4. Let A=a+2 and P0=2XY²+1. Positive Pell classification gives main and first indices p,m1>=1 with c=psi_A(p), k=2psi_P0(m1), and |Z/M|=chi_P0(m1). Since c>1, p>=2. If m1=1, then k=2, eta=zeta=1 and c=2Y+1, contrary to c>=2A>=4Y+4. Hence m1>=2, and

       c>kY>=4P0Y>8XY³>=8q⁹>2R.

Only A0 and A1 have been used. In particular no strong index or auxiliary rank has been assumed. Now T>=1 and f>=2 give

    V=f²(cT-R)-c > f² c/2-c >= c > 1.

Thus n+V>0 and the rational elimination in Section3 is valid. It recovers positive integers i_positive,u_positive such that

    f²-Delta(i_positive c²)²=1,
    QV²-(Q-1)(V+u_positive)²=1.

Together with A0=A1=0, these are exactly the four residual equations of the parent P13. Its old positive j coordinate is 2j, because 3(2j)+1=6j+1. Therefore every positive zero of the new equation gives a positive zero of package61 P13.

The parent's remaining Pell rank recovery, restoration of q|X and the deleted quotients, native compiler, and K215/refutation calibration are inherited unchanged. They yield a finite syntactic ZFC refutation. This paragraph states the inherited semantic boundary rather than replacing it by a finite algebra test.

## 5. Completeness and the exact residue restriction

A finite refutation gives the canonical compact source witnesses specified by package61. Their radix is B=2^590069; q=B^N and J=1+B+...+B^(N-1), with N odd and greater than1. Since B is even, J is odd. Since B=-1 modulo3 and N is odd, J=1 modulo3. Thus J=1 modulo6, and j=(J-1)/6 is a positive integer.

The parent supplies positive f,i,T,u and carrier gaps r,gamma. Its normalized strong equation implies f>1. Put t=f-1>0 and n=i+u>0. Retain all other coordinates. Then d i²=rho and h(u)=0, so the exact norm identity gives N=0. The carrier residuals are unchanged and vanish. Hence P12=0.

No new congruence restriction on f, no doubling of the strong index, and no new choice of the auxiliary pair is needed in this principal construction. The canonical J restriction is already part of the parent's completeness proof. The equivalence is an existence equivalence; it is not a claim of a bijection between every pair of positive zero sets.

Combining soundness and completeness gives, by ordinary mathematics formalizable in ZFC,

    exists a positive zero of P12  iff  a finite ZFC refutation exists.

Negating gives the requested equivalence with Con(ZFC). Here Con(ZFC) refers to the same recursive syntactic proof predicate as the inherited calibration, and no consistency or arithmetic-soundness assumption is introduced.

## 6. Exact degree and a coefficient independent of three ports

Each input has degree1, while the four fixed coefficient ports have degree0. Put

    q0=6 beta j, k0=eta+zeta, c0=k0Y,
    Delta0=X²Y², R0=q0³(q0-F),
    Bt0=(K0q0+X)(q0-F-alpha)-q0F.

The retained carrier cancellation identities give

    in15(A0)=-2q0⁸k0²XY²Bt0,
    in17(A1)=8q0¹⁰k0X²Y³gamma.

For the new norm, the exact degrees of rho,d,Q,V,aN,bN,AN are respectively 2,12,6,6,13,12,25. Their relevant leading forms are

    d0=Delta0 c0⁴, Q0=Delta0 t², V0=-t² R0,
    (aN)13=-2Q0V0n, (bN)12=-2Q0V0,
    (AN)25=-2d0Q0V0n.

The second summand d bN² rho has degree38, strictly below the degree50 of AN². Therefore

    in50(N)=4Delta0⁴c0⁸t⁸R0²n².

Only A0 A1 N reaches degree82 in the product finalizer. Its leading homogeneous form is

    in82(P12)=-64q0²⁴(q0-F)²k0¹¹X¹¹Y²¹t⁸n²gamma Bt0.

In particular, the coefficient of

    j²⁴ F² eta¹¹ X¹² Y²¹ t⁸ n² gamma alpha

is exactly 64(6 beta)²⁴>0. The minimum j-power24 forces F² from (q0-F)² and -X alpha from Bt0, so no specialization of K0,MC,MF can cancel it. This proves exact degree82 on the authentic fixed coefficient slice.

## 7. Reproducibility and scope

Run python3 verify.py from this directory. It independently checks the literal graph, full coefficient bindings, exact small polynomial identities, exact carrier cancellations and leading forms, the norm cut, degree/operation ledgers, canonical Pell reconstruction examples, and byte-identical rebuilding of equation.json. It also rebuilds the inherited coefficient recipe in a temporary directory and runs its independent audit. Normal and python3 -O runs use explicit checks, so optimization does not disable them.

These finite checks support exact formulas and finite data. They do not prove ZFC consistent, search for a contradiction, execute K215 to completion, or replace the unbounded compiler/Pell proofs. The descent and elimination proofs above are self-contained ordinary mathematics. Formal integration of the new literal equation and the native calibration is separate work.
