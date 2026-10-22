# Smaller low-degree Start-only systems

The exact artifacts in this directory use the same four fixed numerals as the audited Start-only construction: beta = `Bm1` = B−1, K0 = `Kconstant`, `MC`, and the shifted source numeral `MF` = MF_native+B−1. They are fixed compiler outputs, not quantified parameters. The compiler must be the Start-only variant; arbitrary positive choices of these ports do not establish the consistency theorem.

Two improvements are certified here:

* `ordinary_quartic33.json`: 33 strictly positive unknowns, 24 quadratic equations, one quartic sum of squares.
* `start_only_sextic25.json`: 25 strictly positive unknowns, 16 cubic equations, one sextic sum of squares.

The first combines the ordinary-strong Pell certificate from report02 with the compact quadratic lift from report08. The second applies exact register elimination and a positive first-root shear to report08. Neither is claimed to be globally minimal. The first requires the inherited ordinary-strong rank theorem; the second is a positive-zero bijection with the old 34-variable system.

## 1. The 33-variable quadratic system

Start with all variables and equations in `diophantine_zfc_encoding/start_only_quartic34.json`. Delete the variable K and its two equations K=D²−1 and K=Delta*C2. Replace those equations by

    D²−Delta*C2=1.

Replace I=iK by

    I=i*C2.

Keep every other equation unchanged, including C2=c², Delta=a²+4a+3, Baux=I², Baux=Delta(F2−1), and F2=f². There are exactly 33 variables and 24 equations of degree at most two. The JSON contains every expanded residual.

This is not a same-i polynomial identity. In the old system the strong equation is f²−Delta*(i*c²)²=1. The new one is (i*c²)²=Delta*(f²−1), the ordinary strong equation of the original raw half-binomial kernel.

### 1.1 Completeness and positivity of the lift

Given a positive solution of the old system, retain every coordinate except set

    i_ordinary = Delta*i_normalized.

Then I, Baux, f, and every other retained register have their old positive values. The new I equation follows from old I=i_normalized*Delta*c², and the new strong equation is identical to the old Baux equation. Main-norm equality follows by eliminating old K. This constructs a positive solution of the new system, with no additional inequality or sign hypothesis.

### 1.2 Soundness: the ordinary strong theorem applies before decoding

From the new equations put

    q=beta*J+1, L=q²−1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, a=E+Y, A=a+2, Delta=A²−1,
    c=kY+eta, C=q−F−alpha,
    R=(q²−C−qF)(q²−1)+(MC+q*MF)J.

The transport equation is (K0+w)C+q−F−z(q−1)=1. If C≤0, its left side is at most 1−F−(z−1)(q−1)≤0. Thus C>0. Consequently

    2q−1 <= q²−C−qF <= q²−q−1.

The admissible native masks satisfy 0<MC,MF_native<B−1. Since MF=MF_native+B−1 and J=(q−1)/(B−1), their contribution is strictly between zero and (2q+1)(q−1). Hence

    (2q−1)(q²−1)<R<q⁴−q³,
    E=wsq⁴>=q⁴>R+2, a>R+2.

No power-of-two, decoded computation, auxiliary positivity conclusion, or rank conclusion is assumed in these bounds.

The first norm is tau²−L0(L0+k)=1, where L0=E*kY=XY²*k. Its fundamental-unit classification gives k=2*psi_P(n), P=2XY²+1, n>=1. Because P=1 modulo E and k=R+1+hE,

    2n=R+1 modulo E, n>=(R+1)/2.

The main norm gives c=psi_A(p), D=chi_A(p). Since P>A and c>k, p>n. Standard Pell growth, as in report02's ordinary-strong bootstrap, now gives

    c>A*Delta², c>2p, c>2R.

The ordinary equation I²=Delta(f²−1), I=i*c², therefore satisfies the exact hypotheses of the inherited generic strong-rank theorem. Its conclusions are

    f=chi_A(m), I=Delta*psi_A(m), p divides m, c divides m,
    m>=c>2p.

In particular f²−1=I*psi_A(m)=i*c²*psi_A(m), so c² divides f²−1. This divisibility is not obtained by casually dividing the strong equation.

The retained positive coordinate V satisfies V=c(Tf−1)−Rf². Define

    o=cT−Rf,
    j=Tf−1−R*(f²−1)/c.

They are integers by the preceding divisibility, and of=V+c>0, jc=V+R>0, so o,j>0. Thus the complete positive auxiliary equations are restored. The ordinary strong-rank and signed step-down lemmas, using 0<p,R<c/2, give p=R. A wrap in 2n=R+1 modulo E would force 2n>=R+1+E>2R, contradicting n<p=R. Hence 2n=R+1 exactly.

From this point the first/main Pell ratio and temporal-rotation arguments are exactly the previously audited asymmetric-scale Start-only proof: X=2^R, the half-binomial population threshold, the same shifted masks, and the same Start-only compiler are recovered. The ordinary replacement changes neither that projection nor the compiler. The proof dependencies are the generic ordinary strong-rank theorem and step-down lemma explicitly invoked in `review/02-system63/FIXED_INPUT75_ORDINARY_PROOF.md`, and the original Start-only compiler proof. These are mathematical proof dependencies, not a claim that finite arithmetic tests prove the compiler or that the full development has been newly formalized in Lean.

Accordingly the new system has a positive solution iff the same fixed ZFC contradiction recognizer accepts. The normalized-to-ordinary map proves completeness; ordinary soundness proves the reverse existence implication. No pointwise inverse for i is asserted.

## 2. The 25-variable cubic system

Use the following 25 positive unknowns:

    J,F,alpha,z,f,h,i,T,s,w,t,eta,zeta,y,gamma,
    E,c,a,D,L,R,V,I,Baux,Delta.

The four fixed numerals are as above. Only affine abbreviations are used here:

    q=beta*J+1, k=eta+zeta, H=4a+3, C=q−F−alpha.

The 16 literal equations are

1. L=q²−1.
2. a=E+s*q*(L+1).
3. E=w*q*(a−E).
4. c=k*(a−E)+eta.
5. t²+E*(c−eta)*(2t−k)=1.
6. D=w*q+a*c+gamma*H.
7. Delta=a²+H.
8. D²−1=Delta*c².
9. k=R+1+h*E.
10. R=L*((q−1)*(q−F)+alpha)+(MC+q*MF)*J.
11. (K0+w)*C+q−F−z*(q−1)=1.
12. V=c*(T*f−1)−R*f².
13. I=i*(D²−1).
14. Baux=I².
15. Baux=Delta*(f²−1).
16. y²−Baux*(y²−V²)=1.

Each equation has total degree at most three. The JSON uses the original long variable names where necessary and contains the exact expanded residuals in this order.

### 2.1 Exact positive-zero bijection

The eight eliminated registers are

    N=q(L+1), X=wq, C2=c², K=D²−1,
    G=(q−1)(q−F)+alpha, F2=f², V0=Tf−1,
    g=y²−V².

Their defining equations are deleted and their values substituted everywhere else. The first norm additionally eliminates P and replaces tau by the positive tail

    ell=E*(c−eta), t=tau−ell.

The old equations give P=ell+k and tau²=ell(ell+k)+1. The equations for a and c show a−E=sq³>0 and c−eta=k(a−E)>0, so ell>0. Hence tau²>ell² and tau,ell>0 imply t>0. Substituting tau=t+ell gives the exact identity

    tau²−P(P−k)−1 = t²+ell*(2t−k)−1.

Conversely a positive solution of the 16 equations reconstructs tau=t+ell>0 and P=ell+k>0, then reconstructs the eight listed registers. All old polynomial equalities follow by substitution. The original 15 positive supplied witnesses satisfy the same six-equation source. The original lift's proved positivity lemma therefore restores positive values for every deleted register. Concretely N,X,C2,F2 are positive products; K>0 follows from the displayed positive D formula; G>0 follows from transport C>0; V0>0 follows from the strong f>2c bound; and the auxiliary positivity/gap argument gives g>0. Thus no unmentioned inequality is added by the reverse map. These maps are inverse on positive zero sets.

The first-root shear is essential to the cubic count: simply eliminating P from the unshifted square makes a quartic equation. Also eliminating Delta together with F2 would make the strong equation quartic; the cubic construction eliminates C2 instead and retains Delta.

## 3. Single-polynomial statements and exact degree

For either literal residual list r1,...,re, take Q=sum(rj²), with exactly e terms. Over the integers or naturals, Q=0 iff every residual vanishes. Replace every positive unknown v by n_v+1 to obtain an equation over nonnegative integers, without adding variables or changing total degree.

For the 33-variable form the sum has exact degree four: the tau-root fourth power has coefficient one. For the 25-variable form the sum has exact degree six: its first-norm cubic contains −E*c*eta, so the squared monomial E²*c²*eta² has coefficient one, and no other residual contains these three variables together. A sum of squares of nonzero leading forms also proves the exact degree uniformly after every admissible specialization beta>0. These are literal finite polynomials, not computed ports, a quantifier-bearing formula, or an uncharged circuit-lift convention.

With the fixed Start-only compiler instantiated at the chosen ZFC contradiction recognizer, the inherited proof can be carried out in ZFC and gives, separately for each Q,

    Q has no nonnegative integer solution  iff  Con(ZFC).

This is conditional on the specified compiler and established Pell lemmas, as the prior construction was. Neither finite audits nor the preceding variable count is presented as an independent end-to-end formal proof assistant verification.

## 4. A further 20-variable / degree-eight tradeoff

`ordinary_octic20.json` eliminates thirteen registers from the ordinary33 system. It has the fifteen original positive witnesses and five retained registers E,c,a,V,I, hence 20 positive variables and 11 equations of degree at most four. The exact elimination trace is included. In more readable notation put q=beta*J+1, k=eta+zeta, H=4a+3, Delta=a²+H, C=q−F−alpha, and abbreviate the quadratic expression R=k−1−hE. Then the eleven equations are

1. a=E+s*q³.
2. E=w*q*(a−E).
3. c=k*(a−E)+eta.
4. tau²=E*(c−eta)*(E*(c−eta)+k)+1.
5. (w*q+a*c+gamma*H)²−Delta*c²=1.
6. R=((q−1)*(q−F)+alpha)*(q²−1)+(MC+q*MF)*J.
7. (K0+w)*C+q−F−z*(q−1)=1.
8. V=c*(T*f−1)−R*f².
9. I=i*c².
10. I²=Delta*(f²−1).
11. I²*(V²−y²)+y²=1.

Every expression expands to degree at most four. The symbols q,k,H,Delta,C,R here are explicitly defined polynomials, not additional coordinates; their substitutions are already made in the JSON. In particular R has degree two, so its occurrence in R*f² has degree four. The apparent degree-four main-norm terms a²c² cancel, but the remaining terms still have degree at most four without any use of another equation.

The retained positive original witnesses satisfy the ordinary source. Restoring the thirteen deleted registers by the trace gives all ordinary33 equalities. Their positivity follows as in Section 1 and the original lift: q>1, a−E=sq³>0, C>0, G>0, R>0 from the packed expression, f>2c, V0=Tf−1>0, Baux=I²>1, and the auxiliary norm then gives y²−V²>0 because V>1. Here V=1 is excluded by V≡−c modulo f and 2<c<f/2. Thus the projection and reconstruction are inverse positive-zero maps.

The sum of the eleven squared residuals has exact degree eight. The first equation contains −beta³*J³*s, whose square contributes beta^6*J^6*s², and no other residual contains s. This is nonzero for every admissible beta>0. The nonnegative shift therefore yields an exact degree-eight equation in twenty unknowns, with the same consistency equivalence. This is a tradeoff, not a replacement claim that degree eight is preferable to degree four or six.

