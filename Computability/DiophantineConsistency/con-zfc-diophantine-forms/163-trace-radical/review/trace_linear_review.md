# Independent mathematical review: a linear strong trace in the auxiliary Pell code

Prepared 25 October 2026 by a separate AI research agent. This is an ordinary mathematical review within the AI-assisted workflow, not outside human peer review or a proof-assistant certificate.

## Reviewed change and conclusion

The component is `agent_frontier/trace_component`. Its retained source boundaries are:

- `inherited/lucas/parent/PROOF.md` for the q^3 charts;
- `inherited/cofinal/PROOF.md` for the q^2 and first-order q charts;
- `inherited/lucas/PROOF.md` for the second-order Lucas q chart;
- `inherited/lucas/parent/proof_sources/universal_pell.tex`, especially the signed auxiliary-index, normalized-rank, and positive auxiliary reconstruction lemmas.

The sole semantic change in the auxiliary ordinate is

    V_old=f^2(c T_old-R)-c,
    V_new=f(c T_new-R)-c,
    f=1+2a,  a=Delta i^2 c^4 E.

The quantities G=E(1+a), Q=4 Delta^2 U^2 G=Delta(f^2-1), and U=ic^2 retain their old meanings. The literal producer was inspected: the old `Fsqr` register is used only by the multiplication forming V; Q is formed from the separate `fouraF0` register. The finalized graph shares the existing F0=1+a and computes f=a+F0 with one addition, replacing the old single `Fsqr` addition. It therefore does not replace Q by Delta(f-1), and does not add an arithmetic operation. The final five supplied operation/degree labels are 75/402, 76/352, 79/290, 80/258 and 87/232; the algebraic degree reductions reviewed below are unaffected by this exact gate sharing.

**Mathematical conclusion: PASS** for the trace replacement, including both transport weights, negative Lucas ranks, and strictly positive completeness, composed with the explicitly retained source calibration. This review does not independently certify the numerical operation/degree counts or the native coefficient reconstruction.

## 1. Root extraction is unchanged

For positive inputs, q>=32, X,Y>=q, k>=2, c=kY+eta>kY, U>=c^2, E>1, and Delta>0. In particular a>c and

    f=1+2a>2c.

For any integer b=cT-R, V=fb-c is nonzero and |V|>1. The identities involving Q and G remain exactly those of the parent. At a zero of the polynomial,

    (Q-1)z^2=G(Q V^2-1).

The unchanged prime-valuation argument forces G=g^2 with g a positive integer, and coprimality gcd(E,1+a)=1 then gives E=tau^2 and 1+a=f0^2. The unchanged adjacent-Pell descent forces y=|z|/g integral. Thus

    Q V^2-(Q-1)y^2=1,
    f^2-Delta I^2=1,
    I=2Ug, Q=(Delta I)^2, c^2 | I.

The old signed all-index folding proof uses only V=-c modulo f, not modulo f^2. That congruence is retained. It supplies c=psi_A(p), with p a positive odd index, before any sign of the outer rank R is known.

## 2. The rank-identifying congruences remain valid

The explicit polynomial f satisfies

    f=1 mod c

because f-1=2Delta i^2 c^4 E. Consequently the new V obeys

    V=-c mod f,   V=-R mod c.

The retained signed auxiliary-index lemma states exactly these congruences, together with the strong norm, normalized rank divisibility, and 0<p,R<c/2. It does not require V to contain f^2. The normalized rank lemma uses c^2|I and is also unchanged. After the transport argument has established C>0 and the inherited outer bounds 3q<R<q^4-2, the same c>2R bound and these congruences therefore give p=R.

This is the decisive point: a congruence modulo f is sufficient for soundness, while the old square was stronger than required.

## 3. Absolute transport bounds with the smaller coefficient

The first Pell norm still gives k=2psi_(2XY^2+1)(n0). Excluding n0=1 as in the parent yields c>8XY^3>=8q^4, and hence c>X and K>0. These facts are independent of R and B.

If b=0, then V=-c and the adjacent norm gives

    y^2-c^2=(c^2-1)/(Q-1),

strictly between 0 and 1, impossible. Therefore b is nonzero and sign(V)=sign(b).

Put D0=Delta U^2. Since a=D0 E and g^2=E(1+a),

    a^2/g^2 = D0*a/(1+a) > D0/2 > 9.

Thus a>3g. Since f-c=1+2a-c>a, one obtains

    |V|>3g, |V|>|b|, y<(3/2)|V|.

For L=V^2 these imply gy<L/2 immediately.

For L=bV one needs a lower bound on |b|. The parent's exclusion of p=3 depends only on X,Y,k,c, not V, and hence is unchanged. For clarity, with p=3 the case n0>=3 contradicts c<16X^2Y^2<32X^2Y^5<kY<c. In the case n0=2, setting u=X+2-2Y gives

    eta=4Y^2(Xu+1)+8Y(X+1)+3-4Y.

The interval 0<eta<k forces u=0 or 1; then 2Y-X is 2 or 1, impossible since q divides X,Y and q>=32. Thus p>=5 and c>c3=4Delta+3.

Write S=Delta I, so Q=S^2. The adjacent Pell classification gives |V|=chi_S(j)/S for odd j. Index 1 is excluded by |V|>1. Index 3 would give |V|=4Q-3 and, according to the sign of V, one of

    f(b-4Delta f)=c-c3,
    f(b+4Delta f)=c+c3.

Both right-hand sides are strictly between 0 and 2c<f, impossible. Thus j>=5 and |V|>8Q^2. Since Q=Delta(f^2-1)>f^2 and c<f/2,

    |b|>(8Q^2-c)/f >8f^3-1/2 >4g.

It follows that L=bV=|b||V|>0 and gy<(3/8)L<L/2. For either transport weight, |b|/D<L/2 for the relevant carrier denominator D>2.

## 4. Ordinary transports

For the charts without the cubic Lucas correction, the rational carrier is

    z=n+kappa+sigma-(1+hL)B/h-rho,

with sigma=0 in the q^3 chart and sigma>0 in the lower-scale charts. The uncorrected error satisfies rho<|b|/D before any integrality of rho is used. If B<=-1, then (1+hL)B/h<=-L-1/h, and the preceding absolute bounds force n<0. Therefore B>=0. Since B=(K0+Wbase)C-F and F>0, this implies C>0.

All later first-order index, denominator, projection and native reconstruction arguments involve only the unchanged outer variables and the two congruences in Section 2. Their hypotheses remain present.

## 5. Negative ranks in the second-order Lucas chart

Here X=wq, Y=qs, v=XY^2=wq^3s^2, and the rational correction is

    rho=[k-R-1-v(R+1)(R-1)(R+3)/6]/q^6.

The only integer ranks with (R+1)(R-1)(R+3)<0 are R<=-4 and R=0. They cannot be dropped from a soundness proof.

If the cubic product is nonnegative, then rho<|b|/q^6 and the ordinary transport argument applies.

For R=-r<=-4, the exact outer identity

    R=(hC+q alpha)(q^2-1)+(MC+q MF)J

implies C<0 and |C|>r/q^3. It also gives B<=-1-w|C|. The adverse cubic correction is

    delta0=v(r-1)(r+1)(r-3)/(6q^6)
          < w s^2 r^3/(6q^3).

Now b=cT+r>c and b>r, so the new linear trace still gives

    V=fb-c>(f-1)b,
    L>(f-1)r^2

for either weight. The crucial residual domination needs only f-1>s^2, and this follows from f-1=2a and Delta>Y^2>=s^2. Consequently

    w|C|L > w(f-1)r^3/q^3 >delta0.

Using gy<L/2 and |b|/q^6<L/2 in the exact carrier again forces n<0. Thus no positive zero occurs in this rank case.

For R=0, the same outer identity gives C<0 and |C|>=1. Here b=cT>=c and V>=(f-1)b, so L>f-1. The adverse correction is only v/(2q^6)=w s^2/(2q^3), strictly below w|C|L. The same contradiction follows.

Therefore every positive zero of the Lucas trace-linear polynomial also has B>=0 and C>0. Its subsequent second-order congruence argument, including its prime-2 and prime-3 treatment, is unchanged: that argument uses the integral carrier, c=psi_A(R), and outer bounds, rather than the old f^2 coefficient of V.

## 6. Canonical strictly positive completeness

The old auxiliary construction supplies a positive adjacent Pell solution (V,y) with

    V=-c mod f^2, V=-R mod c,

where R>0 and the strong trace satisfies f=1 mod c. Therefore

    T_new=(V+c+Rf)/(cf)

is an integer: the numerator is divisible by f because V+c is, and is divisible by c because f=1 mod c; gcd(c,f)=1. All terms in the numerator and the denominator are positive, so T_new>0. It satisfies f(cT_new-R)-c=V exactly.

The remaining canonical witnesses are unchanged. In particular g>kappa+sigma, and

    n=gy+(1+hL)B/h+rho-kappa-sigma

is a strictly positive integer by the retained integral/nonnegative canonical budgets. This proves completeness in the actual positive domain.

## 7. Stronger explicit polynomial map from the parent zero set

There is also an exact polynomial substitution taking every parent positive zero to a new positive zero; this avoids having to rely on an unproved inverse shift.

Let

    d=2Delta i^2 c^3 E, so f=1+cd.

Given any parent tuple, define

    T_new=f T_old-dR.

Then, as identities of integer polynomials,

    b_new=cT_new-R=f(cT_old-R)=f b_old,
    V_new=f b_new-c=f^2 b_old-c=V_old.

For L=V^2 keep n_new=n_old. For L=bV put

    n_new=n_old+(f-1)L_old B.

Then L_new=f L_old and

    n_new-L_new B=n_old-L_old B.

All remaining variables and abbreviations are unchanged, so the entire new polynomial, after this substitution, equals the entire parent polynomial. On a parent positive zero, the retained soundness proof gives R<c/2, B>=0 and b_old,V_old>0. Thus

    T_new=f T_old-(f-1)R/c > f-(f-1)/2>0,
    n_new>=n_old>0.

This establishes a fully explicit polynomial map between the relevant zero sets in the needed direction. No assertion that every new zero lies in its image is made.

## Scope

The review validates the unbounded mathematics specific to the trace-linear change and checks the precise inherited lemma hypotheses. The final written `PROOF.md` was read through its soundness, canonical completeness, polynomial source-map, and degree sections and agrees with this review. The final release must additionally authenticate the literal DAGs, their costs/degrees, all four coherent fixed coefficients, and the retained calibration provenance. Such finite checks complement rather than replace this ordinary proof.
