# Independent positive-zero proof for the auxiliary quotient85

**PASS: the normalized85 construction has a bijection with the full positive integer zero set of its specified transport-shear86 parent, at the same ordinary input and valid fixed-program numerals.** No positivity assumption about the restored coordinates, no binary typing, and no zero of the parent polynomial is used prematurely. The author’s ordinary relaxed-rank route is valid. A shorter, direct normalized-rank proof is given below.

This is an independent mathematical review of [the source-specific construction](complete85_auxiliary_bezout_projection.md), with a [bounded checker](review_complete85_auxiliary_bezout_math.py) and [receipt](review_complete85_auxiliary_bezout_math.json). It authenticates the author trio and the proof dependencies, checks the literal mathematical interface, and counts the85 paid instructions and18 witnesses. It does not duplicate the separate complete API or exact-degree audit. In particular the author’s degree175 claim is not established merely by the small mathematical fixtures here.

## Scope and literal interface

The domain is the strictly positive ordinary input and strictly positive supplied witnesses. Fixed numerals satisfy the entire existing complete75 compiler recipe; this review does not replace that recipe by a few necessary numerical inequalities. In particular B=2^d≥16, J>0, Kconstant>0, the input scale is positive, and the actual shifted mask convention is retained. The current source computes

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A²−1, H=4a+3,
    D=X+ac+(rho+sigma)H.

The source names for Delta,c,k,E,a,D,R,K are respectively `A`, `R10a`, `R10b`, `UM`, `R12`, `R14`, `r_lhs`, `index_difference`; K=k−hE. This distinction between the Pell parameter A and register `A` matters. In particular D is positive before any norm equation, even though the input-norm root may be signed.

The child replaces the only supplied o,j consumers by positive T=`auxiliary_quotient` and

    V=c(Tf−1)−Rf²,
    Ns=f²−Delta*i²*c⁴,
    Kaux=Delta²*i²*c⁴,
    Na=Kaux*V²−(Kaux−1)y².

The other retained factors are the first, main, input, index and transport factors. There are seven factors altogether. The child is their product minus1. The index factor is Nk=K−R. The transport factor is the already reviewed shear

    Nt=(Kconstant+w)C+q−F−t(q−1),
    C=q−F−Z−alpha−2dx,

where t is the positive `transport_quotient`, distinct from T. The checker reads the complete parent and child JSON arrays and verifies these actual ports and the literal retained instructions. It does not execute ancestor Python.

## 1. Algebraic restoration is not an off-zero positive map

Define integer polynomial expressions

    o=cT−Rf,
    j=Tf−R*Delta*i²*c³−1.                            (1)

Exact expansion gives

    of−c=V,
    V+R−cj=R(1−Ns),
    V−cj+K=Nk+R(1−Ns).                              (2)

Consequently the full parent and child polynomials obey

    Fparent(restored)+1
      =(Fchild+1)[Nk+R(1−Ns)].                       (3)

Every retained factor is the same under (1); o,j had no additional source consumers. This is a correction identity, not polynomial equality. Before the unit equations and sign proof below, (1) need not be positive, and (3) does not show that a child zero is a parent zero.

## 2. Unit signs and the untyped packing bounds

At a child zero all seven integer factors are units. Five are necessarily+1:

* Main and input norms cannot equal−1 modulo4 since Delta is0 or3 modulo4; the input root need not be positive.
* The normalized strong norm has the same exclusion, so Ns=1.
* Kaux is a square, hence0 or1 modulo4. Therefore Na is congruent to y² or V² modulo4, excluding−1 without an assumption on V.
* The first norm is `tau²−u(u+1)k²`, u=XY²>1. The negative equation admits a strict descent: for positive x,k satisfying it, uk<x<(u+1/2)k. Thus k'=(2u+1)k−2x is a positive integer less than k. With x'=(2u+1)x−2u(u+1)k, the norm remains−1; replacing x' by its nonzero absolute value gives a smaller positive solution. Hence the negative norm is impossible.

Write Nk=epsilon and Nt=nu. Their product is1, so nu=epsilon, but neither sign is fixed yet.

The last two terms of Nt equal `1−F−(t−1)(q−1)≤0`. Since Kconstant+w≥2, C≤−1 would make Nt≤−2. Thus C≥0 and F+Z<q. This uses only the unit magnitude and supplied positivity.

For the actual shifted packing

    G=q²−Z−qF,
    R=G(q²−1)+(MC+q(MF0+B−1))J,

the compiler mask sizes give `2q−1≤G≤q²−q−1` and `0<(MC+q(MF0+B−1))J<(q−1)(1+2q)`. Therefore

    (2q−1)(q²−1)<R<q⁴−q³,
    3q+1<R−2<R+2<q⁴≤E,
    a=E+Y>R+2, Delta>R>0.                           (4)

These are ordinary integer inequalities. No conclusion q=2^t or q=B^N is used. The strict room R+2<E is what later excludes wraps; the older symmetric estimate E>2R is unnecessary.

## 3. The new auxiliary argument is positive without a rank theorem

From Ns=1,

    f²=1+Delta*i²*c⁴.

The computed c=kY+eta is greater than2, and Delta≥1, i≥1. Consequently f>c²>2c. Also

    Kaux=Delta(f²−1),
    Kaux−(Rf²+c)
       =(Delta−R)f²−Delta−c
       ≥1+Delta(i²*c⁴−1)−c>0.                       (5)

Only (4), integrality and supplied positivity have been used.

Here is an elementary root gap. For integers H>1, y>0 and V satisfying

    H*V²−(H−1)y²=1,

V=0 is impossible. If v=|V|>1 then `y²−v²=(v²−1)/(H−1)>0`, hence y≥v+1. It follows that

    v²−1≥(H−1)(2v+1).

If 1<v≤2H−2, the left side minus the right side equals `v(v−2H+2)−H<0`, a contradiction. Thus |V|≥2H−1. This argument is purely integral; no Pell classification or previously positive auxiliary root is assumed.

Apply it with H=Kaux. The source formula and T≥1 give V>−Rf²−c, whereas (5) excludes every negative value with |V|≥2Kaux−1. The cases V=±1 are excluded separately: V≡−c modulo f, but 0<c−1<c+1<f. Hence V>0.

The polynomial o in (1) is an integer and `of=V+c>0`, so o>0. At Ns=1, the second identity in (2) gives `cj=V+R>0`; therefore j>0 as well. These are established before the main/auxiliary rank and without asserting Fparent=0. The same identities give the useful congruences V≡−c (mod f) and V≡−R (mod c).

## 4. A direct normalized rank proof

Put P=2XY²+1. The first norm's fundamental positive unit has first coordinate P and coefficient2, so

    tau=chi_P(n), k=2psi_P(n), n≥1.

A coefficient1 solution would place a square strictly between u² and (u+1)²; coefficient2 gives P. This proves the stated fundamental unit. Since P≡1 (mod E), the recurrence gives psi_P(n)≡n (mod E). The index unit therefore implies

    2n=R+epsilon+vE, v≥0,
    n≥(R−1)/2≥24.                                   (6)

Here v<0 is excluded by `0<R+epsilon<E` from (4).

The main norm has positive root D, so D=chi_A(p), c=psi_A(p) for p≥1. Since P>A and c>k, monotonicity forces p>n. In particular p≥25, and Pell growth gives c>2p. Independently, k=R+epsilon+hE and h≥1 give c>kY>2R.

Now exploit normalization directly. Ns=1 and positive i,c,f give

    f=chi_A(m), psi_A(m)=i*c²                         (7)

for some m≥1. The fundamental positive unit at discriminant A²−1 is A+sqrt(A²−1), as any positive second coordinate gives first coordinate at least A. Standard strong divisibility follows directly from the Pell addition identity and the Euclidean algorithm:

    gcd(psi_A(r),psi_A(s))=psi_A(gcd(r,s)).

Since c=psi_A(p)>1 divides psi_A(m), strict growth forces p|m. Write m=pk0. Expanding `(D+c*sqrt(Delta))^k0` gives

    psi_A(pk0)/c ≡ k0*D^(k0−1) (mod c).

The left side is divisible by c by (7), and gcd(D,c)=1 by the main norm. Thus c|k0 and in fact **pc|m**. In particular c|m and m≥pc>2p.

This direct rank proof is stronger than the ordinary relaxed-rank conclusion needed here. It does not assume c>A*Delta² or use an old complete-parent zero. The author's alternative route first establishes that larger bound and uses i_ordinary=Delta*i in the authenticated relaxed-rank proof; that route also has its hypotheses in the correct order.

## 5. The auxiliary congruences identify p=R

Set S=Delta*i*c²>1. The auxiliary equation is

    (SV)²−(S²−1)y²=1.

Since V,y are positive, Pell classification gives SV=chi_S(ell), y=psi_S(ell). The divisibility by S forces ell odd, since chi_S(2h)≡(−1)^h (mod S). Write ell=2h+1. The integer polynomial Q_h defined by

    Q_0(z)=1, Q_1(z)=4z−3,
    Q_(h+2)(z)=(4z−2)Q_(h+1)(z)−Q_h(z)

satisfies V=Q_h(S²), `Q_h(1−A²)=(−1)^h psi_A(ell)` and `Q_h(0)=(−1)^h ell`. These are the recurrence identities in the pinned half-parameter proof, not division in residue rings.

Since S²=Delta(f²−1), reduction modulo f and V≡−c imply, after squaring and doubling,

    chi_A(2ell)≡chi_A(2p) (mod f), f=chi_A(m).        (8)

For completeness, reduce ell to ±z+k0*m with 0≤z≤m/2. The Pell pair at2m is (−1,0) modulo f, so (8) compares ±chi_A(2z) with chi_A(2p). If2z=m, the former is0 modulo f, impossible. Otherwise both positive representatives are less than f/(2A−1), because 2z,2p≤m−1. Their sum is less than f; a negative sign is impossible and a positive congruence forces equality. Strict growth gives z=p. Thus ell≡±p (mod m), and hence modulo c.

Also c|S. Reducing Q_h(S²) modulo c and using V≡−R gives R≡±p (mod c). But both R and p lie strictly between0 and c/2. Therefore **p=R**. This is the local signed step-down argument with the target R, not an invocation of the complete kernel or compiler theorem.

## 6. The index sign and both inverse maps

With p=R and n<p, (6) cannot have v≥1: then `2n≥R−1+E>2R`, a contradiction. Therefore2n=R+epsilon. If epsilon=−1, p=2n+1. Let Q=2A²−1. Explicitly,

    Q−P=2Y²(X²+X+1)+8Y(X+1)+6>0,
    A>Y+1.

Pell duplication gives

    psi_A(2n)=2A*psi_Q(n)≥2A*psi_P(n)=A*k.

It follows that `c=psi_A(2n+1)>A*k>k(Y+1)`, contradicting `kY<c<k(Y+1)`, which follows from eta,zeta>0. Thus epsilon=1, and also nu=1. The restored linear factor in (2) is now1. Equation (3) therefore proves a full positive zero of the exact parent. Only at this point is the parent's universal ordinary-input theorem invoked.

Conversely, at any positive parent zero the reviewed parent sign theorem gives Ns=Nk=Nlinear=1. Hence

    of+R=c(j+1), f²≡1 (mod c).

Multiplication of the first congruence by f gives `c|(o+Rf)`. Thus

    T=(o+Rf)/c>0

is an integer. This value reconstructs V exactly, all seven child factors are1, and the child is zero. Formula (1) recovers the original o. At Ns=1 the equality cj=V+R uniquely recovers the original j. Conversely this forward formula recovers the original T from every child zero.

This proves a **bijection of the entire supplied positive integer zero sets**, with ordinary x and every retained coordinate fixed. It is not merely a fresh-witness existence theorem. It is not an unconditional map of positive orthants, an all-integer zero theorem, or a polynomial identity without correction.

## Executable evidence and limits

The checker is standard-library-only and rejects optimized Python because assertions implement its checks. It strictly authenticates the three frozen author files and every listed parent/proof file, including current bytes of the1980 proofs; it imports none of them. It checks the actual retained source rows, removed coordinate consumers, new local formula, seven-factor tail, explicit polynomial identities, and the85=48M+37A/18-witness ledger.

Finite supplementary checks cover the norm residues modulo4, the elementary auxiliary root-gap inequality, the direct strong size margin, asymmetric no-wrap cases, the negative-index ratio inequality, and normalized rank/binomial examples. Four independently constructed exact Pell fixtures exercise positive o,j,T and both maps for the auxiliary/main/strong subsystem. They are explicitly not full compiler zeros and do not carry any ordinary-input acceptance claim. The general arguments above prove the domain and sign statements; the finite checks do not substitute for them.

The checker does not call author verification, historical verifiers, or a general compiler builder. It does not independently audit public API behavior or uniform exact degree. Those remain the separate full-source review scope. In this mathematical scope no defect remains.

    python3 review_complete85_auxiliary_bezout_math.py --root /absolute/path/native-stream-queue --author-root /absolute/path/native-stream-queue --expect /absolute/path/review_complete85_auxiliary_bezout_math.json
