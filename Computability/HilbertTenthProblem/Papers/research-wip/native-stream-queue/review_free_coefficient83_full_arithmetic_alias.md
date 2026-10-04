# Independent review of the full arithmetic wrong-index diagnostic

**PASS, with the stated noncompiler scope.** The frozen [author proof](free_coefficient83_full_arithmetic_alias.md) constructs a full positive integer zero of the actual 83-gate polynomial whose main Pell index p differs from its computed packing index R. Its factors have the intended values `(1,1,1,1,1,1,Delta)`. The construction supplies the previously missing input and transport equations, including the shared positive rho/sigma split. It does not furnish a valid fixed-program recipe or a false accepted input for the universal compiler.

The [independent checker](review_free_coefficient83_full_arithmetic_alias.py) authenticates the author trio and five source/proof dependencies, reads only inert data, and executes no author or predecessor Python. It verifies the finite arithmetic with a different modular Pell implementation and proves the complete rational graph substitution by exact polynomial coefficient arithmetic. The [receipt](review_free_coefficient83_full_arithmetic_alias.json) records that evidence. No enormous complete Pell tuple is numerically evaluated.

## 1. Exact outer data and inherited first/main theorem

I read the entire frozen author proof and source, the scaled first/main obstruction proof, the native alias proof, and the relevant odd-quotient identities. The inherited scaled lemma is used only for the explicit family

    t=9159759548913079,
    p=t(t+2), n=t(t+1), R=2n-1,
    X=2^p, Y=2^(t+1),
    a=Y(X+1), A=a+2, Delta=A²-1,
    P=2XY²+1,
    (D,c)=(chi_A(p),psi_A(p)),
    (tau,k)=(chi_P(n),2psi_P(n)).

Its strict ratio proof establishes `kY<c<k(Y+1)` for every odd t≥11. That argument depends on X,Y,p,n, not on choosing q=16 in the earlier presentation. Here q=512³=2²⁷, so the supplied scales `w=2^(p-27)` and `s=2^(t+1-81)` are positive integers. The other retained ratio witnesses are `eta=c-kY` and `zeta=k(Y+1)-c`. They are positive and sum to k.

Since P≡1 modulo E=XY, the ordinary Pell recurrence gives `psi_P(n)≡n mod E`. Thus `h=(k-2n)/E` is integral; it is positive because `psi_P(n)>n`. This uses the actual chosen R=2n-1, giving the literal index factor 1. No positive-index recovery theorem is assumed to prove that same index equation.

My independent exact arithmetic gives

| Quantity | Value |
|---|---:|
| q, J | 134217728, 262657 |
| G=q²-qF-Z | 9314903847579751 |
| literal packed R | 167802389987808683282499692346639 |
| W, C | 8388608, 25972633 |
| alpha | 25844766 |
| w modulo q-1 | 4096 |
| K split as DC+B*DR | DC=410, DR=264 |

The packed R equals 2n-1 exactly and differs from p by t²-1. All stated mask residues, ranges, population count, packing bounds and positive input bound `2x<N` hold. The transport numerator is exactly divisible by q-1.

## 2. Shared input coordinates and positivity

For `g_j=chi_A(j)-a*psi_A(j)`, one has g0=1, g1=2 and

    g_(j+1)=2A*g_j-g_(j-1).

Induction gives a positive strictly increasing sequence and, for j≥1,

    g_(j+1)>(2A-1)g_j.

Modulo H=4A-5, the sequence 2^j has the same recurrence and initial values. Hence `g_j≡2^j mod H`. This proves integrality of the main quotient `(g_p-X)/H` and of the input quotient `(g_23-W)/H`, because W=2²³ is checked from the actual input/alpha rows.

The author gives a valid explicit lower bound for rho: `g_3=8A²-2A-2>H+A`, while `g_23≥g_3` and W<A. Also p>23 and A>X imply

    g_p-g_23 >= g_24-g_23 > (2A-2)g_23 > X.

It follows that rho is positive and that

    sigma = (g_p-g_23-X+W)/H > 0.

Thus the same two supplied coordinates simultaneously restore the input root and the main root. This is not an independent choice of unrelated Pell quotients.

For odd e=23, the integer-polynomial expansion of `psi_A(e)` in A² gives `psi_A(e)≡e mod Delta`; its strict growth gives `psi_A(e)>e`. Hence the supplied input delta is a positive integer. The exact source input root and index become `chi_A(23)` and `psi_A(23)`, respectively. Its norm is 1.

The transport quotient is integral by the finite congruence in Section 1. Its numerator is strictly positive since C>0, K+w>0 and q-F-1≥0. No positivity or divisibility in these steps is borrowed from the 84-operation parent.

## 3. Independent noncoprime CRT and auxiliary proof

My modular Pell calculation uses powers of the recurrence matrix

    [[2A,-1],[1,0]],

rather than the author's quadratic-ring multiplication. It computes

    c mod p  = 36618251610398372242942694064198,
    c mod 4p = 288321836592111424645970879323395,
    gcd(c,p) = gcd(c,4p) = 3.

An independent extended-Euclidean inverse gives

    j=105345483961408813243095246968108,
    v=R+c*j,
    v≡p mod 4p.

The displayed nonnegative j makes v>0 without constructing c. Also v≡R mod c and v≡3 mod4. The compatibility condition is exact: 3 divides R-p. The parity statement follows independently from even A and odd p, which make c odd.

Take f=D and S=Delta*c. The main norm gives

    Delta*f²-S²=Delta,
    gcd(c,f)=1,  f²≡1 mod c.

For odd v=2m+1, the pinned odd-quotient polynomial satisfies

    chi_S(v)/S=Q_m(S²),
    Q_m(0)=(-1)^m*v,
    Q_m(1-A²)=(-1)^m*psi_A(v).

Here m is odd. Modulo c, S² vanishes, so `V=chi_S(v)/S≡-R`. Modulo f, S²≡-Delta=1-A². In the coefficientwise quadratic ring modulo f, writing `epsilon=A+sqrt(Delta)`, one has

    epsilon^p ≡ c*sqrt(Delta),
    epsilon^(2p) ≡ -1,
    epsilon^(4p) ≡ 1.

Therefore v≡p mod4p implies `psi_A(v)≡psi_A(p)=c mod f`; it follows that V≡-c mod f. This argument uses no division by 2 and is valid even though f is even.

Consequently `(V+c+R*f²)/(c*f)` is an integer, by the two congruences and gcd(c,f)=1. It is positive. Together with `y_aux=psi_S(v)`, it gives the exact emitted auxiliary argument and auxiliary norm 1. All 18 supplied witnesses are thus specified positive integers. No auxiliary sign or inverse-index premise is left unstated.

## 4. Complete source proof, independent of the author's numerical tests

The checker reads the pinned 83-row array and gives its original free ports a formal rational assignment using independent variables for X,Y,k,c,D,tau,W,kappa,mu,V,f,S and the remaining outer data. In particular it substitutes

    w=X/q, s=Y/q³,
    eta=c-kY, zeta=k-eta,
    rho=(mu-a*kappa-W)/H,
    sigma=(D-a*c-X-mu+a*kappa+W)/H,
    delta=(kappa-u)/Delta,
    h=(k-R-1)/(XY),
    transport_quotient=((K+w)*(Z+W)+q-F-1)/(q-1),
    auxiliary_quotient=(V+c+R*f²)/(c*f).

Here q, a, H, Delta and R are the actual source formulas. The formal rational identities require q, q-1, H, Delta, XY and cf nonzero; all are strictly positive in the proof-defined specialization above.

Every gate is evaluated with exact sparse polynomial numerators and denominators. At 37 identified cuts the checker verifies equality by coefficientwise cross-multiplication before replacing the expression by its simpler equal form. It checks the seven complete factor polynomials as

    tau²-XY²(XY²+1)k²,
    D²-Delta*c²,
    mu²-Delta*kappa²,
    S²V²-(S²-1)y²,
    1,
    1,
    Delta*f²-S².

It also checks the whole finalizer against their product minus Delta, including a complete expanded 726-monomial polynomial digest. This is an exact rational-function identity for the triangular assignment, not a general all-ring identity at vanishing denominators. The Pell specialization makes the displayed factor values `(1,1,1,1,1,1,Delta)` and therefore makes the actual full output zero.

All 83 paid rows, all 25 supplied ports, closure, and complete liveness are checked. The direct recount is 46M+37A. No source array or historical builder is modified or executed. The independent review does not rely on the author's 16 off-zero rational tests to establish the graph identity.

## 5. Exact scope and reproduction

The b=5,d=9 choice fails the required integral radix layout `B=(2^b)^L`, since 5 does not divide 9. The powers-of-five width recipe also fails. Necessary bit masks and outer arithmetic therefore cannot be relabeled as an admissible program. This result rules out recovery of p=R from the displayed arithmetic constraints alone; it does not settle the 83-gate candidate on valid fixed-program slices or change any established universal bound.

The witness description is constructive and exact, but its huge Pell integers are not numerically expanded. Indeed `psi_A(p)>2^(p(p-1))`, from A>2^p and the inherited elementary lower bound. The executable evidence consists of finite modular/outer arithmetic and the independent formal source identity. This distinction is preserved in both receipts.

The checker authenticates all frozen author and dependency bytes on every invocation. Fresh normal and optimized typed receipt replays from `/` pass:

```sh
python3 review_free_coefficient83_full_arithmetic_alias.py --root ABS_WIP --expect ABS_REVIEW_JSON
python3 -O review_free_coefficient83_full_arithmetic_alias.py --root ABS_WIP --expect ABS_REVIEW_JSON
```

Before installation, `--author-root /tmp` reads the same pinned author bytes there. All checks use explicit exceptions, including the JSON type-exact comparison. No finding remains in the reviewed source, proof or stated scope.
