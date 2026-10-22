# A 28-unrestricted-integer gap-norm equation

## Result and scope

There is a fully specified polynomial in 28 unrestricted integer unknowns, exact total degree 426, evaluated by the literal 127-operation circuit `integer28_gap_norm127_degree426.json`, such that ZFC proves that its lack of integer zeros is equivalent to Con(ZFC). The operation ledger is 66 multiplications and 61 additions/subtractions, charging every binary operation including multiplication by fixed numerals. This improves the 29-integer count in repository package 14, with a higher-degree tradeoff.

This is an ordinary mathematical reduction using the repository's existing Pell, blank-tableau and exact-machine calibration theorems. It is not a newly kernel-certified theorem, a consistency proof, or a global minimum claim. The enormous four coefficients are fixed integers, not variables. The original baseline uses finite recipes, while the compact primary backend below is explicitly materialized.

All upstream sources are pinned to ProveIt commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. The derivation below uses the original coherent package-06 coefficient quartet, recorded in `upstream/14-integer29/vendor/blank67/k215_constants.json`. The primary instantiated equation instead uses the audited complete compact Wang943 tuple selected by `COEFFICIENT_BINDINGS.json`, with signed-domain transfer explained in `COEFFICIENT_TRANSFER.md`. Its `MF` port is the shifted mask. No individual ports from different compiler tuples are mixed. The original recipe references the literal K215 transition relation and finite compiler definitions in the pinned repository; the recipe JSON is not a standalone expansion of those source definitions.

## 1. Definitions

Retain seven positive ports

    J, F, alpha, z, s, eta, zeta.

Let h,T,tau,e,gamma,r,u be unrestricted integers and put i=2r+1 and w=u². The resulting mixed-domain construction has fourteen coordinates, before expanding the seven positivity ports. Use the standard polynomial abbreviations

    q = beta J + 1,          C = q-F-alpha,
    X = wq,                 Y = s q³,
    E = XY,                 k = eta+zeta,
    c = kY+eta,             a = E+Y,
    H = 4a+3,               Delta = a²+H,
    Dmain = X+ac+gamma H,    L = E kY,
    R = ((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    N0 = tau²-L(L+k),       N1 = Dmain²-Delta c²,
    Nk = k-hE-R,            Nt = (Kconstant+w)C+q-F-z(q-1).

Here beta is the fixed port Bm1. Set

    Q = (Delta i c²)²,      d = 1+Delta i²c⁴,
    b = c+Rd,               v = cT,
    S = Q-1,                r_gap = b+S e,
    p = d v²,
    A = p+r_gap²-Q S e²-1,
    B = 2v r_gap,
    Kgap = A²-d B²,
    P4 = N0 N1 Nk Nt.

The mixed-domain equation is

    P4(1+Kgap)-1 = 0.

The evaluator computes d B² as 4 p r_gap² and hence does not need a B register. The useful exact cancellation is

    A = p+b²+S e(2b-e)-1.                                      (1)

For any f with f²=d and V=vf-b,

    A-Bf = Q[V²-(V+e)²]+(V+e)²-1.                            (2)

Both are polynomial identities; they do not depend on any sign premise.

## 2. Outer signs and the zero-square boundary

At a zero, all five integer factors N0,N1,Nk,Nt,1+Kgap are units. Since B is even, Kgap is a square modulo four. Thus 1+Kgap cannot equal -1 and Kgap=0.

For u!=0, the usual consecutive-product lemma excludes N0=-1. At u=0, X=E=L=0 and N0=tau², which also excludes -1. As Delta=(a+2)²-1 is 0 or 3 modulo four, the elementary Pell-norm congruence excludes N1=-1. Therefore N0=N1=1 and Nk=Nt=epsilon for epsilon in {-1,1}.

Already a=Y when u=0 and Dmain=ac+gamma H. Reducing N1=1 modulo H gives

    1 = Dmain²-Delta c² = (ac)²-a²c² = 0 modulo H.

But H=4Y+3>1. This contradiction proves u!=0, so w>=1 and X>=q.

Now apply precisely the weak-transport bootstrap of package 14, which allows the two common unit signs and signed h. It gives C>=0 and

    q>=16, 3q+1<R<q⁴-2, E>=q⁴>R+2, a>R+2.

Since k=R+epsilon+hE>0, negative h would make k<=R+1-E<0. Thus h>=0 and k>=R-1. In particular c>2, 0<R<a<Delta, and c>2R. These arguments precede any restoration of f and use no auxiliary-gap sign.

## 3. Both root-denominator factors are nonzero

The odd multiplier i is nonzero. Consequently Q>1 and d>1. Since R,c are positive, b>2. Moreover

    Q-b = (Delta-R)d-Delta-c
        >= d-Delta-c
         = 1+Delta(i²c⁴-1)-c > 1.

The last strict inequality uses |i|>=1, Delta>0 and c>2. Hence

    2 < b < Q-1 = S.

It follows immediately that r_gap=b+S e is nonzero for every integer e: a zero would require the nonzero residue b modulo S to vanish.

Suppose T=0. Then v=p=B=0, and Kgap=0 forces A=0. Formula (1) rearranges to

    Q b²-(Q-1)(e-b)²=1.                                      (3)

Put y0=e-b. Since b>1,

    (Q-1)(y0²-b²)=b²-1>0.

Therefore |y0|>=b+1, yielding

    b²-1 >= (Q-1)(2b+1) > b²-1,

where the final strict inequality follows from Q>b. This contradiction proves T!=0. Thus B=2cT r_gap is nonzero. Every division below is now by an established nonzero integer.

## 4. Soundness by exact restoration

Since Kgap=0, the rational number f=A/B has f²=d, an integer. A rational number whose square is integral is itself an integer, by reducing the fraction to lowest terms. No sign assertion about f is made or required.

Set V=vf-b and y=V+e. As f²=d,

    V = cTf-c-Rf² = c(Tf-1)-Rf².

Identity (2) and A-Bf=0 give

    Q V²-(Q-1)y²=1.

Also f²=d says

    f²-Delta i²c⁴=1.

Thus we have restored exactly the normalized strong and auxiliary equations. Together with P4=1, these give the normalized package-14 product on its proven enlarged signed domain: the seven named positive ports, odd i, square w, and otherwise unrestricted f,h,T,tau,y,gamma. Its signed-domain theorem therefore recovers a valid blank K215 tableau. The delicate signed main-root and auxiliary-quotient arguments are inherited from that theorem, not replaced by an invocation of a positive-only parent theorem.

In particular, one must not assume gamma>=0 or f,T,y>0, and one must not apply an unmodified positive-domain theorem after root restoration.

## 5. Completeness with the odd and square restrictions

Package 14's signed-domain proof provides canonical witnesses from any accepting blank K215 computation with all seven retained ports positive, odd i and square w. Its completeness construction takes the strong Pell index m=cR, where canonical R and c are odd. The divisibility c²|psi(cR), followed by parity, makes i=psi(cR)/c² a positive odd integer. The canonical temporal/spatial padding uses powers of five, so the dyadic cell exponent t is odd. Canonical R is odd, hence w=2^(R-t) is an integer square. These are existence-preserving choices, not assertions about every old witness tuple.

For these canonical normalized witnesses, put

    e = y-V.

No sign requirement is imposed on e. Formula (2) gives A=Bf, and consequently Kgap=0; the four outer norms equal one. Deleting f and replacing y by e produces the required fourteen-coordinate mixed-domain zero.

Thus the mixed-domain equation has a solution exactly when the calibrated blank machine halts, exactly when a finite ZFC refutation exists. Negating the existence equivalence yields the claimed consistency equivalence within ZFC, with the same formalizability boundary as the pinned source.

## 6. Conversion to 28 unrestricted integers

For each of J,F,alpha,z,s,eta,zeta independently substitute

    Pos(a,b,c) = 1+a²+b²+c(c+1).

It is positive on all integer inputs. It is surjective onto the positive integers: Legendre's three-square theorem represents 4n-3 by three squares, exactly one odd and two even modulo four; writing those as (2c+1)²,(2a)²,(2b)² gives the formula. This proof is invariant under permutation of the three square summands.

Seven triples and the seven free coordinates h,T,tau,e,gamma,r,u give 7*3+7=28 unrestricted integers. Seven positivity circuits cost 49 operations. The affine i replacement costs two and the w square costs one. Added to the 75-operation pinned gap norm, this is 127 operations, with 66 multiplications and 61 additions/subtractions. Every gate and every input port is live.

## 7. Exact degree, including cancellations

Give the seven positive original ports weight two, i and all other signed original coordinates weight one, and w weight two. The actual substitutions have precisely these degrees. The relevant degrees before the positivity expansion are

    q=2, k=2, X=4, Y=8, E=12, c=10, a=12, Delta=24, R=8;
    L=22, N0=44, N1=35, Nk=13, Nt=4, P4=96;
    Q=90, d=66, b=74, v=11, p=88, S=90, r_gap=91;
    A=165, B=102, Kgap=330, P4(1+Kgap)-1=426.

The N1 degree uses the exact cancellation

    N1=(X+gamma H)²+2ac(X+gamma H)-Hc²,

whose unique top contribution is 2ac gamma H. The A degree uses (1); its unique top contribution is 2Q e b. The other term dB² has degree 270, strictly below A²'s 330. These facts prove the upper bound without relying on naive circuit-degree propagation through cancellation.

For exactness, let Q0=beta J and k0=eta+zeta in the weighted leading forms. The final top form, before substitution, is

    32 h gamma e² i⁸ k0¹⁹ w¹⁷ s³⁶ Q0¹³¹ (Q0-F)²
       * (w(Q0-F-alpha)-z Q0).

After i=2r+1, w=u² and the seven independent positivity substitutions, the coefficient of

    J_a²⁶⁸ h gamma e² r⁸ eta_a³⁸ u³⁴ s_a⁷² z_a²

is exactly -8192 beta¹³⁴, nonzero because beta>0. The exponent sum is 426. Distinct positivity triples and the displayed selection of the z term prevent ambiguity in this coefficient. Hence the degree is uniformly exactly 426 for the fixed coefficient recipe.

## 8. Reproducible finite checks

The fresh local emitter `build_integer28.py` reads the pinned circuit only as inert JSON and creates the new literal circuit. The independent verifier `verify_integer28.py` checks input/gate validity, all-port/all-gate liveness, dimensions, 150 signed integer evaluations against an independently written cancellation formula and the pinned parent circuit, 1000 direct evaluations of the remainder identity, positivity-surjection coverage through 1500, and two exact finite-field univariate leading-coefficient checks. The receipt is `INTEGER28_CHECKS.json`.

These finite checks supplement the proof; they neither prove the unbounded Pell/compiler dependencies nor exhibit an actual K215 accepting computation. No received source code, external checker, or installation is executed, and no remote repository state is changed.

## Sources

All paths below are under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/` at the pinned commit:

- `14-integer29/proofs/signed_domain_proof.md`: seven-positive-port signed theorem, odd multiplier, square-scale completeness, zero-square exclusion, signed-rank and main-root restoration.
- `12-gap-norm14/gap_root_elimination.tex`: gap norm, remainder identity and signed-denominator argument.
- `12-gap-norm14/arithmetic/blank14_gap_norm75.json`: literal 75-gate parent circuit, parsed as inert data.
- `14-integer29/vendor/blank67/k215_constants.json`: original coherent four-port coefficient recipe.

The saved upstream files are exact text evidence modulo a possible terminal newline added by the local text transport. `SOURCE_MANIFEST.json` records both Git blob identity and local SHA-256.
