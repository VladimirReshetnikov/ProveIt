# A lower-degree 28-integer normalized root merger

## Result

The literal circuit `integer28_normalized_amalgam128_degree258.json` is one fixed polynomial in 28 unrestricted integers, of exact degree 258 and 128 binary operations (66 multiplications, 62 additions/subtractions). Its lack of integer zeros is equivalent to Con(ZFC), by an ordinary mathematical proof formalizable in ZFC, using the pinned original K215 compiler and calibration. This is a degree-versus-one-operation improvement over the accompanying degree-426, 127-operation gap norm, not a claim of global minimality or a new proof-assistant certificate.

The derivation below uses the original coherent package-06 coefficient tuple in `upstream/14-integer29/vendor/blank67/k215_constants.json`; here beta=Bm1 and K0=Kconstant. The primary instantiated equation instead uses the audited complete compact Wang943 tuple selected by `COEFFICIENT_BINDINGS.json`, with signed-domain transfer explained in `COEFFICIENT_TRANSFER.md`. MF is shifted. Fixed coefficients are not unknowns. The upstream source files are pinned to ProveIt commit f0ae4e0991ca44a7bb4e5671d42e33d775e48035.

## Construction

Use exactly the common abbreviations q,X,Y,E,k,c,a,H,Delta,R,N1,Nk,Nt,L from `INTEGER28_PROOF.md`. Retain f, delete tau and y, and introduce the integer t. Set

    A = 1+L(L+k),
    I = i c²,
    Ns = f²-Delta I²,
    K = Delta(f²-1),
    V = c(Tf-1)-Rf²,
    d = K-1,
    e = K V²-1,
    U = d(t²+A)-e,
    Res = U²-4d²t²A.

The equation is

    N1 Nk Nt Ns (1+Res)-1 = 0.                                 (1)

The difference from package09's fourteen-variable root merger is important: use the normalized strong factor Ns=f²-Delta I², not its ordinary-strong factor 1+I²-Delta(f²-1). The actual root-merger polynomial still computes K cheaply as Delta(f²-1); on the normalized strong locus, K=(Delta i c²)².

Require only J,F,alpha,z,s,eta,zeta positive, impose i=2r+1 and w=u², and allow f,h,T,t,gamma,r,u to be arbitrary integers. Seven positive surjections then give 28 unrestricted integer coordinates.

## Soundness and the missing zero-t branch

At a zero of (1), all five factors are integer units. The usual Delta=0 or3 modulo4 argument excludes N1=-1 and Ns=-1. Also Res is a square modulo4, so 1+Res cannot equal -1. Thus

    N1=Ns=1, Res=0, Nk=Nt in {-1,1}.

The zero-square argument from package14 uses only N1=1 and excludes u=0 before any first-root reconstruction. It gives X>=q. Weak transport and the signed-h argument then give the same bounds as in `INTEGER28_PROOF.md`, in particular X,Y>=1, k>=2, c>kY and L=XY²k>k.

Since Ns=1,

    f²=1+Delta i²c⁴,
    K=Delta² i²c⁴>0.

The nonzero odd integer i and a=(X+1)Y>XY imply

    K >= Delta² c⁴ > (X²Y²)²(kY)⁴ = L⁴.

Since L>=2 and k<L,

    A=1+L²+Lk < 1+2L² < L⁴ < K.

Thus 1<A<K and d=K-1>0.

If t=0, Res=0 forces U=0, or dA=e. That says

    (K-1)A=K V²-1,
    K(A-V²)=A-1.

But 0<A-1<K, a contradiction. Therefore t!=0. This is the zero-denominator case not covered by a naive signed use of the original positive-t merger.

Define, as proof abbreviations,

    tau=U/(2dt),
    y=t-tau.

Since Res=0, tau²=A is integral, hence tau is an integer. Therefore y is an integer. Expanding U=2dt tau gives dy²=e. Consequently

    tau²-L(L+k)=1,
    K V²-(K-1)y²=1,
    f²-Delta i²c⁴=1.

These restore precisely the normalized first, auxiliary, and strong equations. No sign of f,T,tau,y,gamma is used. Together with the outer factors they satisfy package14's seven-positive-port, odd-i, square-w signed theorem, which yields a valid blank K215 tableau.

## Completeness

From a canonical accepting tableau take package14's normalized witnesses with odd i and square w. Put t=tau+y. The ordinary positive canonical tau,y make t positive, though the equation does not require that sign. Expanding gives U=2dt tau and Res=0; all other factors are one. Deleting tau,y yields (1). No extra canonical congruence or new tuning is necessary.

The odd multiplier and square scale are the exact existence-preserving choices in package14, not properties asserted of every earlier solution. The inherited exact-machine calibration and ordinary formalizability argument then give the ZFC consistency equivalence.

## Variable and operation count

Seven disjoint positivity triples represent J,F,alpha,z,s,eta,zeta using Pos(a,b,c)=1+a²+b²+c(c+1). The other seven coordinates are f,h,T,t,gamma,r,u. This gives 28 integers.

In the pinned 76-gate `09-combined13/arithmetic/amalgam14_product76.json`, replace the final two strong-factor gates by

    normalized_strong_term = Delta*I2,
    Ns = f2-normalized_strong_term.

All other gates remain unchanged. This changes one addition into one multiplication but does not change gate count. The normalized 14-coordinate circuit has 43M+33A=76 operations. Seven positivity substitutions add21M+28A, and i=2r+1,w=u² add2M+1A. Total:66M+62A=128. Every gate and input is live.

## Exact degree 258

Use weights two on J,F,alpha,z,s,eta,zeta,w and one on f,h,i,T,gamma,t. As in the companion proof,

    deg(N1,Nk,Nt)=(35,13,4), deg(Delta)=24, deg(c)=10,
    deg(L)=22, deg(A)=44, deg(Ns)=66.

Here K=Delta(f²-1) has degree26, V has degree12, d has degree26, and e has degree50. Hence U has degree70, uniquely from dA, and Res has degree140, uniquely from U², since 4d²t²A has degree98. Summing the five factor degrees gives258.

For a nonzero top-form certificate, write Q0=beta J and k0=eta+zeta. Before the explicit substitutions the weighted leading form is

    8 h gamma f⁴ i² k0⁹ w¹³ s²² Q0⁷⁹
      * [w(Q0-F-alpha)-z Q0].

After i=2r+1, w=u² and the seven positivity substitutions, the coefficient of

    J_a¹⁶⁰ h gamma f⁴ r² eta_a¹⁸ u²⁶ s_a⁴⁴ z_a²

is -32 beta⁸⁰. It is nonzero for the actual beta>0, and its exponent sum is258. This proves exact degree uniformly; modular checks are supplementary.

## Verification and source boundary

`build_integer28_amalgam.py` is a fresh local emitter, and `verify_integer28_amalgam.py` is a fresh independent checker. The latter validates live gates and ports,150 signed integer comparisons against a separately written formula,300 root-restoration identities, and two exact modular leading-coefficient tests. `INTEGER28_AMALGAM_CHECKS.json` records PASS.

Source code received from the repository is not executed. Upstream circuits are read only as inert JSON. The unbounded Pell/compiler and machine-calibration dependencies are inherited mathematics, not proved by finite tests, and no actual blank accepting run or ZFC consistency proof is asserted.
