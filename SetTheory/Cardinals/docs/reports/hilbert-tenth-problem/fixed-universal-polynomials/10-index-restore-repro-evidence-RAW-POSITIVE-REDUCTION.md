# Raw/positive restored-index reduction

## Result and scope

For the raw30 and positive22 parents and their index-eliminated children, the reviewed bootstrap plus the **actual fixed compiler** and retained outer/input equations prove

    R = p or R = -p,
    q is even,
    input index v = u or v = uA, where u=2dx+b.

They eliminate every other signed representative of the rank congruence. A negative zero, if one exists, must satisfy the explicit narrow parameter restrictions in Section 4. This note does **not** prove R>0, does **not** assert that such a negative zero exists, and does **not** establish exponent no-wrap. The precise remaining obstruction is the negative branch R=-p, with its first-index congruence still allowed to wrap.

All sources are pinned to ProveIt commit 2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff. No upstream code was executed, and no upstream repository file was edited. The accompanying sources are read-only research copies. Source URLs and Git blob identities are in source_manifest.json; cached files have been checked against those identities.

## 1. Exact retained equations used

Write K0=DC+B*DR and use the bootstrap's mathematical notation A=a+2, Delta=A^2-1 and H=4a+3. In particular the source register A denotes Delta, not mathematical A. The literal parent schedule in complete74_factored_first_norm.json, after the proven index restoration, supplies

    q=(B-1)J+1,
    C+alpha+2dx=q,
    (K0+X)C=F+z(q-1),
    C=Z+W,
    R=(q^2-Z-qF)(q^2-1)+(MC+q*MF_source)J,
    MF_source=MF_native+B-1,
    kappa=u+delta*Delta, u=2dx+b,
    c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H.

Every supplied coordinate here is positive. In positive22 the corresponding omitted triangular values are positive by their definitions, including mu. Thus

    q>=B>=16, 0<Z<C<q, 0<W<C<q,
    F<(K0+X)C, 0<2dx<q, 0<u<2q.

The fixed compiler has positive odd b<B, and d=bL is odd; hence u is odd. The bootstrap supplies

    X=wq^3, Y=sq^3, E=XY, a=Y(X+1),
    c=psi_A(p), p odd, p>=13,
    R=+/-p modulo c,
    k=2psi_P(n), P=2XY^2+1,
    (p+1)/2<=n<=p-1,
    2n=R+1 modulo E,
    c>2p and c>A^12.

The last growth bound follows directly from c>=(2A-1)^(p-1)>A^12. No sign of R is used in those conclusions.

## 2. The actual compiler really has K0<B^2

This is not an additional assumption on the numeral ports. It follows from the pinned compiler export:

1. complete75_half_binomial_compiler.py, compile_windows, calls the complete76 compiler, leaves its sparse DC polynomial and DR degree unchanged, and raises the inner radix Rrad=2^b. Its mass choice is

       mass=(K+2)(2 sum_e c_e+6), Rrad>=4 mass+8.

2. explore_fixed_raw_universal_76.py, compile_windows, builds DCpoly from four unit monomials, two copies of the positive center coefficients, and at most one additional unit monomial. Every coefficient is consequently at most 2 sum_e c_e+5, strictly below the final Rrad. Its support, including the optional correction, satisfies max(DCpoly)+Emax<L. The DR exponent Hcomp is also below L by the displayed choices Hcomp<T1<T2<g<L.

3. The inherited materializers in explore_fixed_raw_universal_78.py define DC as sum_e DCpoly[e]*Rrad^e, DR=Rrad^Hcomp, and B=Rrad^L. Complete77 overrides MC and constants(), not DC or DR; complete76's Compiled class is empty.

4. complete75_half_binomial_compiler.py, new_constants, copies constants() and changes only MC and MF. It does not replace DC or DR. Increasing b occurs before that export; no DC/DR/B cached property is materialized by the intervening sparse compiler construction.

Therefore 0<DC<B and 0<DR<B, including the optional high-monomial branch. Integrality gives

    K0=DC+B*DR <= (B-1)+B(B-1)=B^2-1 < B^2 <= q^2.

Relevant pinned links:

- [Half-binomial compiler export](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py#L21-L60)
- [Complete76 sparse choices](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_76.py#L90-L147)
- [Inherited materializers](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_78.py#L95-L105)
- [Complete77 export override](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/verification/explore_fixed_raw_universal_77.py#L75-L84)
- [Compiler proof, fixed layout and stronger radix](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md#L15-L68)

## 3. Exact representative reduction and parity

The paid shifted-mask identity is

    S'=Z+qF-1,
    T'=MC*J+1+q*(MF_native*J-1),
    R=(q^2-S')(q^2-1)+T', 0<T'<q^2-1.

Thus R is nonzero and R<q^4, as in the independent bootstrap review.

If R<0, its original packing expression, positive mask, positive F,Z and q>=16 imply

    -R < (Z+qF)q^2
       < Cq^3 (X+K0+1/q)
       < C X q^3 (1+1/q)
       <= (q-1)Xq^3(1+1/q)
       < Xq^4.

For the third strict inequality, K0<=q^2-1 gives K0+1/q<q^2, while X>=q^3 gives q^2<=X/q. This is stronger than the earlier rough 2Xq^4 bound. If R>0, R<q^4<Xq^4. Hence always |R|<Xq^4.

Since A>XY>=Xq^3, A^2>X^2q^6>2Xq^4; therefore c>A^12>2Xq^4. In particular |R|<c/2. The bootstrap independently gives p<c/2. Now R=+/-p modulo c implies that either R-p or R+p is an integer multiple of c with absolute value strictly below c. That multiple is zero, proving R=+p or R=-p.

In either case R is odd. If q were odd, the repunit equation with B even would make J even. Both (q^2-Z-qF)(q^2-1) and the mask term would then be even, forcing R even. Thus q is even. Consequently X,Y are even, A is even, and Delta is odd. This does not prove q is a power of two.

## 4. Necessary restrictions on a negative zero

Suppose R=-p. The first-index equation becomes

    2n+p-1=tE

for an integer t. The reviewed interval on n yields

    2p <= tE <= 3p-3.

The left side is positive, so t>=1; consequently

    E/3+1 <= p < Xq^4,
    Y<3q^4, equivalently s<3q,
    1<=t<3q/s.

The exact packing restrictions remain

    p=(Z+qF-1-q^2)(q^2-1)-T',
    F>=q,
    0<Z<C<q,
    (K0+X)C=F+z(q-1), z>0.

F>=q follows because negative R requires S'>q^2 and Z<q. In the possible boundary F=q it further requires Z>=2. Thus F<q is precisely a conclusion that cannot be imported from the old positive-index proof.

For fixed q,X,Y and fixed compiler, p and t are now finitely bounded. They are not uniformly bounded as q and X vary. The earlier infinite fixed-X,Y negative kernel family does not prove existence in this bounded window.

## 5. What the actual positive input block adds

Because kappa,mu>0 and their Pell norm holds, there is an integer v>=1 with

    kappa=psi_A(v), mu=chi_A(v).

The retained strict gap c>kappa gives v<p. On either sign branch, p=|R|<Xq^4<Delta, since Delta>(XY)^2>=X^2q^6>Xq^4. Also u<2q<A-1, so 0<u<Delta and 0<uA<Delta.

For every index v, the discriminant congruence gives

    psi_A(v)=v modulo Delta if v is odd,
    psi_A(v)=vA modulo Delta if v is even.

Combining with kappa=u+delta*Delta:

- If v is odd, v=u modulo Delta; since both lie in (0,Delta), v=u.
- If v is even, multiply vA=u modulo Delta by A and use A^2=1 modulo Delta. Then v=uA modulo Delta, and both representatives again lie in (0,Delta), so v=uA.

This proves the exact dichotomy v=u or v=uA. Since A is even and u odd, the second alternative really is even. On R=-p, it additionally implies

    uA<p<Xq^4, hence us<q.

The input projection supplies only

    W=2^v modulo H, 0<W<q,

while the main projection supplies only X=2^p modulo H. Neither p<Delta nor v<p implies 2^p<H or 2^v<H. The old proof's use of v<A-1 and its subsequent exponent no-wrap depend on the positive index bound p<q^4; that bound is unavailable on R=-p.

## 6. Precise unresolved point

To prove positivity in raw/positive it remains to exclude a tuple satisfying all the negative-branch restrictions above, the main projection congruence 2^p=X modulo H, the exact Pell ratio Y<psi_A(p)/(2psi_P(n))<Y+1, and the input dichotomy/projection. No contradiction follows merely by replacing congruences with equalities. Conversely, these necessary restrictions have not been realized as a complete negative zero.

The accompanying bounded checks corroborate the sharpened arithmetic estimate in 7,644 independent small parameter cases and the input-index dichotomy in 1,482 modular hits. These are supplementary checks, not unbounded proofs or full compiler/kernel zero searches.
