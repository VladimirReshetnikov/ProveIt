# Exact full-zero obstruction for raw29 and positive21

## Status, source boundary, and novelty

This note does **not** prove that the restored index is positive, and it does **not** construct a negative zero. It replaces the previous necessary-condition reduction by a necessary-and-sufficient, effective obstruction for full negative zeros of both actual positive interfaces. It closes all outer/input/auxiliary sufficiency obligations in the inherited two-unbounded-parameter reduction. The bounded ranges and at-most-one candidate main index are prior results; deterministic recovery and the full-zero equivalence are new here.

Additional consequences are a finite wrapped-odd-input sector, an explicit forbidden scale interval for the odd input branch, and the strengthened even-input bound `us <= C <= q-u+b-1`.

The audited upstream snapshot is commit `d5bd4a67b41b89688a079997574a94bcd855bb83` (current main when read, 2026-10-03 19:05 UTC). The projected source receipt is byte-identical to the earlier reviewed receipt (SHA256 `ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92`). The targeted refinement file's latest change is still commit `813c1cff42f9238a0158228f5e003a6a5405444a`. Its defect exclusion and one-index uniqueness proof have been read and verified, and are prior results here, not claimed as new. Its weaker `p<(q+1)E` bound is replaced below by the previously independently reviewed `p<Xq^4` bound.

The current upstream universal-polynomial headline has separately moved to a source-claimed 85 operations. This investigation concerns the unchanged nonlinear-index scout and makes no universal bound claim. Receipt mode labels are inherited `raw30`/`positive22`; the children have 29/21 supplied positive witnesses. The signed19 child is outside this theorem.

No upstream program or schedule was executed. Upstream files were read as text/data only. Any finite checks below execute newly written independent mathematical code and are not a search certificate for all full zeros.

## 1. Fixed hypotheses and notation

Fix one valid exported complete75 compiler slice and an ordinary positive input `x`. Its fixed integers are `B=2^d_cell`, positive odd `b`, `K0=DC+B*DR`, and the native masks `MC, MF0`; the actual source mask port is `MFsrc=MF0+B-1`. Retain the exact original compiler recipe, including its powers-of-five conditions. The already independently audited consequences used here are

    B>=16, 1<=b<B, d_cell>0,
    0<DC,DR<B, K0<=B^2-1,
    0<MC,MF0<B-1.

Put `u=2*d_cell*x+b`, an odd integer at least 3. For a source zero write

    q=(B-1)J+1, X=wq^3, Y=sq^3, E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1, Q=q^2-1,
    M=(MC+q*MFsrc)J.

For integer `A>=2`, define `chi_A(r)+psi_A(r)*sqrt(A^2-1)` to be the r-th power of `A+sqrt(A^2-1)`.

The previous raw-positive reduction and independent audit establish, on every positive child zero,

    q even, q>=B,
    c=psi_A(p), D=chi_A(p), p odd and p>=13,
    R=+p or -p, |R|<Xq^4,
    k=2psi_P(n), (p+1)/2<=n<=p-1,
    input index e=u or e=uA, 0<e<p.

For `R=-p`, they further establish an integer `t>=1` with

    2n+p-1=tE, 2p<=tE<=3p-3,
    s<3q, ts<3q.

The verified upstream refinement proves, writing `d_def=2n-p`,

    4^d_def>X>=q^3, d_def>=7,
    2p+6<=tE<=3p-3,

and at most one ratio-admissible p per fixed q,X,Y,t. The letter t here is the source refinement's representative v; e is the input Pell index, and neither is a supplied register.

## 2. Finite candidate extraction at fixed q,w

Enumerate just two unbounded positive integers q,w, subject to

    q>=B, q even, q=1 (mod B-1), q>u-b+2.

Set `J=(q-1)/(B-1)` and `X=wq^3`. For each such pair the remaining choices are finite:

    1<=s<=3q-1,
    1<=t<=floor((3q-1)/s).

Set Y,E,A,P as above. Search only odd p in the finite interval

    max(13, ceil(tE/3)+1) <= p
        <= min(Xq^4-1, floor((tE-6)/2)).                 (1)

For each p define the positive integer

    n=(tE+1-p)/2.

The interval implies `n<p<2n`. Select p only if

    2Y*psi_P(n) < psi_A(p) < 2(Y+1)*psi_P(n).           (2)

There is at most one such p. It can be found effectively by integer binary search: on the ordered odd p's, the function `psi_A(p)/(2psi_P(n))` strictly increases, since p increases and n decreases. Find the least odd p for which its value exceeds Y, then test its upper bound. All comparisons can be done by exact integer Pell recurrence/powering; no transcendental oracle or asymptotic equality is required. This is a terminating procedure for each fixed q,w,s,t, not a practicality claim for astronomical inputs.

Reject unless `4^(2n-p)>X` and

    2^p = X (mod H).                                   (3)

The defect test is retained as an inexpensive necessary filter, not an independent sufficiency ingredient.

## 3. Packing is a deterministic recovery, not another search

Given this p, require

    p+M = 0 (mod Q).

Put

    N=(p+M)/Q,
    Z=N mod q, with 0<=Z<q,
    F=q+(N-Z)/q.                                       (4)

Then require `Z>0`. These are the **only** possible Z and F compatible with the full negative packing equation and `0<Z<q`.

Indeed the literal source equation is

    -p=(q^2-Z-qF)Q+M,

equivalently `N=Z+qF-q^2`. Its residue modulo q gives Z uniquely, and then F is forced. Conversely (4) gives exactly that equation. Since p,M>0, N>0; hence F>=q automatically. If F=q, N=Z>0, but the retained shifted-mask remainder bound sharpens this to Z>=2, agreeing with the previous reduction.

This is stronger than bounding or enumerating F,Z: their values are fully determined before the input branch is chosen.

## 4. Exact full obstruction

For one of the two values `e in {u,uA}`, form

    W = the least nonnegative residue of 2^e modulo H.

As H is odd, W is nonzero. Accept this branch precisely when all of the following hold:

    e<p,
    0<W<q,
    C=Z+W,
    C+u-b<q,                                          (5)
    L=(K0+X)C-F is a strictly positive multiple of q-1. (6)

Together, (1)--(6), the finite parameter ranges, and the two projection congruences are a necessary-and-sufficient obstruction:

**Theorem.** For a fixed valid compiler slice and x>0, the raw29 child has a full strictly positive supplied tuple with R<0 if and only if some q,w and finite choices s,t,p,e pass the foregoing predicate. The same equivalence holds for positive21. Any passing predicate reconstructs a full tuple in both modes. Every negative zero projects to a passing predicate, though auxiliary witnesses need not be unique.

Only q,w are unbounded search parameters; s,t lie in explicit finite sets, p is absent or uniquely determined by exact comparisons, and e has at most two choices. This is not global finiteness, a positivity theorem, or a counterexample family. It is a genuine full-zero equivalence: none of the first Pell, input Pell, positivity, outer packing, transport, strong norm, or auxiliary sign obligations are left outside the predicate.

### Necessity

The prior audited reductions supply the parameter ranges, (1)--(3), and e's two possibilities. Literal packing and `0<Z<C<q` give (4). The input norm and exponent equation give `W=2^e mod H`; because `0<W<q<H`, it is the unique least residue. The retained raw bound is exactly `C+alpha+u-b=q` with alpha>0, giving (5). The transport equation is exactly `L=zquot*(q-1)` with zquot>0, giving (6).

### Sufficiency: first/main and outer witnesses

For a passing predicate set

    alpha=q-C-u+b,
    zquot=((K0+X)C-F)/(q-1),
    c=psi_A(p), D=chi_A(p),
    k=2psi_P(n), tau=chi_P(n),
    eta=c-kY, zeta=k-eta,
    h=(k+p-1)/E,
    ga=(D-a*c-X)/H.                                   (7)

All divisions are exact. In particular P=1 modulo E implies `psi_P(n)=n mod E`, and `2n+p-1=tE`; hence h is integral and positive. The strict ratio gives eta,zeta>0. The two Pell identities give

    D^2-Delta*c^2=1,
    tau^2-XY^2(XY^2+1)k^2=1.

The latter is exactly the factored first norm in the complete74 schedule. The restoration identity is `k-hE-1=-p`; (4) proves its packing comparison. Definitions (5)--(7) prove every outer transport, raw-bound, ratio and scale equation.

Let `E_r=chi_A(r)-a*psi_A(r)`. The exact recurrence gives `E_0=1,E_1=2` and `E_r=2^r mod H`. Also

    E_r=2psi_A(r)-psi_A(r-1)>psi_A(r)  (r>=1).

At r>=3, `psi_A(r)>=4A^2-1>H+X`. Thus (3) makes ga a strictly positive integer. No gamma splitting with the input rho is required: raw29/positive21 supply ga independently. The split ga=rho+sigma belongs to the different signed19 source and is not imported here.

### Sufficiency: the entire input block

Set

    kappa=psi_A(e), mu=chi_A(e),
    delta=(kappa-u)/Delta,
    phi=c-kappa,
    rho=(mu-a*kappa-W)/H.                              (8)

For e=u odd, the discriminant recurrence gives `kappa=u mod Delta`. For e=uA even, it gives `kappa=eA=uA^2=u mod Delta`. Thus delta is integral. Since u>=3 and e>=u, strict Pell growth gives kappa>u, so delta>0. Since e<p, phi>0. Since e>=3, the preceding bound gives `mu-a*kappa>H+q`; (5) and the definition of W therefore make rho a strictly positive integer. The norm and both input equations are exact. This checks the supplied root's sign rather than merely satisfying the squared norm.

### Sufficiency: complete the ordinary strong/auxiliary block

This step uses, rather than reclaims as new, the verified upstream mixed-sign auxiliary construction. It works for every odd p, not just p=3 mod4. Set

    m=c*p       if p=3 mod4,
    m=2*c*p     if p=1 mod4,
    f=chi_A(m), Taux=Delta*psi_A(m), i=Taux/c^2,
    ell=p+2m,
    U=chi_Taux(ell)/Taux, y_aux=psi_Taux(ell),
    j=(U-p)/c, o=(U+c)/f.                              (9)

The binomial expansion of `(D+c*sqrt(Delta))^(m/p)` shows `c^2 | psi_A(m)` because m/p is c or 2c. Hence i is a positive integer and `Taux^2=Delta*(f^2-1)`.

Because A is even and p odd, c is odd. The chosen m makes `(ell-1)/2` even. The odd quotient polynomial identities therefore give

    U=p (mod c),
    U=psi_A(ell)=-c (mod f).

For the second congruence, `Taux^2=-Delta=1-A^2 mod f` and the Pell addition formula gives `psi_A(p+2m)=-psi_A(p) mod chi_A(m)`. Thus j,o are integral. They are positive: Taux>=c^2, ell>=3, and `U>=4Taux^2-3>p`. Finally the Pell norm at Taux gives

    Taux^2*(U^2-y_aux^2)=1-y_aux^2,
    U=jc+p=jc-R=of-c.

These are every remaining strong/auxiliary comparison. The choices m can also be enlarged with the same requisite parity, but no auxiliary uniqueness is asserted.

### Both literal witness lists

For raw29 supply exactly

    C,F,J,W,Z,a,alpha,c,D,delta,eta,f,ga,h,i,j,k,kappa,
    mu,o,phi,q,rho,s,tau,w,y_aux,zeta,zquot,

with source aliases Jrep=J and d=D. For positive21 supply exactly

    J,F,alpha,zquot,f,h,i,j,o,s,w,tau,eta,zeta,ga,y_aux,
    Z,W,delta,phi,rho.

The omitted positive21 coordinates are the same positive values by their triangular source definitions. There is no missing residual between these reconstructions and the literal saved source. All retained residuals vanish; therefore either saved SOS finalizer vanishes over the integers.

## 5. New input/packing consequences

### 5.1 A finite wrapped-odd sector at each fixed input

In the odd input case e=u, W is the least residue of the *fixed* integer 2^u. Exactly one of the following holds.

**Unwrapped sector:** H>2^u. Then W=2^u. Since Z,alpha>=1, the raw bound gives

    q >= 2^u+u-b+2.                                   (10)

(The two units are precisely Z>=1 and alpha>=1.) Thus the unbounded sector has a fixed exact input marker W, not merely a modular marker.

**Wrapped sector:** H<=2^u. Since H is odd and 2^u even, in fact H<=2^u-1. Substituting the exact modulus gives

    4s*w*q^6+4s*q^3+4 <= 2^u,
    w <= floor((2^u-4s*q^3-4)/(4s*q^6)),               (11)
    4q^6<2^u.

Thus for each fixed input and fixed compiler there are finitely many possible q,w,s,t,p in the wrapped odd-input sector. Formula (11), together with the exact candidate extractor, is a complete finite decision procedure for that sector. No effectiveness claim relies on computing a multiplicative order or on factoring H.

In particular, no odd-input negative zero can have

    4q^6>=2^u  and  q<2^u+u-b+2.                     (12)

This is an explicit forbidden range, not a claim that the even-input branch is eliminated there. No finite enumeration of the wrapped sector for the actual huge compiler constants has been performed. There is one immediate uniform exclusion: because q>=B=2^d_cell, wrapping requires u>6*d_cell+2. Thus u<=6*d_cell+2 eliminates this sector without enumeration. In the actual compiler d_cell=bL with L>=1, so b<=d_cell; consequently inputs x=1 and x=2 have no wrapped odd-input branch. The even-input alternative is unaffected.

### 5.2 An even-input bound using the real outer C

On either negative input branch the reviewed packing estimate is

    p < C X q^3(1+1/q).

If e=uA, then `uA<p`, while A>XY=sXq^3. Consequently

    us < C(1+1/q) < C+1,

where C<q. Since us is integral,

    us <= C <= q-u+b-1,
    u(s+1) <= q+b-1.                                 (13)

This strengthens the earlier `us<q`: it couples the even-input alternative to the *same* C constrained by both outer positivity and the ordinary input. Equivalently, s is bounded by `floor((q-u+b-1)/u)` on this branch. Also `uA<p< tE/2` gives t>2u, hence t>=2u+1.

### 5.3 A small universal local exclusion

No full child zero on either sign can have 3|q. If 3|q, then 3 divides X and Y, hence H=4Y(X+1)+3 is divisible by 3; the main projection `2^p=X mod H` would imply `2^p=0 mod3`, impossible. This can be used as an initial q filter. It is an elementary new filter, not the central theorem.

## 6. Unresolved scope and failed lines

The remaining unbounded possibilities are (a) the odd branch with exact W=2^u and q satisfying (10), and (b) the even branch with (13). The first/main ratio and the two modular exponent tests still need simultaneous realization or exclusion. The new criterion does not imply that their intersection is empty or nonempty.

The signed19 density construction cannot be transplanted: its free progression eventually makes Z unbounded, whereas (4)--(5) restrict the same recovered Z and W to C<q. Likewise density at fixed q,X,Y cannot prove a hit in the bounded interval (1). No such argument is used.

A possible strategy of replacing W's congruence by W=2^u everywhere fails exactly in the finite sector (11), and is never valid for e=uA merely from the present size bounds. A possible strategy of using only the auxiliary norm to force a positive sign fails by the explicit completion (9). No finite fixture is represented as a complete negative compiler zero.

## 7. A certified sub-unit real window, without materializing the Pell values

This section is a further improvement over the earlier monotonicity-only uniqueness result. It extracts a necessary real interval of length less than `q^(-3)+q^(-5)`, and excludes a parameter choice whenever that interval contains no odd integer. Computing the interval needs only rational logarithm enclosures, not the exponentially large Pell witnesses.

For Q0>=2 put

    a_-(Q0)=2Q0-1/Q0,
    a_+(Q0)=2Q0-1/(2Q0).

Squaring gives the strict elementary bounds

    Q0-1/Q0 < sqrt(Q0^2-1) < Q0-1/(2Q0),
    a_-(Q0) < Q0+sqrt(Q0^2-1) < a_+(Q0).

Write a_-=a_-(A), a_+=a_+(A), b_-=a_-(P), b_+=a_+(P), and define positive rational numbers

    r_- = (P-1/P)/(2A) * (1-(2A-1)^(-26)),
    r_+ = P/(2(A-1/A)) / (1-(2P-1)^(-14)).

For p>=13 and n>=7 the exact Binet formula proves

    L(p)=log(r_-)+p log(a_-)-n log(b_+)
      < log(psi_A(p)/(2psi_P(n)))
      < U(p)=log(r_+)+p log(a_+)-n log(b_-).             (14)

The exponents 26 and 14 bound the two tail corrections uniformly. They do not assume p/a small. Replace `n=(tE+1-p)/2` to get affine functions of the real variable p. The ratio interval therefore requires the explicit strict interval

    [log Y-log r_+ +(tE+1)log b_-/2]
       /[log a_+ +log b_-/2] < p

    p < [log(Y+1)-log r_- +(tE+1)log b_+/2]
       /[log a_- +log b_+/2].                          (15)

Intersect (15) with (1). On this intersection, the denominators are positive, p>=13, and 7<=n<p. We claim its length is less than `q^(-3)+q^(-5)<1`.

Indeed

    log(a_+/a_-) = log(1+1/(4A^2-2)) < 1/(3A^2),
    log(b_+/b_-) < 1/(3P^2).

The prefactor square-root error is less than

    1/(A^2-1)+1/(P^2-1) < 3/A^2,

and the sum of the two logarithmic tail errors is less than `1/A^2`. For example `-log(1-z)<2z` at the present z<1/2, and each resulting term is less than `1/(2A^2)`. Consequently throughout (1),

    U(p)-L(p) < (p+n)/(3A^2)+4/A^2 < p/A^2
             < 1/(Xq^2) <= 1/q^5.                   (16)

The last step uses the actual outer bound p<Xq^4 and A>XY>=Xq^3. If p1<p2 are two real points in the intersection of (15) with (1), then

    L(p2)-L(p1) < log(1+1/Y)+1/q^5
                < 1/q^3+1/q^5.

The slope `log a_-+log b_+/2` is greater than 1, proving the claim. Thus this interval has at most one integer, even before odd parity is imposed.

For full effectiveness, logarithms of positive rationals admit standard elementary rational enclosures. Range-reduce r as `r=2^k*t`, 1<=t<2, put `z=(t-1)/(t+1)`, and use

    log t = 2 sum_(j=0)^(N-1) z^(2j+1)/(2j+1) + error,
    0<=error<=2*z^(2N+1)/((2N+1)*(1-z^2)).

Use the same formula at t=2 to enclose log2. All endpoints and errors are rational. Enclose (15) outward, refining as needed; exact Pell comparison remains the definitive fallback for an endpoint coincidence or surviving integer. This interval filter cannot falsely reject a valid ratio when implemented with outward bounds. Its width isolates at most one possible integer; it does not certify strict endpoint membership or ratio acceptance. The logarithmic precision depends on the parameters, and exact final acceptance can still require very large Pell integers. No uniform polynomial-time complexity bound or nonzero separation estimate is claimed. The theorem still does not guarantee a surviving candidate.

## 8. Exact checked cases and reproducibility

The new checker `check_exact_obstruction.py` authenticates all five cached upstream files against their Git blob SHA1 and SHA256 and reads the projected JSON as static data. It confirms the exact raw29/positive21 witness lists, comparison counts, and the relevant source ports; it never interprets or executes a saved source schedule.

Its own mathematical checks pass:

- 18,360 negative outer-packing arithmetic fixtures reconstruct precisely the original Z,F and transport quotient. These are not actual compiler slices or full zeros.
- 288 input discriminant/residue fixtures verify integral positive delta,rho and the positive Pell root.
- Four small complete auxiliary-only tuples cover both p modulo 4 classes; the p=1 fixtures are outside the full main-index range and are labeled as such. Sixteen p>=13 modular fixtures cover c^2 divisibility and the chosen auxiliary-index parity without materializing giant auxiliary witnesses.
- 450 direct rational Binet bounds compare the proposed bounds with actual independently computed Pell values.
- All 3,536 choices with q in {16,20,32}, w in {1,2,3,4}, every s=1,...,3q-1 and every t=1,...,floor((3q-1)/s) have no odd integer in the outward-rational necessary interval. Their maximum outward width is less than 1/100000. This is an exact finite exclusion for a relaxed arithmetic scale grid, **not** a validation of a full compiler slice and **not** an unbounded proof.

The interval calculations use 36 terms of the rational atanh series with the displayed exact tail bound. Every necessary endpoint is rounded outward with Fraction arithmetic. The floating maximum-width display in the receipt is descriptive only; all mathematical checks use exact rationals. No surviving integer was found in this grid, so no full Pell-ratio candidate acceptance or full negative-zero construction was attempted there.

Run the new mathematical checker from any directory with `python3 check_exact_obstruction.py`, using the appropriate relative path to the script. Its default is deterministic JSON on stdout only. `--output` accepts an external destination outside the packet, and `--expect expected_check_results.json` checks the frozen canonical receipt byte-for-byte. Every former Python assertion is an unconditional exception check, so optimization does not disable verification. Both normal Python and `python3 -O` have been replayed against the same frozen receipts. The three checkers share this read-only-by-default contract; the README lists their individual commands. The source manifest gives immutable URLs, exact source byte counts, Git blob SHA1 and SHA256. The two prior reduction/audit snapshots are under `context/`; their logical status remains prior work. A separate independent review is under `independent/`.
