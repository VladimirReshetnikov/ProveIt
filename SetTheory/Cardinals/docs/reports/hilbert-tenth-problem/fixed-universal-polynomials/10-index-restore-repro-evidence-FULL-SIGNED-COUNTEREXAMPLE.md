# Full negative-restoration family for the signed19 child

Status: proof proposal submitted for independent audit, 2026-10-03. This is a proof packet, not a full article. The claim concerns the complete eliminated **signed20 -> signed19** source, with all nineteen supplied child witnesses strictly positive. It does not concern the raw29 or positive21 child domains. No upstream program was executed, no repository file was modified, and no universal bound is claimed.

## Theorem

Fix any actual half-binomial compiler export used by complete74, with its fixed numerals `B=2^d`, `b`, `K0=DC+B*DR`, `MC`, and native `MF`. In particular, `d` is a power of five, `b` is odd, and `K0>=0`. For **every strictly positive ordinary input x**, the complete signed19 child polynomial has infinitely many strictly positive supplied-witness zeros whose restored index

    R = k - h*X*Y - 1

is strictly negative. The constructed input root is positive. The negative restored W is an allowed intermediate register, not a supplied witness.

Thus the omitted-positive-index restoration fails on this full child. In fact its positive existential projection contains every positive ordinary input. This is a statement about the proposed eliminated child, not a counterexample to the established parent theorem or a claim about any identified machine input's acceptance status.

## 1. Exact source and compiler scope

All repository sources are pinned to `VladimirReshetnikov/ProveIt` at commit `2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`. The complete74 graph review establishes that deleting r replaces it everywhere by `R=k-hXY-1`; no other residual is removed except the now-identical index comparison. The signed parent equations and definitions are given verbatim in `complete75_signed_projection_elimination101.md` Section 1. The factored complete74 descendant has the same polynomial equations, with only an arithmetic factoring of the first norm.

The retained supplied witnesses are

    J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma.

The mathematical abbreviations are

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=X*Y,
    k=eta+zeta, a=Y*(X+1), A=a+2,
    H=4a+3, Delta=A^2-1=a^2+H,
    c=kY+eta, gamma=rho+sigma, D=X+a*c+gamma*H,
    u=2d*x+b, kappa=u+delta*Delta,
    C=q-alpha-2d*x, W=C-Z, mu=W+a*kappa+rho*H.

Put `MFsrc=MF+B-1`. The eight retained comparisons, in mathematical form, are

    (K0+X)C = F+z(q-1),
    R = (q^2-Z-qF)(q^2-1)+(MC+q*MFsrc)J,
    tau^2-XY^2(XY^2+1)k^2 = 1,
    D^2-Delta*c^2 = 1,
    (i*c^2)^2 = Delta*(f^2-1),
    (i*c^2)^2*((j*c-R)^2-y^2) = 1-y^2,
    j*c-R = o*f-c,
    mu^2-Delta*kappa^2 = 1.

The restored index identity `k=R+1+hE` must also hold by its definition. All computed definitions will be verified, including `gamma=rho+sigma` with both summands positive.

The new source receipt in `sources/complete75_half_binomial_compiler.md`, Section 1, says to keep b,L,d powers of five. Nonnegative K0 is part of the authenticated fixed source contract; the original nonnegative-coefficient definitions of DC and DR are also retained in `sources/explore_fixed_raw_universal_76.py` and `sources/explore_fixed_raw_universal_78.py`. The construction does **not** replace these actual compiler numerals by toy masks. It works for their arbitrary fixed exported values. The original bootstrap and negative-kernel reviews contain the remaining authenticated source pins; all referenced source texts are included in this packet's `sources/`, and `source_manifest.json` records their origins and byte hashes.

## 2. Fix the input, repunit, and transport witnesses

Fix x>=1. Choose N to be a power of five, large enough that

    q=B^N>2d*x+1.

Then `t=d*N` is a power of five and `q=2^t`. Set

    J=(q-1)/(B-1), C=1, alpha=q-1-2d*x,
    p0=12t+7, X=2^p0, w=2^(p0-3t),
    z=1, F=K0+X-q+1, Q=q^2-1,
    M=(MC+q*MFsrc)*J.

These are integers with J,alpha,w,z,F strictly positive. Indeed p0>3t and X>=q^3>q. The repunit, X-scale, C-definition, and transport equality are exact. Keep the positive odd input index

    u=2d*x+b>=3

fixed throughout the construction.

## 3. Choose the Y-scale to remove every CRT obstruction

Set

    D0=4q^3*(X+1)/3.

This is an integer, since p0 is odd. We prove `gcd(D0,Q)=1`.

Since t is a power of five,

    gcd(p0,2t)=gcd(12t+7,2t)=1.

The elementary binary-power gcd identity gives

    gcd(2^p0+1,2^(2t)-1)=3.

Also p0=1 mod6, so X=2 mod9 and X+1=3 mod9. Dividing X+1 by3 therefore removes its only factor of3. Since Q is odd and coprime to q, `gcd(D0,Q)=1` follows.

For each prime r dividing the odd number Q, choose a residue s0 that is neither0 nor `-D0^(-1)` modulo r. There is such a residue because r>=3. Combine these choices by the Chinese remainder theorem, obtaining s0 with

    gcd(s0,Q)=gcd(1+D0*s0,Q)=1.

The progression

    ell = 1+D0*s0 (mod D0*Q)

is primitive: its residue is1 modulo D0 and is a unit modulo Q. Dirichlet's theorem therefore supplies a prime ell in this progression, as large as desired. Fix one with ell>3 and put

    s=(ell-1)/D0>0, Y=s*q^3,
    E=X*Y, a=Y*(X+1), A=a+2,
    H=4a+3=3ell, Delta=A^2-1,
    P=2X*Y^2+1.

We have s=s0 modQ, hence `gcd(s,Q)=1`. Since 3 divides Q, neither s nor D0 is divisible by3. Also ell is a unit modulo3. Thus ell-1=D0*s is nonzero modulo3 and ell is neither0 nor1 modulo3; so ell=2 mod3.

Let `O=ord_H(2)`. This order exists because H is odd. Because H=3ell with ell prime>3,

    O | lcm(2,ell-1) | 2(ell-1)=2D0*s.

Consequently

    gcd(QH,O)=1.

Here the Q-part follows from `gcd(Q,D0*s)=1`; the H-part follows because neither3 nor ell divides `2(ell-1)`. Separately

    gcd(QH,2E)=1:

Q is coprime to Xq and to s; H=3ell is coprime to Xq (powers of two), to s (since ell=D0*s+1), and to3's contribution in s (which is absent). Set

    T=lcm(4,2E,O), L=E/2.

Then the decisive coprimality is

    gcd(QH,T)=1.                                             (A)

Only this scale-selection step uses Dirichlet's theorem. A primary historical proof, in English translation, is P. G. L. Dirichlet, [There are infinitely many prime numbers in all arithmetic progressions with first term and difference coprime](https://arxiv.org/abs/0808.1408v2). Its application here is solely to one explicitly primitive progression.

## 4. Incorporate the complete input and packing equations in a free progression

For integer A>=2, define Pell polynomials by

    chi_A(r)+psi_A(r)*sqrt(A^2-1)
      = (A+sqrt(A^2-1))^r.

Set the now-fixed input quantities

    kappa=psi_A(u), mu0=chi_A(u), e_u=mu0-a*kappa,
    delta=(kappa-u)/Delta.

Because u is odd, the binomial expansion modulo Delta gives `psi_A(u)=u (mod Delta)`: in general `psi_A(u)=u*A^(u-1) (mod Delta)`, and A^2=1 modulo Delta. Also psi_A(u)>u for u>=3. Hence delta is a strictly positive integer.

Choose the main index p in the simultaneous progression

    p=p0 (mod T),
    p=-M-Q*(q^2-qF+e_u-1) (mod QH).                        (B)

By (A), these conditions define an ordinary nonempty arithmetic progression with step `V=T*QH`. In particular, p remains freely variable along that progression; it is **not** confined to a Pell-value subsequence. Every p in it satisfies

    p=3 (mod4), 2^p=X (modH), p=p0 (mod2E).

Choose an integer n0 representing `(1-p0)/2 (mod L)` and consider

    n=n0+L*v.

Then `2n=1-p (modE)` for every p in (B) and every such n.

For any sufficiently large p in (B), define

    Z=q^2-qF+(p+M)/Q,
    rho=(Z+e_u-1)/H.

Both are integers by (B), and both are strictly positive for sufficiently large p. Their dependence on p is affine, with positive slopes 1/Q and 1/(QH). Define `W=1-Z`. Then

    W+a*kappa+rho*H = e_u+a*kappa = mu0>0.

Thus the entire input equation, its index congruence, the definition of W, and its root sign are already exact. Also

    (q^2-Z-qF)Q+M=-p.                                    (C)

The packing equation is satisfied with R=-p. No assumption about typed words, accepting computations, or no-wrap exponents has entered.

## 5. Preserve the first/main Pell ratio by irrational rotation

A is even, so Delta is odd. In contrast,

    P^2-1=4X*Y^2*(XY^2+1)

has 2-adic valuation `2+p0+2*v2(Y)`, which is odd because p0 is odd. Hence the squarefree parts of Delta and P^2-1 have different parity, and their real quadratic fields are distinct.

Put

    alpha0=log(A+sqrt(Delta)),
    beta0=log(P+sqrt(P^2-1)).

Their ratio is irrational. Otherwise equal positive powers of the two units would belong to the intersection of the distinct quadratic fields, namely Q. A positive rational element having norm one in a quadratic field is1, contradicting those units' growth.

Write the progression (B) as `p=p_star+V*r`. The quantity `V*alpha0/(L*beta0)` is irrational. Therefore irrational rotation supplies infinitely many arbitrarily large positive r, with corresponding positive integers v, such that

    Y < psi_A(p)/(2*psi_P(n)) < Y+1,                     (D)
    n=n0+L*v.

For precision, choose a closed interval of positive length strictly inside `(log Y,log(Y+1))`. The affine logarithmic approximation

    p*alpha0-n*beta0+log(sqrt(P^2-1)/(2*sqrt(Delta)))

is dense modulo L*beta0 as r varies. Integer translates give infinitely many values in that interval. The corresponding v grows linearly and positively with r. The exact logarithmic quotient differs from this approximation by

    log(1-exp(-2p*alpha0))-log(1-exp(-2n*beta0)),

which tends to zero. Shrinking to an interior interval makes (D) valid for all sufficiently large selected hits. This is the same legitimate free-progression density mechanism as the audited kernel result, now after all outer constraints have been incorporated into (B).

## 6. All first/main definitions and positive gamma splitting

For the unbounded selected pairs (p,n), set

    c=psi_A(p), D=chi_A(p),
    k=2*psi_P(n), tau=chi_P(n),
    eta=c-kY, zeta=k-eta,
    gamma=(D-a*c-X)/H,
    R=-p, h=(k+p-1)/E,
    sigma=gamma-rho.

The strict ratio (D) makes eta,zeta positive integers, and establishes k=eta+zeta and c=kY+eta. The two Pell norms give

    D^2-Delta*c^2=1,
    tau^2-XY^2(XY^2+1)k^2=1.

The projection sequence `e_p=chi_A(p)-a*psi_A(p)` starts with1,2 and has recurrence coefficient2A. Reducing modulo H gives `e_p=2^p (modH)`, hence gamma is integral by (B). Moreover

    e_p=2*psi_A(p)-psi_A(p-1)>psi_A(p)=c,

so gamma is positive for sufficiently large p. Since rho is affine in p whereas e_p grows exponentially, sigma=gamma-rho is also a strictly positive integer for all sufficiently large p. Consequently the source's stronger definition `gamma=rho+sigma` is met.

Since P=1 modulo E, `psi_P(n)=n (modE)`. Hence k=2n=1-p modulo E, so h is a positive integer and

    k=R+1+hE.

This is exactly the eliminated source's restoration identity, and (C) verifies its retained packing comparison.

## 7. All strong auxiliary witnesses remain positive

Because p is odd, c=psi_A(p) is odd. Set

    m=c*p, f=chi_A(m), Qaux=Delta*psi_A(m),
    i=Qaux/c^2.

The binomial expansion of `(D+c*sqrt(Delta))^c` shows `c^2 | psi_A(pc)`: its linear square-root term contains c^2, and every higher odd term contains at least c^3. Thus i is a positive integer and

    Qaux=i*c^2, Qaux^2=Delta*(f^2-1).

Take

    saux=p+2m, baux=(saux-1)/2,
    U=chi_Qaux(saux)/Qaux, y=psi_Qaux(saux).

Here m is odd, p=3 mod4, and saux=1 mod4; hence baux is even. The odd-quotient Pell polynomial `Q_b(z)` has the integer identities

    chi_Q(2b+1)/Q = Q_b(Q^2),
    Q_b(0)=(-1)^b*(2b+1),
    Q_b(1-A^2)=(-1)^b*psi_A(2b+1).

Therefore U is a positive integer. Modulo c, the first constant-term identity gives U=p; modulo f, the second identity and `psi_A(p+2m)=-psi_A(p) (modf)` give U=-c. Set

    j=(U-p)/c, o=(U+c)/f.

These are integers. They are positive because, for sufficiently large p, `c>p`, `Qaux>=c^2`, `saux>=3`, and

    U>=chi_Qaux(3)/Qaux=4Qaux^2-3>c>p.

As R=-p, the definitions imply

    U=j*c-R=o*f-c.

Finally the Pell norm at Qaux gives

    Qaux^2*(U^2-y^2)=1-y^2.

This verifies every remaining retained residual. The odd-quotient identities and sign step are sourced and independently proved in the previous negative-kernel audit, with no positive-R hypothesis.

## 8. Conclusion and boundary of the theorem

All nineteen supplied witnesses are strictly positive once the selected p is sufficiently large. Every triangular definition and all eight retained comparisons hold. Thus the complete signed19 sum-of-squares polynomial vanishes, while its unique algebraic restored index is R=-p<0. The unbounded selected p give infinitely many distinct assignments at the same x, already distinguished by the affine outer witness Z.

The construction uses actual compiler numerals unchanged. It is a complete positive child zero theorem, unlike the earlier subsystem-only family. It does not restore a positive supplied W, so it is not a counterexample for positive21 or raw29. The parent positive theorem retains its R>0 hypothesis and is unaffected. No numerical full witness is claimed to have been materialized; existence rests on Dirichlet's theorem, elementary CRT, irrational rotation, and exact integer Pell identities.
