# A quartic in 44 unrestricted integer variables

## Result, exact equation, and provenance

Let Q44 be the sum of the squares of the 27 literal residuals in
`quartic44.json`. Its 44 listed coordinates range over all integers; the
four coefficient ports are fixed numerals, not unknowns. With the complete
`mixed-parity-unrounded-1064921` coefficient tuple of source 34, ordinary
mathematics formalizable in ZFC proves

    (there exists an integer zero of Q44) iff (ZFC has a finite refutation).

Equivalently ZFC proves that absence of integer zeros is Con(ZFC). The
polynomial has exact total degree four: the coefficient of tau^4 is one.
This improves the 45-integer quartic in source 57 by one unrestricted
integer variable, without increasing degree. It is not a minimum-variable
claim, and is not a new kernel-checked Lean/Rocq theorem.

The source snapshot is ProveIt commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486` (23 October 2026). Source 57's
quartic45 is copied into `upstream/`; source 34 supplies the complete
coefficient tuple, its mathematical adapter, and its numerical manifest.
The inherited ordinary Pell and signed-scale proofs are identified below.

## 1. Change in the literal polynomial

Retain all the arithmetic and two common-sign guards of quartic45, except:

* replace `w-u^2=0` by `X-2u^2=0`;
* delete `beta J+1-2 q_half_root^2=0` and its private coordinate
  `q_half_root`.

Thus 45 unknowns and 28 quadratic residuals become 44 unknowns and 27
quadratic residuals. In particular w is still an unrestricted coordinate
and the row `X=(beta J+1)w` is retained. This is an existential reduction,
not a polynomial identity or a same-coordinate equivalence of witnesses.

The key change is that the *global* power X is twice a square. Its
nonnegativity suffices to begin the Pell argument. The sign of the radix
q is recovered only after the equation has forced X to be a power of two.
This avoids separately representing positivity of q or w.

## 2. Fixed numeral hypotheses, actually checked

Write d=1064921, B=2^d, beta=B-1. The actual four ports satisfy

    beta>=17, 0<MC<beta, beta<MF<2 beta, K0>=0.

Here MF is the shifted high mask MF_native+beta. These bounds are proved
in `upstream/COEFFICIENT_PROOF.md` and also checked by reconstructing all
four actual integers from the literal 943-tile list. The reconstructed
minimal unsigned little-endian bytes match *every* raw SHA256 in
`upstream/PAYLOAD_BINDING.json`; the checks do not use small substitute
numerals. The tuple's full native compiler soundness and canonical
completeness are inherited from that coefficient proof. Numerical bounds
alone would not substitute for this full adapter.

## 3. Common signs and absolute-radix bounds

Let a common integer zero of the residuals be given. Set

    q=beta J+1, C=q-F-alpha, Q=|q|,
    Pos(u,v,t)=1+u^2+v^2+t(t+1).

Pos is a positive integer for every integer triple. The retained guards

    F alpha=Pos(FA1,FA2,FA3),
    F C=Pos(FC1,FC2,FC3)

force F,alpha,C to be nonzero and have the same sign. Their sum q has
that sign too; in particular |q|>=3. If J=0 then q=1, impossible. Thus
J>=1 or J<=-1, and respectively q>=beta+1 or q<=1-beta. In either case
Q>=beta-1>=16. This step does not assume q positive.

Define exactly the source packing registers

    G=(q-1)(q-F)+alpha=q(q-F)-C,
    R=G(q^2-1)+(MC+q MF)J.

The retained quadratic packing row is equivalent to
`eta+zeta=R+1+hE`, using L=q^2-1 and N=q^3. The finite auditor checks
this polynomial identity independently, with symbolic coefficient ports.

### Positive q

Here F,alpha,C>=1 and q=Q. Consequently

    Q+2 <= G=Q(Q-F)-C <= Q^2-Q-1.

Moreover J=(Q-1)/beta and the coefficient bounds give

    0 < (MC+Q MF)J < (2Q+1)(Q-1).

Therefore

    Q(Q^2-1) < R < Q^4-Q^3 < Q^4-2.

The stronger upper bound follows by expanding
`(Q^2-Q-1)(Q^2-1)+(2Q+1)(Q-1)=Q^4-Q^3`.

### Negative q

Put F0=-F, alpha0=-alpha and C0=-C. These are positive and sum to Q.
Since J=-(Q+1)/beta, the same signed packing expression becomes

    G=Q(Q-F0)+C0,
    R=G(Q^2-1)+(Q MF-MC)(Q+1)/beta.

Thus

    2Q+1 <= G <= Q^2-2,
    0 < (Q MF-MC)(Q+1)/beta < 2Q(Q+1).

The two positive summands imply the same lower bound as above, while

    R < (Q^2-2)(Q^2-1)+2Q(Q+1)
      = Q^4-Q^2+2Q+2 < Q^4-2,

because Q>=16. Therefore in *both* sign branches

    Q(Q^2-1)<R<Q^4-2,       R-2>3Q+1.                 (1)

No sign of z, w, or s has been used in deriving (1).

## 4. Recover a strictly positive global power scale

Set, as forced by the unchanged lift,

    s=2 v_scale+1, i=2r+1,
    X=qw=2u^2, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=(X+1)Y,
    A=a+2, H=4a+3, Delta=A^2-1=a^2+H,
    D=X+ac+gamma H.

The separate ternary guards for eta and zeta are retained, so
eta,zeta>0 and k>=2. Since s is odd, Y is nonzero and |Y|>=Q^3.
Initially X>=0. If X=0, then a=Y and D=ac+gamma H. Reducing the retained
main norm `D^2-Delta c^2=1` modulo H gives `0=1 mod H`, impossible
since |H|=|4Y+3|>1. Hence X>0.

Because X=qw with q,w integers and q nonzero, X>0 gives X>=|q|=Q.
Combining this with (1) gives

    X>=Q>=16, |Y|>=Q^3,
    |E|>=Q^4>R+2.                                  (2)

This is the only early role played by square-w and positive-q assumptions
in the inherited signed-scale proof. Here it is established without them.

## 5. Apply the inherited Pell argument with Q, not q

The unchanged lift yields the exact arithmetic equations

    tau^2-(XY^2)(XY^2+1)k^2=1,
    D^2-Delta c^2=1,
    (i c^2)^2=Delta(f^2-1),
    (i c^2)^2(V^2-y^2)+y^2=1,
    k=R+1+hE,
    V=of-c=jc-R.                                   (3)

All variables in (3) that were permitted to be signed in the source
proof remain signed. The two exposed congruences for V are present
literally; no quotient T is assumed integral without proof.

The argument in `upstream/ODD_SCALE_27_PROOF.md`, Sections 2--4, uses
q only through the inequalities (1)--(2), and uses s only through the
sign and nonvanishing of Y. Thus replace the positive symbol q in those
inequalities by Q and interpret its negative-s branch as Y<0.
For clarity, its substantive steps are recorded here.

If Y<0, put Z=-Y, B1=(X+1)Z-2 and c0=-c=kZ-eta. Then

    k(Z-1)<c0<kZ, B1>=2,
    |tau|=chi_P0(n), k=2 psi_P0(n),
    |D|=chi_B1(p), c0=psi_B1(p),
    P0=2XZ^2+1>B1, p>n>= (R+1)/2>=24.

The index congruence follows from P0=1 mod |E| and k=R+1+hE;
the nonnegative quotient follows because 0<R+1<|E|. The main-coordinate
growth gives c0>B1(B1^2-1)^2, c0>2p, c0>2R. The inherited ordinary
strong-rank lemma is therefore applicable: it gives
`|f|=chi_B1(m)`, p|m, c0|m, m>=c0>2p. The signed auxiliary step-down,
using the two V congruences in (3), gives p=R. This is precisely the
ordinary-strong case of the cited proof; it does not divide a strong
equation by an unchecked factor.

The no-wrap argument now gives R=2n-1. The source ratio estimate yields
Z>2^R. For either sign of D, the main-root congruence is respectively

    X=-2^R mod H,    or    X 2^R=1 mod H.

The strict intervals

    0<X+2^R<X+Z<|H|,
    1<X 2^R<XZ<|H|

exclude both. Thus Y>0.

For Y>0 the positive-scale argument of
`upstream/SIGNED_DOMAIN_29.md`, from "Signed h" through "Signed gamma",
applies with the same replacement q -> Q. It uses only eta,zeta>0,
(1)--(3), X>=Q, Y>=Q^3 and the ordinary strong-rank lemma. It recovers
the main rank p=R, the first rank R=2n-1, the positive main root
D=chi_A(R), and then the exact identity

    X=2^R.                                          (4)

For the sign of D, its lower-ratio estimate gives
`0<X 2^R<a<H-1`; the negative-D congruence would be
`X 2^R=-1 mod H`, impossible. For positive D the source recurrence gives
X=2^R mod H and its strict bounds give equality. No sign of q, w or z
enters these steps once (1)--(3) have been established.

This proof uses named unbounded Pell results; the finite script does not
certify them by testing a finite box.

## 6. A Mersenne-radix sign lemma

For every integer d>=3 and t>=0,

    -2^t is not congruent to 1 modulo 2^d-1.         (5)

Indeed write t=ad+r with 0<=r<d. Since 2^d=1 modulo 2^d-1, the least
positive residue of 2^t is 2^r. But

    1<=2^r<=2^(d-1)<2^d-2,

so that residue cannot equal -1 modulo 2^d-1. This proves (5).

Now q divides the positive power 2^R by (4), so q=+2^t or -2^t for
some 0<=t<=R. The fixed definition q=beta J+1 and (5) exclude the
negative sign. Thus q>0. Common signs give F,alpha,C>0; then J>0,
w=X/q>0, and s=Y/q^3>0. Since s is an odd integer, the original odd
cubic-scale interface is preserved.

This is where the sign of q is first recovered. Inferring it before (4)
would leave a gap. The fact that d is odd is not needed for (5); d>=3
suffices. Odd d is needed only in inherited canonical completeness.

## 7. Literal transport and the compiler endpoint

There is a small transcription error in the prose accompanying quartic45:
its literal transport row expands to

    (K0+w)C=z(q-1)+F,                               (6)

not `(K0+w)C=(z-1)(q-1)+F`. The independent auditor verifies (6) exactly.
This does not spoil source45's existence reduction, but its conclusion
at this point should be z>0 rather than z>1.

Here R>3q and q>=16 imply 2^R>q^2. Therefore w=2^R/q>q>F. Since
K0>=0 and C>=1, the left side of (6) exceeds F. Hence z(q-1)>0 and
z>0. In the original unshifted positive factor convention of
`upstream/FIXED_BLANK_67_PROOF.md`, take z_source=z+1; then its transport
factor Nt equals one. This states the coordinate shift explicitly.

After (4), soundness proceeds directly by the already proved
"Power and compiler recovery" stage (Section 5) and blank finite-window
stage (Section 6) of that fixed-blank proof, transported to the full source
34 tuple by `upstream/COEFFICIENT_PROOF.md`. The preceding signed-root and
exposed-quotient proofs justify the kernel inputs. In detail, q is a
power of two, q^3 divides Y, and 3q+1<R<q^4. The half-binomial kernel
gives the population threshold, q=beta J+1 forces q=B^N, and inverse
population plus (6) recovers the disjoint native masks. The full source
34 native geometry then decodes a genuine blank K215 accepting tableau.
The calibrated machine endpoint supplies a finite ZFC refutation.

One must NOT claim that the current tuple already has w a square or q
twice a square: (4) alone does not force the exponent t to be odd.
Those two restrictions were sufficient witness choices, not needed by
post-power native soundness. If an explicit zero of quartic45 is wanted,
first decode the accepting computation, then choose the source's fresh
canonical witnesses, which do have both restrictions.

## 8. Completeness

If ZFC has a finite refutation, the inherited K215 calibration gives a
blank halt. Source 34's complete coefficient adapter provides canonical
positive arithmetic witnesses. Its parity proof gives

    q=2^t with t odd, R=3 mod4, X=2^R,
    w=2^(R-t), s odd, i odd, eta,zeta,F,alpha,C>0.

Retain these witnesses in every unchanged row and set

    u=2^((R-1)/2).

The exponent is a nonnegative integer, so X=2u^2. The deleted q-half-root
row needs no witness. Each positive number F alpha and F C has a Pos
representation: Legendre's three-square theorem applied to 4n-3 yields
`n=1+x^2+y^2+t(t+1)`. Supply the two triples and retain the eta,zeta
triples. Thus every residual of Q44 is zero.

This establishes both directions. The equivalence and all imported
finite compiler, elementary Pell, and proof-calibration arguments are
formalizable in ZFC; no assumption of Con(ZFC) is used to construct the
equation or its fixed coefficients.

## 9. Verification and attribution

Run `python3 build_verify44.py` or `python3 -O build_verify44.py`. The
standard-library script reconstructs all four fixed integers and matches
their source SHA256 digests, checks the newly required mask inequalities,
emits the exact polynomial packet, expands its sum of squares with symbolic
coefficient ports, verifies every unknown is live, checks its exact degree
and coefficient of tau^4, and independently verifies the packing and literal
transport identities. It checks 108570 elementary finite-bound cases and
5047 negative-dyadic examples as diagnostics, alongside their universal
proofs above. No assertions are used for acceptance.

Inherited contributions are: the K215 calibration; the native compiler and
source34 coefficient adapter; the ordinary and signed Pell rank arguments;
the source57 common-sign guards and omission of an early transport guard;
and the low-degree quadratic lift. The new contribution is the global
twice-square guard, absolute-radix bootstrap, delayed sign recovery via
(5), and their explicit quartic44 composition. The technique's global
novelty has not been established. Internal AI-assisted review is not
external peer review.
