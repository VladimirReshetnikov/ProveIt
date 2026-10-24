# Shared square radius in the projected C222 compiler

## Exact changes and provenance

The baseline is `Computability/DiophantineConsistency/candidates/projected-factorial-radius`, at repository commit `84e16e43092614bae262ca59651cb9d77e31a255`. It supplies the eight-column direct C222 source and uses two proposed factorial outputs `T` and `J`, at arguments `H` and `t`, with separate radii `T H^2` and `J t^2`. Its binomial radix is `B(V_H+V_t+1)`.

The squared-output fixed-point theorem and the use of one square for all smaller factorials ALREADY occur in the incoming `ConZFC_Bootstrap_Certificates_2026-10-24.zip`, `direct/proofs/NEW_RESULTS.md`, Sections 2 and 3. The contribution here is their composition with the better eight-column projected source, and the following coefficient bound which makes the smaller reused radix sound before factorial correctness.

Keep both proposed outputs but set one common radius

    rho = T^2,
    C_H = binom(rho+H,H),   V_H = (rho+1)^H,
    C_t = binom(rho+t,t),   V_t = (rho+1)^t.

For n=H and n=t keep the natural remainder equations

    V_n + C_n = C_n F_n + r_n + 1,
    C_n = r_n+s_n+1,

where F_H=T and F_t=J. Set the sole binomial radix to

    q = B(V_H+1).

Every POWER and BINOMIAL notation is explanatory only: the supplied compiler materializes its finite shared Pell and digit graphs as quadratic residuals, and then forms their squared sum.

## 1. A uniform coefficient lemma

**Lemma.** If rho,n are positive integers and 0<=j<=n, then

    binom(rho+n,j) <= (rho+1)^n.

Proof by induction on n. The n=1 case consists of the values 1 and rho+1. At n>1 and j<n, Pascal's identity and the preceding induction hypothesis give at most

    2(rho+1)^(n-1) <= (rho+1)^n.

At j=0 interpret the nonexistent negative-index binomial as zero; alternatively check j=0 separately. At j=n, use the exact product

    binom(rho+n,n) = product_(k=1)^n (rho+k)/k <= (rho+1)^n,

because rho+k<=k(rho+1). This proves every case.

Unlike the narrower unimodality argument in the baseline, the lemma does NOT require rho>=n. This matters because initially T is an arbitrary proposed factorial and its intended size cannot be assumed.

## 2. Pointwise recovery order at an arbitrary natural zero

The shared Pell frame first establishes the actual values of power requests. In the unfused construction this is the baseline theorem. If fixed powers have been absorbed into that frame, first apply its individual-request soundness theorem to the two new requests with independently positive exponents, recovering the carrier and H. This gives

    R=2+t+x+y+M0 >=4,
    t>=1,   H=R^E >= R^4 >= t,

where E is the actual fixed local-majorant exponent. Only then recover all remaining requests. This first/second-stage order is required: after absorption H is no longer syntactically positive before its power graph has been interpreted.

The actual power call with base T and exponent t enforces T>=1 directly from its modulus row `2 A T = T_mod+T^2+1`; a zero base is impossible over naturals. Similarly the base-q row excludes q=0. Thus rho=T^2>=1, and the defining q=B(V_H+1) gives B>=1 and q>V_H before any factorial or CRT-product meaning is invoked.

By the uniform coefficient lemma, every lower coefficient needed to extract C_H is at most V_H<q. For C_t, the same lemma gives at most

    (rho+1)^t <= (rho+1)^H = V_H < q.

The inherited exact low-digit extraction therefore recovers both binomial values without knowing T=H! or J=t!.

The two ceiling rows now say precisely F_n=ceil(V_n/C_n). Apply the squared-output fixed-point theorem first at n=H to obtain T=H!, and then the common-radius estimate at n=t to obtain J=t!. Complete proofs of those two statements are included next; no circular size assumption is needed.

## 3. Squared-output factorial fixed point (inherited theorem, proof repeated)

For all n,F>=0, let K=n!, rho=F^2 and

    f = (rho+1)^n / binom(rho+n,n)
      = K product_(j=1)^n (rho+1)/(rho+j).

Then `ceil(f)=F` iff F=K.

Any fixed point has 1<=F<=K. For n>=2 the finite product inequality gives

    0 <= K-f < K n(n-1)/(2F^2).                 (*).

For n>=4 each factor increases with rho, so f>=2^n/(n+1). At n=4 this forces F>=4. For n>=5, induction from 2^5>=5*6 gives 2^n>=n(n+1), hence again F>=n. Substitution in (*) yields f>K/2 and therefore F>K/2. A second substitution gives

    K-f < 2n(n-1)/K <=1,

since n!>=2n(n-1) for n>=4 (equality at4 and induction afterward). Thus ceil(f)=K, proving soundness. At n=0,1, f=1. At n=2, f=2(F^2+1)/(F^2+2) lies strictly between1 and2. At n=3 only F in{1,...,6} is possible; the ceilings are2,4,5,6,6,6, so onlyF=6 is fixed.

For completeness F=K gives K-f<n(n-1)/(2K)<=1/2 for n>=2; n=0,1 are immediate. Thus ceil(f)=K.

With T=H! and1<=t<=H, the common radius rho=T^2 gives

    0 <= t! - (rho+1)^t/binom(rho+t,t)
      < t! t(t-1)/(2(H!)^2)
      <= H(H-1)/(2H!) <=1/2

when t>=2. At t=1 the ratio is exactly1. Hence its ceiling is t!, independently of any prior value of J.

Finally the literal ceiling rows are equivalent to C(F-1)<V<=CF, because0<=r<C and V+C=CF+r+1. They automatically exclude F=0 whenever V,C>=1. Given F=ceil(V/C), set r=V+C-CF-1 and s=C-r-1; both are natural.

## 4. The remaining binomial digits fit the smaller radix

After factorial recovery write T=H!. The baseline's raw remainder rows already give B<TQ for

    Q=(1+(t+1)T)^t+2,

without assuming that B has its intended CRT-product value. The unchanged aggregate range row gives every positive encoded coordinate a_i<=8B. The baseline ordinary estimate therefore still applies:

    Q+t, a_i < H^((t+2)(H+1)).

Every required lower index k is <=R. For 0<=j<=k, the relevant coefficient is bounded by

    binom(N,j) <= N^j <= N^k < H^[k(t+2)(H+1)].

Here N>1 for all actual requests. The elementary paired-factor identity gives

    (H!)^2 = product_(i=1)^H i(H+1-i) >= H^H.

Every factor inequality follows from `i(H+1-i)-H=(i-1)(H-i)>=0`. Thus

    V_H=((H!)^2+1)^H > H^(H^2).

Since R>=4 and H>=R^4, one has4R(R+2)<=H. Consequently

    k(t+2)(H+1) <=R(R+2)(H+1) <=H(H+1)/4 < H^2.

All remaining required coefficients are therefore strictly below V_H<q. The inherited fused range graphs and CRT-product identity now apply, in this order. There is no use of the CRT-product meaning of B before it is established.

## 5. Completeness and finite certificates

Given an actual finite C222 refutation, choose the padded proof horizon, carrier, accumulator path and beta data as in the accepted source. They determineR,H. SetT=H!,J=t!,rho=T^2, and choose the two ceiling remainders using Section3. Choose the actual CRT productB and positive canonical column representatives in[1,B], giving the unchanged aggregate slack. Defineq=B(V_H+1). Sections1 and4 give every required digit bound. The true power values and ordinary Euclidean remainders satisfy all arithmetic macros; the finite-unit period argument then supplies the common Pell frame and all index witnesses simultaneously. This is an ordered finite construction, not an assumed solution of a circular system.

The unchanged eight-column source, Horn-flow theorem and C222-to-ZF-to-ZFC refutation calibration complete the equivalence. The new transformations use ordinary finite arithmetic and induction formalizable in ZFC. They neither prove consistency nor supply a new proof-assistant/object-ZFC derivation.

All final residuals are quadratic and the single polynomial is their sum of squares. Every projected natural coordinate is restored by an integer polynomial independently certified nonnegative; the whole residual list is substituted at each elimination, not merely sampled.

## Measured materializations

The unfused shared-square source has660 natural variables and578 quadratic residuals. At support cap64 it has396 variables,314 rows,7949 monomials and height83843200. At cap256 it has395 variables,313 rows,8131 monomials and height83843268. The incoming centered-factorial construction already has395 variables,313 rows,8292 monomials and height83843425; the shared-square cap256 point improves terms and height at that count, but does not establish a new variable minimum by itself.

After both fixed-power absorptions, the shared-square source has656 variables and569 rows. Cap16 gives373 variables/286 rows/6949 terms; cap64 gives371/284/8060; cap256 gives370/283/8351. The cap256 coefficient height is5261245166964942047373384383. Every equation has exact degree4. The substantially larger coefficient height is a real cost of moving large fixed exponents into scalar coefficients; it must be reported rather than treating the reduction as domination in all metrics.

## 6. A shared exponent for carrier and majorant (composition)

The actual delivered certificates give label exponent bound3,445,908, rounded to
lambda=4,194,304=2^22, and local exponent bound6,893,253, rounded to
kappa=8,388,608=2^23. Thus kappa=2lambda exactly. Replace `t=t0+1` by
`t=t0+2`, and request

    M0+1=(t+1)^(lambda*t),
    H=R^(lambda*t).

The carrier is IDENTICAL to the old carrier at the same horizon t, because
`((t+1)^t)^lambda=(t+1)^(lambda*t)`. The majorant need not be identical:
its only semantic role is the proved lower bound. Since t>=2, lambda*t>=kappa,
so H>=R^kappa, retaining every original local bound and H>=R^4>=t.

Existence of a valid finite proof path is unchanged by t>=2. The source has
truth-padding rule `(0,0)->0` and weight1 at label0. Inserting such a row
leaves the accumulator unchanged, and supplies zero schema parameters and
valid beta quotients. Begin by padding the actual proof tree to any horizon
at least2 and at least its schema-parameter maximum, THEN choose the carrier,
accumulator values and beta encoding. This ordering avoids moving a carrier
while keeping an old path encoded at an incompatible carrier.

For soundness the two requests share one positive index k=lambda*t. The
common frame A>W^W follows from nonnegative atoms and the positive frame
ordinate independently of either output. The pointwise shared-power argument
therefore recovers both calls first: their bases t+1 andR are positive, their
exponentk is positive, and all are bounded byW. Only after recovering H does
one invoke other index/power soundness statements whose exponent positivity
uses H. The common-product auxiliary index guards remain valid when
recovering this first seed; the precise selected-request argument is provided
in the independent fusion proof.

This avoids the separate seed certificate for fixed index kappa. No new
assumption about ZFC consistency, nor any semantic power primitive, is
introduced: both requests have their ordinary finite Pell graphs and all
wires remain counted in the quartic.

## 7. An auxiliary index with no power call

The new factorial requests use exponent atoms `rho+H` and `rho+t` in their binomial graphs. Both H and t already have indexed Pell pairs, but rho itself is not an exponent of any requested power. The old additive compiler therefore did not treat rho as an available summand. Add rho to the finite set of allowed seed indices. Generate its ordinary seed index certificate on demand, and generate the two composite pairs by

    X_(rho+n)=X_rho X_n+(A^2-1)Y_rho Y_n,
    Y_(rho+n)=X_rho Y_n+Y_rho X_n,        n in{H,t}.

These are the existing polynomial Pell addition identities. The new seed is positive before factorial meaning: rho=T^2>=1 follows from the actual base-T modulus row. No power value at exponent rho is introduced or asserted.

For soundness first recover every seed pair from its unchanged index certificate, in the previously described power recovery order; then use the two exact identities. For completeness include rho in the finite list whose positive Pell ordinates enter the shared finite-unit period. The same finite group/CRT argument supplies the auxiliary solution and residue base for this enlarged seed set. The two old composite seed tests can then be deleted because their pairs are fixed by the exact addition law. Only seed ordinates enter the auxiliary product, exactly as in the inherited additive-index compiler.

The modified index dependency graph is acyclic: rho, H and t precede their sum atoms as ordinary arithmetic nodes. In the actual implementation the only change to the compiler's index selection set is union with{rho}; existing source-node ordering and addition detection are retained.

The final common-exponent/shared-square/auxiliary-index source has633 natural variables and550 quadratic rows. Its support-cap256 contraction has358 variables,275 rows,8229 monomials and coefficient height9903520314287616167992362844. The cap64 alternative has359 variables,276 rows,7938 monomials and height9903520314287616167983974226. The cap16 alternative has361 variables,278 rows,6759 monomials and height9903520314287616167799424614. All degrees are exactly4.
