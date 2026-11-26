# Independent referee note on the new analytic results

## Verdict

I checked the positive-ramp moment theorem, its bounded-coefficient integer-support sharpness construction, the floor discretization, its meromorphic expansion, and the proposed joint-filter theorem. I found no mathematical error in their stated main conclusions. The scope qualifications below should be preserved in the final manuscript.

## 1. Positive-ramp local moment bound

For a positive locally finite measure on [1,infinity), H(t)=S(1/t) is finite and convex for t>0. Consequently f(v)=R(x/v) satisfies that f(v)-A log v is convex. The midpoint inequality

    f(1-z)+f(1+z) >= 2f(1)+A log(1-z^2)

has the correct sign. Jensen applied to the convex increasing map t -> (t_+)^p is valid for every real p>=1, including p=1. For z<=1/2, log(1-z^2)>=-4z^2/3. With

    r=min(1/2,sqrt(3h/(4A))),  h=R(x)_+,

both the midpoint lower bound h/2 and the change-of-variables Jacobian are correct. In particular,

    (1/x) integral_[2x/3,2x] R(y)_+^p dy
       >= (2^(2-p)/9) h^p min(1,sqrt(3h/A)).

The coefficient 2^(2-p)/9 and both exponents in the resulting maximum bound were checked. The assumption x>=3/2 ensures all integration arguments are >=1. A=0 is correctly treated separately. No differentiability assumption on the measure is needed.

Covering [2x/3,2x] by at most a fixed number of dyadic intervals with lengths comparable to x is sufficient, even if the exponent 1-p*gamma is negative. A dyadic moment bound with every epsilon>0 first makes the local mean tend to zero, so h tends to zero; then the small-h branch gives exponent 2p*gamma/(2p+1). The conversion of epsilon after taking powers is legitimate.

## 2. Sharpness construction

All derivative constants are valid:

- For psi(z)=(1-z^2)^3 on [-1,1], zero elsewhere, |psi'|<=2 and |psi''|<=6; psi, psi' and psi'' vanish at the endpoints, so the extension is C^2.
- With X_k=4^k, h_k=X_k^(-alpha), L_k=10X_k sqrt(h_k), and h_k<=1/400, each support lies in [X_k/2,3X_k/2]. The supports are disjoint.
- The density estimate is |w-1|<=27/200+(3/5)sqrt(h_k)<=33/200. Thus the more generous 1/2<=w<=3/2 is valid.
- The atom at 1 is necessary and correctly included: mu_c([1,x])=x+x^2 R_c'(x), and integration of S'=mu_c([1,x])/x^2 gives S-log x=R_c exactly.
- Every dyadic interval [X,2X] meets at most two supports, whose centers lie in [2X/3,4X]. Hence the full dyadic moment estimate, not merely an estimate at chosen scales, follows from the computed individual bump areas.
- The exponent identity alpha(p+1/2)=p*gamma is correct. Since x^2 R_c'=O(x sqrt(h_k)), the summatory measure is asymptotic to x.

**Scope:** the integer-support construction proves the advertised sharpness for 0<gamma<1, including the main gamma=1/2 application. Do not state that this particular construction proves sharpness for every gamma>0. The local interpolation exponent itself is sharp in the stated positive-ramp class.

**Terminology:** the a_n are positive, uniformly bounded **real coefficients indexed by integers**. They are not generally integer-valued coefficients. “Bounded coefficients on integer support” is accurate; “bounded integer coefficients” is not.

## 3. Floor discretization

I derived the identity directly. For N=floor x,

    R_d(x)-R_c(x)
       = - integral_[N+1,infinity) w(u)(1/floor(u)-1/u) du
         + integral_[x,N+1] w(u)(1/u-1/x) du.

Both terms are nonpositive. The centering constant c_d converges absolutely because the contribution from [n,n+1] is at most (3/4)n^(-2). A direct bound for the error is

    0 <= R_c-R_d <= (3/4)/N + (3/4)/x^2 <= 4/x,  x>=2.

This is even a little stronger than required. Therefore R_d,+<=R_c, so the moment upper bounds survive unchanged. At integer centers X_k, the error O(1/X_k) is negligible compared with X_k^(-alpha) because alpha<1. Summing the cell masses gives mu_d([1,x])=N+1+(N+1)^2 R_c'(N+1), so mu_d([1,x])~x. The finite extra mass at index 1 does not alter that assertion.

The example does not have prime-power support, an Euler product or the growth/functional equation of a standard L-function. Its stated arithmetic limitation is necessary.

## 4. Meromorphic expansion

Formula (9) is correct. The factor 10, the power 100^m, and the exponent 1-s-alpha(m+3/2) all follow from h_k L_k X_k^(-s) and the even binomial expansion. Initial termwise integration and summation hold in a sufficiently far right half-plane. On a fixed compact set, the rising-factorial quotient (s)_(2m)/(2m)! grows at most polynomially in m; the factor (100*4^(-k0 alpha))^m gives normal convergence when its base is <=1/4. The pole set is locally finite because its real parts tend to minus infinity with m. This proves global meromorphic continuation of F_c.

The possible poles are simple. At a positive real pole u, the denominator derivative is log 4 and the geometric numerator is 1, giving the stated positive residue 10*100^m*J_m(u)/log 4. Distinct m have distinct real parts, so poles from distinct m cannot combine into higher order poles. Nonreal residues may vanish; retaining “possible poles” is correct.

The bound R_d-R_c=O(1/x) proves that F_d-F_c is holomorphic only on Re s>0 by this argument. Thus F_d has the same poles and residues as F_c in that half-plane; no global continuation of F_d has been established. The manuscript already preserves this distinction.

The inequality 1-3alpha/2<=1-gamma is equivalent to p>=1 and is correct, with equality for p=1. At gamma=1/2 there are no poles right of 1/2 even though the pointwise peaks have the weaker stated decay. This is consistent with the positive-part Mellin criterion.

## 5. Joint-filter theorem

Assume R is real, locally integrable, and has an initial Mellin half-plane of absolute convergence (polynomial growth suffices). Let F(s)=integral_1^infinity R(x)x^(-s)dx continue meromorphically to Re s>beta. Assume all real poles there are simple with nonnegative residues.

For a>0 with a>=1,

    Mellin[R(a x)](s)
       =a^(s-1) F(s)-a^(s-1) integral_1^a R(u)u^(-s)du.

The last term is entire, so finite-interval boundary terms must appear in the transform identity but do not affect poles.

For the proposed pair,

    A(x)=5R(x)+6R(2x),
    B(x)=25R(x)+30R(2x)+36R(4x),

the multipliers are P=5+6z and Q=25+30z+36z^2, z=2^(s-1). At every real s both are strictly positive; therefore their transforms inherit only simple real poles with nonnegative residues from F. Applying the positive-part Landau lemma separately to A and B proves that both are absolutely Mellin integrable for every real sigma>beta, and their transforms are holomorphic there.

The identity Q-6zP=25 is exact. It excludes a common zero anywhere in the complex plane, so F is holomorphic on Re s>beta. More strongly, the pointwise identity

    25R(x)=B(x)-6A(2x)

gives, for sigma>beta,

    integral |R| x^(-sigma) dx
      <= [ integral |B| x^(-sigma) dx
           +6*2^(sigma-1) integral |A| x^(-sigma) dx ]/25.

Thus the explicit pair proves absolute integrability as well as holomorphy. This does not require a separate bound on R_+.

For checking the positive-part Landau step: F_+ is holomorphic; the transform of the negative part is F_+-F. If its real convergence abscissa exceeded beta, Landau would force a real singularity there. Meromorphy makes it a simple pole of residue at most zero, contradicting positivity of the negative-part transform as the real abscissa is approached from the right. Polynomial growth ensures a finite initial abscissa. This argument is sound.

## 6. General-family scope and necessity

For finitely many nonzero polynomials P_j with nonnegative real coefficients and a common dilation base b>1, define T_j R by replacing z^k with R(b^k x). The universal statement

    “for every admissible R, positive-part Mellin integrability of every
     T_jR throughout Re s>beta forces F holomorphic there”

holds if and only if the multipliers P_j(b^(s-1)) have no common zero in that half-plane.

Sufficiency follows exactly as above: each filter transform is holomorphic by Landau; at a putative pole of F, at least one multiplier is nonzero. Necessity uses a common zero rho with Re rho>beta and

    R(x)=Re(x^(rho-1)).

The common zero cannot be real because each nonzero positive-coefficient multiplier is positive on the real axis. Hence F has two nonreal simple poles, no real poles, and every T_jR vanishes identically. This is a valid counterexample satisfying the admissibility conditions.

Necessary wording qualifications:

1. The “if and only if” concerns the **universal detection property**, not each fixed individual R.
2. Common zeros are zeros of the attained Mellin multipliers in Re s>beta. A shared polynomial root z=0 is never attained by b^(s-1) and is irrelevant.
3. The general criterion directly proves holomorphy. Keep the strong absolute-integrability conclusion attached to an explicit finite Bezout recovery identity, as provided by the pair above, unless an additional inversion argument is supplied for a more general family.
4. The explicit pair can be individually blind: P has root -5/6, while Q has roots (5/6)exp(plus-or-minus 2pi i/3). Their hidden poles lie on Re s=1+log_2(5/6), approximately 0.73697. The pair has uniform separation, since |Q|+6|z||P|>=25. This is a correct useful contrast to relying merely on incommensurable zeros.

## Recommendation

The new analytic results are suitable for inclusion as self-contained proved additions, with the limitations above. They do not establish the missing arithmetic estimate for a nonabelian L-function. The sharpness construction explains exactly why a good one-sided moment can suffice for zero exclusion while yielding weaker pointwise control through positivity alone.

## 7. Independent referee check of the explicit nonabelian local example

I read the working mathematical audit (now developed in `sections/nonabelian_frame.tex`) and the complete checker (delivered as `code/check_nonabelian_frame.py`), and replayed the latter successfully. The script exited with status zero and `all_checks_passed: true`. Its only file mutation is regeneration of its own JSON certificate. It uses exact rational and finite-field arithmetic and elementary trial-division primality tests; the output is an arithmetic certificate, not a Lean proof or a verification of the global transfer.

**Field and trace frame.** The signs of `X^3-4X+1` at `(-3,-2)`, `(0,1)`, and `(1,2)` give three distinct real roots. The rational-root test and nonsquare discriminant 229 give Galois group S3 and splitting field `F=L(sqrt(229))`. The displayed trace norms for the six-element basis are correct: the first three norms are twice the cubic norms, the last three are a further factor 229, and mixed blocks vanish by the quadratic trace from F to L. Thus the positive integer multiplicities with bound `48*229^2=2517168` prove the claimed frame simultaneously at all embeddings. All its bad rational prime factors are among 2, 3, and 229.

**Intersection and tensor frame.** Since 229 divides the conductor, the intersection of F and the cyclotomic field is exactly `Q(sqrt(229))`: an intersection with an abelian extension must lie in the maximal abelian subextension of the S3 field, and the quadratic field of conductor 229 is indeed present. The fiber-product degree is consequently `3*phi(q1)`, not `6*phi(q1)`. The source parameter lemma ensures `gcd(d,q1)=1`; both F and the cyclotomic field are unramified at d, so the ramified quadratic field K is disjoint from their compositum. The claimed CM type cardinality follows. Restricting the product frame to compatible pairs of embeddings preserves its row orthogonality, even though the list of product vectors is redundant. No linear disjointness assumption is being smuggled into this step.

**Normalization and local integrality.** If the original frame has bound B, replacing each vector w by w/B and each multiplicity m by Bm gives exactly `Bm/B^2` times the old quadratic expression, hence a Parseval frame. This means B copies in total, or B-1 additional copies, before scaling. The phrase “B additional times” in the audit should be changed accordingly. At an inert-K prime p, the splitting lemma for all primes dividing q1 excludes p from the divisors of B. Thus every conjugate of every normalized vector is p-integral. For the later general sentence about clearing denominators, “integral above p” should mean integral at every place above p (membership in the p-localized ring of integers), not merely at one chosen prime. The explicit construction satisfies the stronger condition.

**Frobenius partner and the coupling.** The asserted inert prime is unramified in all of E: it is neither d nor a prime dividing q1, in particular not 229. Arithmetic Frobenius h at the chosen p-adic embedding therefore gives congruence modulo p, rather than only modulo a smaller uniformizer. Complex conjugation c is central in this Galois CM compositum. For odd e, `c*h^e*tau` fixes the prescribed embedding of K. Conjugating it cancels c, leaving precisely the p^e Frobenius congruence for every conjugate coefficient. Reducing the p^e power of each linear form modulo p and then using Parseval proves the stated coupling: the mixed coefficient is the Parseval inner product of the rows indexed by `partner(tau)` and `tau'`. The action order is consistent; it is left composition by `c*h^e`. The exclusion of the ramified case p=d is necessary and is correctly explicit.

**Coset selector.** For `B=tS` with `S` contained in H, the count of a in H with ga in B is the cardinality of `gH` intersected with B. Since B lies in the single left coset tH, it equals `|B|` if `gH=tH`, and zero otherwise. This proof does not require commutativity. In this field H is central, its index is `3*phi(q0)`, and `t=(1,-1)` is allowed because the quadratic character of 229 is even. The restriction of c to `F Q(zeta_q0)` is exactly t. Therefore the partner coset condition is exactly `Frob_p^e=1` in that field, including higher prime powers. For e=1 it detects complete splitting; it does not reduce to a cyclotomic congruence. Since the identity class is invariant under conjugation, the correlation is independent of the chosen prime over p even when the sparse subset S is not itself invariant.

**Concrete primes and scope.** The replay verified primality of d and both displayed primes, the source congruence conditions, inertness in K, and factor degrees `[1,1,1]` and `[3]` for the cubic. Thus the two primes really share the stated arithmetic progression and have different S3 Frobenius classes. It also checked all 60 finite-model elements and the counts `[6,6]` versus `[2,0]`. The model is clearly identified as a group-theoretic test, not an additional number-field realization. No false global conclusion is present: the audit explicitly leaves the required Weil lattice, frame bounds and unit conditions, odd-cocycle budgets, level-prime estimates, local crystalline defects, spanning inputs, and analytic bridge unproved. The example establishes local arithmetic visibility of nonabelian Frobenius; it does not establish the missing global prime-sum inequality or a new case of Artin holomorphy.

**Verdict.** The mathematics in this local example is sound. Only the two wording qualifications about total copy count and integrality at every place above p are needed; neither changes its explicit construction or its conclusions.
