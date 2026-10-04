# Signed auxiliary quotient: source-specific recovery of the positive domain

This proof-only continuation proposes the following extension for independent review. Fix the **entire valid inherited complete75 compiler recipe** used by the literal complete84 polynomial. Let the ordinary input and every supplied witness except `auxiliary_quotient` T be strictly positive integers, and allow T to be any integer. Then every zero has **T>0**. Thus the signed-T and original positive zero sets coincide on the same supplied coordinates, and the existing ordinary-input soundness and completeness transfer by the identity map.

This is stronger than an ordinary-input projection statement. It is not a theorem for arbitrary mask numerals, arbitrary signed witnesses, or a local strong/auxiliary subsystem. It changes no source, count, degree or witness bound. This note has not executed any author, predecessor, archived or copied program. The accompanying JSON records inert source/proof hashes and exact read spans; the source row checks are binding evidence, not a full compiler certification.

## 1. Starting point and actual source bindings

Use the notation of the accepted `complete84_signed_quotient_absorption.md`, §§1–4:

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=Y(X+1),
    A0=a+2, Delta=A0²−1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    S=Delta*i*c², V=c(Tf−1)−Rf².

In the actual 84-row JSON, X,Y,E,k,c,a,D,Delta,H,R,S,V are respectively `wn2`, `sn2`, `UM`, `R10b`, `R10a`, `R12`, `R14`, `A`, `a4m5`, `r_lhs`, `aux_coefficient_root`, `aux_u_rhs`. The supplied T occurs only in `auxiliary_Tf=T*f`. The scaled strong factor is Delta*f²−S²; the auxiliary factor is S²V²−(S²−1)y². The complete all-ring identity F84=Delta*F85 remains valid with signed T, and Delta>0 does not depend on T.

The accepted signed-T proof supplies, without invoking a positive-T parent zero:

    all seven normalized factors = 1;
    q>=B>=16, 3q+1<R, R+2<q⁴<=E<a;
    tau=chi_P(n), k=2psi_P(n), P=2XY²+1;
    D=chi_A0(R), c=psi_A0(R), n=(R+1)/2;
    f=chi_A0(m), psi_A0(m)=i*c², R*c divides m;
    c>2R, f>2c, m>2R;
    F+Z<q, C>=0, |W|<q;
    kY<c<k(Y+1).

In particular R is odd; put r=(R−1)/2>=24. The source ratio interval is literal: c=kY+eta with 0<eta<k. At this stage neither R=3 modulo4 nor T>0 nor any binary mask is assumed.

The fixed numeral recipe includes

    B=2^d, MC=2 mod4, MF_native=4 mod8,
    0<MC,MF_native<B−1,
    pc(MC)+pc(MF_native)=d,
    MF_source=MF_native+B−1.

Here `MF` in the actual source is MF_source, not MF_native. These are the hypotheses in `complete75_coupled_index_linear88.md` §1, lines31–41, and `FIXED_RAW_UNIVERSAL_75_PROOF.md` §3. The signed-T bootstrap uses the same convention.

## 2. Power recovery needs only odd R

The elementary Pell estimates, for integer parameter L>=2, are

    (2L−1)^(j−1) <= psi_L(j) <= (2L)^(j−1), j>=1.

They follow directly by induction from the recurrence and monotonicity. Set

    xi=(X+1)^(2r)/X^r, k0=k/2=psi_P(r+1).

The lower estimate gives

    c/k0 >= xi*(1+3/(2a))^(2r)
                     *(1+1/(2XY²))^(−r) > xi.

The last comparison follows from 6XY²>a; indeed X>=16 and Y>=q³>=4096. No parity of r, upper approximation, decoded q-power or positive V is used. Since c/k<Y+1,

    Y>xi/2−1>X^r/2−1>X^r/3,
    a=Y(X+1)>X^r(X+1)/3>X^(r+1)/3.

The third inequality uses X^r>6. Consequently

    2^R=2*4^r < X^(r+1)/3 < a,
    0<X<a.

For z_j=chi_A0(j)−a*psi_A0(j), the initial values are 1,2 and the recurrence is z_(j+1)=2A0*z_j−z_(j−1). Since 4A0−1=H+4, induction gives z_j=2^j modulo H. The actual main-root definition is z_R=X+(rho+sigma)H. Hence X=2^R modulo H, and the two positive representatives lie below a<H. Therefore **X=2^R** exactly.

This is the proof in `complete75_asymmetric_scale_tradeoffs.md` §3, lines202–234, applied to p=R already obtained in the signed domain. We do not use §4's invocation of an old full positive zero. Since q divides X, q=2^t for an integer t>=4. The repunit equation and B=2^d imply d|t, using gcd(2^d−1,2^t−1)=2^gcd(d,t)−1. Thus q=B^N and t=dN, N>=1. Also R>3q>3t, so q³ divides X. All of these conclusions precede recovery of the binary masks.

## 3. Exact half-binomial Y and the population threshold need only odd R

For completeness the upper ratio is established here rather than importing the full positive kernel theorem. The same elementary estimates give

    c/k0 <= xi*(1+2/a)^(2r).

Now a>X^(r+1)/3 implies a>8r, so 4r/a<1/2. The elementary bound (1+u)^n<1/(1−nu), for u>0 and nu<1, gives

    (1+2/a)^(2r)<1+8r/a,
    0<c/k−xi/2<4r*xi/a.

Since X=2^(2r+1), one has 2r/X<=1/4 and

    (1+1/X)^(2r)<4/3,
    xi/a<3*(1+1/X)^(2r)/(X+1)<4/(X+1).

Therefore

    0<c/k−xi/2<16r/(X+1)<1/2.

The last bound holds for r>=24. Expand the rational number xi exactly as

    xi=M+theta,
    M=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j,
    theta=sum_(j=1)^r binom(2r,r−j)/X^j.

Here 0<theta<1/4: the sum of the lower-half coefficients is less than 2^(2r−1), while X=2^(2r+1). The integer M is even, because its central binomial coefficient is even and X is even. Thus

    M/2<c/k<M/2+1/8+1/2<M/2+1.

Together with Y<c/k<Y+1, this forces **Y=M/2**. No assumption that r is odd appears in the calculation. This is precisely the extraction argument of `pell_kernel_half_binomial42.md` §5, lines171–220, with its estimates explicitly justified at the asymmetric scale.

The exact central-binomial valuation is v2(binom(2r,r))=pc(r)<R; every other summand of M is divisible by 2^R. Hence

    v2(Y)=pc(r)−1.

Since q³ divides Y, pc(r)>=3t+1. As R=2r+1,

    **pc(R)=pc(r)+1>=3t+2=3dN+2.**

This uses the valuation calculation in half-binomial42 §6, lines224–231. Its subsequent positive converse, with its separate auxiliary parity requirement, is not invoked.

## 4. Actual compiler masks force R=3 modulo4

Define the integer words

    S_word=(Z−1)+qF,
    TC=MC*J+1, TF=MF_native*J−1,
    T_word=TC+q*TF.

The actual source and the repunit equation give the exact equality

    R=(q²−S_word)(q²−1)+T_word.

The accepted untyped bound F+Z<q with F,Z>0 already gives 1<=S_word<q². Because q=B^N, repeated-cell multiplication has no carries, 0<T_word<q²−1, and

    pc(T_word)=dN+2.

The MC increment increases population by one since MC is even; the MF_native decrement increases population by one because it has exactly two trailing zero bits. The inverse-population lemma in `complete75_half_binomial_compiler.md` §2, lines90–107, now gives

    pc(R)<=2dN+pc(T_word)=3dN+2,

with equality exactly when S_word AND T_word=0. The threshold from §3 forces equality, hence

    (Z−1) AND (MC*J+1)=0,
    F AND (MF_native*J−1)=0.

This lemma is purely a binary-word identity; it uses no auxiliary sign or decoded computation. Its excluded S_word=q² boundary is already absent here, but even under a weaker nonstrict bound the population threshold excludes it.

Since B and q are divisible by4, J=1 mod4. Thus MC*J+1=3 mod4, and the first AND constraint forces Z−1=0 mod4. Reducing the literal source identity

    R=(q(q−F)−Z)(q²−1)+(MC+q*MF_source)*J

modulo4 gives R=Z+MC*J=1+2=3 mod4. This is exactly the last implication in `FIXED_RAW_UNIVERSAL_75_PROOF.md` §3, lines203–215. It has now been obtained without any positive auxiliary quotient or root.

## 5. Both auxiliary congruences restore V>0 and T>0

Keep e=sign(V), which is nonzero because the auxiliary unit with y>0 excludes V=0. From the signed-T proof,

    |S*V|=chi_S(ell), y=psi_S(ell), ell=2v+1,
    V=e*C_v(S²),
    C_v(0)=(−1)^v*ell,
    C_v(−Delta)=(−1)^v*psi_A0(ell).

The literal identities give V=−c mod f and V=−R mod c, while S²=−Delta mod f and c|S. Squaring the f-congruence gives

    chi_A0(2ell)=chi_A0(2R) mod f, f=chi_A0(m).

Here 0<2R<m. The **plus-sign** step-down in `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` §2 gives 2ell=±2R mod4m, hence

    ell=epsilon*R+2m*z, epsilon in {−1,1}, z an integer.

For clarity, this stronger step-down follows by reducing the chi recurrence modulo f using chi_A0(2m)=−1 and psi_A0(2m)=0. Negative representatives cannot equal chi_A0(2R): for indices j<m, 2chi_A0(m−1)<chi_A0(m), so the sum of the two positive representatives is below f. Positive representatives force equality of their indices. This yields the modulus4m, not merely2m.

Writing r=(R−1)/2, one has

    (−1)^v*epsilon=(−1)^(r+m*z),
    psi_A0(ell)=epsilon*(−1)^z*c mod f,
    ell=epsilon*R mod c.

These hold for both epsilon signs; when epsilon=−1 the extra minus in epsilon cancels the shift from v=−r−1+m*z. Substitution into the **two unsquared** source congruences gives

    e*(−1)^(r+m*z)*R=−R mod c,
    e*(−1)^(r+(m+1)*z)*c=−c mod f.

Since c>2R and f>2c, both signs must equal −1 as ordinary integers. Dividing the sign equalities forces z even, regardless of the parity of m. Consequently

    e*(−1)^r=−1.

The f-congruence alone would leave a parity twist when m is even; the c-congruence is essential. This is the signed version of fixed-minus parity §§3–4, with its actual hypotheses supplied above. Section4 proved R=3 mod4, so r is odd and e=+1. Therefore V>0. Finally the literal source equality

    c*T*f=V+c+R*f²>0

and c,f>0 force **T>0**.

Every supplied coordinate is now in the original positive domain, unchanged. Thus the existing complete84 positive-zero theorem applies to this very tuple. No new auxiliary completion, off-zero positive map or sign-insensitive parent invocation is needed.

## 6. Input index and outer decoding: separate audit of possible dependencies

The accepted signed-T proof §4 already classifies the positive input root and proves j<R without using T>0, V>0, R mod4, X=2^R or canonical input j=u. Let u=2d*x+b and kappa=u+delta*Delta=psi_A0(j). It also gives 0<u<2q<R<a<A0.

The Pell recurrence modulo Delta gives psi_A0(j)=j*A0^(j−1) mod Delta. For 0<j<R<A0−2 the representatives are j when j is odd and j*A0 when j is even; both lie strictly below Delta. Since u<A0, an even j is impossible and an odd j forces **j=u**. This identifies the actual odd input index without using R=3 mod4.

The same projection recurrence as §2 gives W=2^u mod H. Initially W may be signed, but |W|<q and, after §2, 0<2^u<X<a. Thus |W−2^u|<q+a<H, forcing **W=2^u>0**. Hence W=2^b*B^(2x), and W<q=B^N gives 2x<N. This checks the input bridge without assuming positivity of W beforehand.

The remaining native-word proof consumes precisely these decoded powers, the two masks, the source transport equality and the fixed coefficient bounds. Its steps do not inspect T or V: the low mask places Start and End; the high mask and raw coefficient bounds identify the convolutions; clean bands and anchor differences force a whole-cell shift; retained overlap and occupancy constraints recover the accepted doubled input. These interfaces are spelled out in `complete75_half_binomial_compiler.md` §§3–5 and `FIXED_RAW_UNIVERSAL_75_PROOF.md` §§4–5. For the stated theorem we do not re-certify that entire historical compiler: §5 has already restored the original full positive tuple, so its accepted ordinary-input theorem is applicable without a new domain assumption.

## 7. Where positivity and parity actually enter; scope

* The normalized85 mathematical review uses T>0 explicitly at line103 to obtain V>−Rf²−c and exclude the negative auxiliary root. Its lines105 and144 then use the resulting V>0 to restore o,j>0 and classify SV as the positive Pell root. Its line170 invokes the whole positive parent only after those signs have been established. The signed-T proof replaces these steps by absolute-root classification and direct normalized rank; this note does not reuse their positive conclusions early.
* Power recovery, exact half-binomial extraction, its valuation and the input-index congruence do **not** require R=3 mod4. They require the odd R and index relations already available in the signed domain.
* The complete compiler's mask contract itself forces R=3 mod4 after population recovery. Thus this parity is a soundness consequence independently of auxiliary positivity. It is also needed by the historical canonical positive auxiliary **completeness** construction to obtain its two fixed-minus congruences; that converse is not a premise of §§2–5 here.
* Both auxiliary congruences then restore T>0 on the original tuple. This closes the signed-T soundness gap on valid compiler slices; it does not establish that arbitrary local strong/auxiliary tuples have positive T.
* As an immediate source-level consequence, if only f is instead allowed signed while T remains positive and every other supplied port stays positive, a negative f could be changed to −f while simultaneously replacing T by −T. Every computed source value is unchanged because the actual f consumers are f² and Tf. This would be a positive-f, negative-T zero, now excluded. At f=0 the normalized strong factor cannot be a unit. Thus signed-f zeros in this otherwise positive domain also have f>0. This is a domain observation, not a paid f-elimination compiler or a claim about the separate resultant candidate.

The intended review boundary is the extension proved above, conditional on the pinned accepted signed-T and positive-complete84 results and the explicit elementary ratio/population/parity lemmas. There is no new executable source, large Pell fixture, operation saving, formal Lean proof or unrestricted signed-zero theorem in this packet.

## Frozen provenance

The actual84 JSON SHA256 is `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. Its complete84 rows were read inertly; fresh standard-library data checks matched the63 literal rows listed in the provenance JSON and confirmed every direct f/T consumer. These checks execute no saved arithmetic array.

The exact source/proof manifest is `complete84_signed_quotient_soundness_scout.json`, SHA256 `0e31841fce2a8db87c930c8f5fcfeeab3e3761547897c218d2c964e1dab906cf`. It pins all11 proof files and gives inclusive read spans with hashes; unread portions are not claimed reviewed. The principal dependency pins are:

- `complete84_signed_quotient_absorption.md`: `79800010986c07674fb681a93e02f624ee7bc6e5d39b99a1e77daf5021fa77c9`.
- `review_complete85_auxiliary_bezout_math.md`: `77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d`.
- `complete75_asymmetric_scale_tradeoffs.md`: `3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2`.
- `pell_kernel_half_binomial42.md`: `0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992`.
- `complete75_half_binomial_compiler.md`: `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.
- `FIXED_RAW_UNIVERSAL_75_PROOF.md`: `e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d`.
- `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md`: `47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b`.
