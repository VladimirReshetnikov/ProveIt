# Independent ordinary proof review: eleven-integer square-root saturation

## Verdict

ACCEPT all six equations, relative to the explicitly retained ordinary source34/native/compiler/refutation calibration. No fatal error or unclosed mathematical gap was found in the new reduction. In particular, the free-scale degree-352 equation is not relying on the invalid early assumption gcd(H,q)=1.

Latest reviewed live operation counts and exact degrees:

| Equation | Operations | Degree |
|---|---:|---:|
| free_main_saturated11_none | 127 | 376 |
| free_main_saturated11_simple | 131 | 364 |
| free_main_saturated11_sharp | 132 | 352 |
| main_saturated11_none | 123 | 428 |
| main_saturated11_simple | 127 | 412 |
| main_saturated11_sharp | 128 | 396 |

All variables range over unrestricted integers. Intermediate registers and six fixed coefficient ports are not additional unknowns. This is an ordinary mathematical equivalence with the calibrated finite-refutation predicate, not a proof of consistency, global optimum, or new complete proof-assistant endpoint.

## Inspected scope

Read the whole new PROOF.md, the concurrent free-scale proof, the complete supported-modulus interpolation argument in POWERED_SATURATION_PARENT.md Section5, and the nonodd rank/fresh Q41 restoration in centered11-proof.md Sections5.2–5.4. Checked the exact arithmetic hypotheses against the old interfaces rather than assuming a syntactic resemblance suffices.

A separately written `independent_audit.py` checks every literal register against independently transcribed complete formulas by canonical free-expression normalization; all six output polynomials match. It imports only this review's own generic normalizer, standard libraries, and SymPy, not any producer or package checker. Normal and optimized outputs agree. It also checks108 source-file pins, all six raw numeral hashes and bit lengths, all live gates and inputs, free-ring norm/budget/center identities, exact sharp leading monomial multiplication, and18 graph corruptions. See AUDIT.json. These finite checks complement, not replace, the ordinary proof below. A separate finite auditor also checked the package independently.

## 1. Unconditional and zero-coordinate bootstrap

For every integer assignment the affine restrictions give q even and nonzero, X divisible by8 and congruent to2 modulo3, |X|≥4|q|. If Y=0 then A=2 and Delta=3; otherwise |a|≥|X|−1, so |A|≥2 and Delta>1. H=4a+3 is odd and nonzero. Therefore Q=Delta²A²Ub²Dm is divisible by4, delta=Q−1 is odd and never zero. Df is1 modulo4; Dt and P are odd.

The homogeneous intersective quintic Ac has no rational zero, so at S=0 the equation is delta²Ac⁴≠0. Thus any zero has r,s nonzero. Dm,Df are positive. If c=0, Q=0 and Da=1. If c≠0, |U|≥2c², Df>|c|+1, and the integer-distance estimate for V makes Da>0. This argument does not accidentally invoke c≠0 while treating the weak-scale branch.

A vanishing conjugate factor cannot have one isolated imaginary root, so P>0. Its oddness already excludes zero. Consequently Dg>0 and Budget≥2. In the free-scale case the strengthened budget independently forces k,Y nonzero, B0>0, and |Y|>|q|³ before any CRT or rank argument. The centered strip then excludes c=0. In the weak case c=0 remains allowed until scale recovery, as the proof explicitly requires.

## 2. Sign separation and three coprime factors

After normalizing the factor and multiplying by delta, its radical terms are2sqrt(Dm Df Da) and delta sqrt(P). P and delta are odd. If the roots shared a nontrivial squarefree class, the first class coefficient would be even and the second odd, so they cannot cancel. If the classes differ, squarefree-radical independence applies. This argument remains valid if Dm has powers of2; no unproved oddness of Dm is used. Both radicands are therefore squares.

The coprimality reductions are exact:

- Modulo Dm, Df=1 and Da=1.
- Modulo Df, Q=−Delta, delta=−A², V=−c, Cy=−Dm, hence Da=A²Dm.
- A|U implies Df≡1 modulo A.

Thus Dm,Df,Da are pairwise coprime positive integers and each is a square. The separate gcd(Dt,Dg)=1 splits the guard product. This does not make the invalid general inference that factors of an arbitrary square product are separately squares.

With d²=Dm and I=Ud, the restored strong ordinate is integral, nonzero when c≠0, and still divisible by c². With T_old=dT, its strong and auxiliary identities are exactly the old ones. The adjacent-Pell denominator descent applies for c≠0. At c=0 the exceptional Q=0 case gives y=−1 directly, so carrier integrality also holds before the weak-scale exclusion. The extracted roots give S|Ac in both cases.

## 3. Early free-scale parity and genuine rank hypotheses

The valuation proof M⁵|Ac implies M|zc is valid: if v_p(zc)<v_p(M), zc⁵ has strictly lower valuation than each other homogeneous quintic term, even at p=3 or19. It yields only M|H(Y−q³) initially. The 2-primary part, together with odd H, supplies Y even. The proof correctly refrains from cancelling H at odd primes here.

Likewise H|Ac gives H|(MK)⁵, and the identity K=HXc−2Kq, with odd H, gives H|(q³Kq)⁵. The extra q^15 remains present.

The strengthened budget supplies |Y|>|q|³ and all old packing/centered-strip inequalities. Hence |XY|>3R+1. Main and first norms, c²|I, and the exact auxiliary residues are present. The nonodd rank theorem is the correct one: c²|I yields c|m for the strong index, not merely the weaker main-index divisibility. The proof does not replace it with an odd-multiplier theorem. These facts yield p=R, the first index (R+1)/2, and the signed growth estimates before using the main projection.

## 4. The enlarged fifth-power bound and late CRT

From the signed projector and H|(q³Kq)⁵, the correct divisibility is H|q^15 Pi⁵. The factor bounds give

|q|^15|Pi|⁵<2^(20t−10)x^25,
|H|>x^(t+1)/2^t.

The constant−10 is correct: the ordinary two-factor bound contributes20t+20, while |q|≤x/4 contributes−30. At x≥2^64 and t≥36 the exponent margin is43t−1526≥22. The stronger t bound is genuinely implied by R>|q|(|q|²−1)≥4080; it is not an unsupported new source restriction. Thus the whole divisible product has absolute value below |H| and vanishes.

The second factor of Pi is odd and nonzero, so sign(c)X=2^R. Only now q|X shows |q| is a power of2 and hence gcd(H,M)=1. The earlier scale congruence can finally be cancelled, restoring Y=(2v_old+1)q³. This resolves the precise obstruction in a naive free-Y substitution.

Orientation, the exact centered half-binomial strip, and fresh Q41 restoration then use the old theorem with its actual hypotheses. The explicit regeneration keeps the outer tuple and constructs odd I_star and rho_star afterward. It never claims the incoming I/c² was odd. The newly expanded restoration paragraph matches centered11-proof.md Section5.4, including both auxiliary quotient congruences and the old first-index row.

## 5. Completeness and fixed-pair supported interpolation

The canonical source gives the stronger B0 margin and Y>X=2^R; the packing bound makes X>4q³, so the new budget exceeds64. The guard Pell coefficient (3Budget−4)Dt is positive and2 modulo3, hence nonsquare. Squaring a positive Pell unit supplies g²=1+4(3Budget−4)Dt s² with s,g positive.

After fixing d,A,c,s, choose a single strong pair with4sAdc²|I. It satisfies the retained interpolation theorem's conditions, including an even strong index (one may choose an even matrix period; equivalently the even ordinate at even A has even index). Set r=I/(Adc²). Every prime dividing d s r divides this same I. The full supported-modulus theorem, not merely its lower-precision linear congruence, therefore applies modulo d s r.

The source theorem was inspected: its p-adic isometry proves the fixed-pair auxiliary coordinate is surjective modulo every prime power supported on I, followed by CRT. Thus prescribing T_old=d a0 modulo d s r is legitimate without changing the strong pair afterward. It makes T=T_old/d integral and T≡a0 modulo sr. The canonical carrier factorization gives Ac/S integral, and4I T_old=4U Dm T is exact. The proposed unrestricted integer n then makes a norm factor vanish. The choice order is noncircular.

## 6. Exact degree attainment

The sharp identity

lambda²−4Dm Df=Dm²Ub²−4Dm

was verified in the free polynomial ring. Substituting it into the complete inner bracket gives a unique degree176 term for free scale, namely S² Q Dm² Ub² V². Other contributions have degrees at most162; the outer correction has degree316<352. Thus there is a global degree352 upper bound, not a propagated maximum that ignores cancellation.

Independent multiplication of the actual complete leading forms gives

[j^124 w^64 v^64 s^4 r^24 c^68 T^4] P
=2^288 3^188 beta^124>0.

The exponents sum to352. The corresponding weak-scale coefficient is2^332 3^232 beta^168 at j^168 w^64 v^64 s^4 r^24 c^68 T^4, sum396. Hence both upper bounds are attained at the authentic fixed beta. The analogous simple/direct degree arguments follow from their stated exact center defect or unique dominant direct term and agree with the separate finite audit.

## Limitations

The new ordinary reduction and its explicit inherited interfaces are accepted. The full historical logical/compiler calibration has not been independently re-formalized here. The six enormous constants are fixed, authenticated numerals, and their storage complexity remains distinct from gate count or degree. Any later graph, coefficient, or mathematical change requires a fresh receipt. Latest reviewed identities and PROOF.md hash are recorded in AUDIT.json.
