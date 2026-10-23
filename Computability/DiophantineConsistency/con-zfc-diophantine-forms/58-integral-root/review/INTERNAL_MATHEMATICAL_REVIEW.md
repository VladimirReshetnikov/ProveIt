# Internal AI review: fifteen-positive integral-root constructions

Review date: 2026-10-23. Reviewer: a separate AI subagent in the same ChatGPT research session. This is an internal mathematical review, not external peer review, an independent human certificate, or a proof-assistant build. The reviewer inspected the source proof dependencies and the new division-free builder, but did not independently reprove the complete inherited native compiler.

This review checks the new coordinate transformations, positivity margins, proof ordering, and exact degree claims. The pinned comparison snapshot is ProveIt commit `6d375f2d2deac0519e659bbce5b48087023c1430`.

## 1. The inherited six-equation source

The supplied domain is fifteen strictly positive integers. The old compiler uses

    q = beta*J_old + 1, C = q-F-alpha,
    X = w_old*q, Y = s_old*q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=E*kY,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q*MF)J_old.

Its exact ordinary-strong equations are

    tau_old^2 - ell(ell+k) = 1,
    (X+ac+gamma_old*H)^2 - Delta*c^2 = 1,
    k-hE-R = 1,
    (K0+w_old)C+q-F-z(q-1) = 1,
    I^2 = Delta(f^2-1),             I=i*c^2,
    U(V^2-y^2)+y^2 = 1,            U=Delta(f^2-1),
    V=c(T_old*f-1)-R*f^2.

The ordinary-strong theorem, not a claim of coordinatewise equivalence with normalized strong, is the relevant inherited soundness result. The complete canonical normalized witness transfers to this source by i_ordinary=Delta*i_normalized.

## 2. Monic-square divisibility principle

If d is a positive integer and d^2 divides z^2, then d divides z. This follows prime by prime from 2*v_p(z)>=2*v_p(d). Equivalently, a rational number whose square is an integer is itself an integer. This argument works for arbitrary composite d and does not presuppose a power of two.

This elementary fact forces divisibility of variables that used to be inserted syntactically as large monomials. It introduces no new unknown and no inequality certificate.

## 3. Free Y and degree 30

Use Y itself as a positive supplied variable, keep X=w*q, and replace the first Pell-root equation by

    [q^3(ell+r)+Y]^2 - q^6[ell(ell+k)+1] = 0.

The square principle implies q^3 divides Y. Hence s_old=Y/q^3>0 and tau_old=ell+r+s_old>0 recover the old first norm and old scale exactly.

For completeness, the old positive first norm gives, with delta=tau_old-ell,

    delta=(ell*k+1)/(tau_old+ell)>ell*k/(2ell+k)>k/3.

Here tau_old<ell+k and ell>k because k>=2 and E*Y>1. Canonical k=R+1+hXY>XY and X>=q>=16 give k/3>Y/q^3. Thus r=delta-s_old is positive.

The other equations are the old main norm, ordinary strong norm, auxiliary positive-gap norm y=V+e, and the grouped relation N1*N_k*N_t=1. Main norm N1 cannot equal -1 modulo4, because Delta is0 or3 modulo4; thus the grouped equation restores N1=1 and N_k*N_t=1. The old ordinary positive product theorem then applies. For its y coordinate use |V+e|: this cannot vanish when U=I^2>1 and the auxiliary norm is1.

The residual degrees are12 (first carrier),15 (grouped main/index/transport),15 (auxiliary gap), and10 (ordinary strong). Their sum of squares has exact degree30. The leading auxiliary contribution contains e^2 and cannot be cancelled by the other degree30 square.

## 4. Free X and degree 26

Use X itself as another positive supplied variable. Replace J_old by3j+1. Every authentic tuple used here has beta=2^d-1 with d odd, so beta=1 modulo3 and q=2 modulo3 on every new assignment.

The canonical compiler chooses B=2^d and an odd number N of cells, so J_old=1+B+...+B^(N-1)=1 modulo3. The large canonical choice also gives J_old>1. Therefore j=(J_old-1)/3>0 is a legitimate completeness restriction; merely setting J_old=3j would not be legitimate.

Keep the first carrier from Section3. Define

    D0=X+ac+gamma*H,
    M=q*D0+X*H,
    Tn=q*(K0*C+q-F-z*(q-1))+X*C.

Require

    M^2-q^2*(Delta*c^2+1)=0,
    (k-hE-R)*Tn-q=0.

First recover q^3|Y. Then H=4Y(X+1)+3 is3 moduloq, and gcd(q,H)=1 because q=2 modulo3. The main square equation implies q|M and hence q|XH. Therefore q|X. Set

    w_old=X/q>0,
    gamma_old=gamma+w_old>0.

Now M/q=X+ac+gamma_old*H is exactly the old main Pell root, and Tn=q*N_t. Thus the grouped equation implies N_k*N_t=1. All old positive equations/product conditions are restored as before.

For completeness gamma=gamma_old-w_old must be positive. One elementary bound uses the inherited canonical Y>X=2^R. Canonical k>XY gives c>XY^2. Since the main positive root D>(a+1)c,

    gamma_old>(c-X)/H>X(Y^2-1)/(4(X+1)Y+3).

For X,Y>=16, H<5XY, so gamma_old>(Y^2-1)/(5Y)>Y/6>X/6>X/q. This proves the needed margin. Alternatively the canonical first Pell index n=(R+1)/2>=3 gives k=2*psi_(2XY^2+1)(n)>32X^2Y^4 and proves the still stronger gamma_old>X.

The residual degrees are11 (first carrier),9 (main carrier),7 (grouped index/transport),13 (auxiliary gap), and10 (ordinary strong). The resulting sum of squares has exact degree26, uniquely from the auxiliary-gap square.

## 5. Index-ideal reduction and the recommended degree 24

Split the grouped index/transport equation into two residuals. Define

    Rhat=k-hXY-1,
    residual_index=Rhat-R,
    residual_transport=Tn-q.

Replace R by Rhat in the auxiliary expression only:

    V=f^2*(c*T-Rhat)-c,
    U=Delta*(f^2-1),
    residual_aux=V^2-(U-1)*e*(2V+e)-1,
    residual_strong=I^2-U.

The six residuals are the first carrier, main carrier, index, transport, auxiliary, and ordinary strong. Their sum of squares is one polynomial. At a zero every residual is exactly zero, so Rhat=R before the old arithmetic theorem is invoked. There is no common-unit sign argument left to check. The first and main carriers recover the old divisibilities as in Section4; transport is exactly N_t=1; index is exactly N_k=1.

The auxiliary identity

    V^2-(U-1)e(2V+e)
      = U[V^2-(V+e)^2]+(V+e)^2

is an integer-polynomial identity. With U=I^2>1, its value1 excludes V+e=0. Replacing that ordinate by its absolute value restores a positive old witness.

## 6. Squared-modulus auxiliary quotient: complete two-sided justification

For soundness use T_old=f*T. Then, exactly and before any equation is assumed,

    c(T_old*f-1)-R*f^2 = f^2(c*T-R)-c.

For completeness use a canonical normalized-derived ordinary witness. It has

    I^2=Delta(f^2-1), c=psi_A(R), A=a+2,
    gcd(c,f)=1, f^2=1 modulo c, R=3 modulo4.

Let r0=(R-1)/2, and let Q_r0 satisfy chi_t(2r0+1)=t*Q_r0(t^2). The elementary polynomial identities are

    Q_r0(0)=(-1)^r0*(2r0+1),
    Q_r0(1-A^2)=(-1)^r0*psi_A(2r0+1).

Set Vstar=chi_I(R)/I and ystar=psi_I(R). Because r0 is odd and I^2=-Delta modulo f^2,

    Vstar=-c modulo f^2,
    Vstar=-R modulo c.

Hence T=(Vstar+c+R*f^2)/(c*f^2) is a positive integer. Its numerator is divisible by both coprime denominators c and f^2. Moreover Vstar>1 for R>=3,I>1. The Pell identity gives

    ystar^2-Vstar^2=(Vstar^2-1)/(I^2-1)>0,

so e=ystar-Vstar>0. Thus the modified quotient has complete canonical witnesses. This is an existence equivalence, not a claim that every historical T_old is divisible by f.

The native phase R=3mod4 and canonical gcd(c,f)=1 are inherited authentic-compiler facts; they are not asserted for arbitrary numerical choices of the coefficient ports.

## 7. Exact degree certificate for the 24-degree polynomial

Assign degree1 to each of the fifteen inputs and degree0 to the four fixed ports. The six residual degrees are

    first carrier11; main carrier9; index4; transport3;
    auxiliary12; ordinary strong10.

The degree12 leading form of the auxiliary residual is

    -2*X^2*Y^3*f^4*e*(k*T+h*X),   k=eta+zeta.

Every other residual has lower degree. Therefore the degree-24 leading form of the final sum of squares is

    4*X^4*Y^6*f^8*e^2*(k*T+h*X)^2.

In particular the monomial X^4 Y^6 f^8 e^2 eta^2 T^2 has coefficient4. This is a uniform exact-degree proof independent of the numerical fixed ports. It is not an interpolation or random-evaluation argument.

## 8. Recommendation and comparison scope

Recommend the 24-degree six-residual sum of squares as the clearest low-degree 15-positive-variable form. The 26-degree five-residual companion may offer a slightly cheaper arithmetic evaluation. The 30-degree construction is a simpler first step that does not need the J congruence restriction.

The reviewed wave7 packets include15-positive degree44 circuits (75/76operations) and the66-operation degree157 equation. The proposed constructions improve degree at this specific variable/domain point, not variable count or the absolute operation record. The16-variable seven-equation degree-24 system is a different comparison. No claim of a global minimum follows.

This audit does not authenticate the final implementation ledger or materialized coefficient bytes; those need the release's deterministic circuit and coefficient checks. It establishes the new universal coordinate maps, positivity margins, proof ordering, and exact-degree argument.

## 9. Literal implementation inspected

The review also inspected `code/build.py` and the `p15_degree24` construction emitted by it. The supplied list contains fifteen variables; all other names are polynomial registers. The implementation uses `u` for the positive auxiliary gap denoted `e` above. It evaluates the auxiliary residual as

    (V+u)^2-U*u*(2V+u)-1,

which is exactly the identity reviewed in Section 5. The first and main cleared norms, the separate index and transport residuals, and the ordinary strong residual match the reviewed formulas. The alternative degree-certificate circuit expands the cancellations algebraically; it does not change the polynomial.

As a finite transcription diagnostic, an independently written direct evaluator of the displayed formulas was compared with the emitted circuits at 270 signed assignments across the three degrees and three prime moduli. All outputs matched. The corresponding cancellation-expanded degree-certificate circuits also matched at all 270 assignments. These are polynomial transcription checks, not semantic checks of the compiler.

The review did not authenticate the final coefficient payloads, independently regenerate the source compiler, or validate the final archive hash. Such finite release checks remain distinct from this mathematical review. The review found no unresolved gap in the new fifteen-positive reduction, conditional on the explicitly inherited mathematical compiler and K215 calibration theorems.

## 10. Twelve-positive companion: separate internal review

The reviewer read `twelve/P12_PROOF.md`, its division-free builder and checker,
and the preserved package44 inner-recovery proof and package52 lean-carrier
proof, including the explicit twelve-positive companion in Section 7a.
The following checks address the additional risks of the degree-629 form.

### No circular use of the old Y scale

Before recovering q^2|s, the new definitions are X=wq and Y=sq, so only
X,Y>=q>=16 and E>=q^2 are available. The unit equations still give
k=hE+R+epsilon>R and c>RY. The inherited outer coefficient estimates
3q<R<q^4-2 depend on the authentic transport unit and complete coefficient
tuple; they do not require Y=s_old*q^3.

The modified bound is valid under these weaker hypotheses:

    b+cf < (4R E^2+2E+1) I^2 < (4R+1)E^2 I^2,
    d0 > (1/2)E^4 I^2,
    (b+cf)/d0 < (8R+2)/E^2 < 9R/E^2.

The exact identity (Ig)^2-(cf)^2=I^2-c^2 gives

    Ig-cf > ic/(8E).

As c>RY and i>=1, icE>RXY^2>72R. Consequently
Ig-cf>(b+cf)/d0. This is precisely the inequality needed for the coherent
auxiliary-root estimate; the former assumptions E>R and Ig-cf>1 are not
used prematurely.

The negative-main-root carrier value is

    b+ITg+(t+s/q^2)+ell+(b0+g)/H.

Here t+s/q^2>0, tau<ell+k, and (b0+g)/H>c/3>k. It therefore exceeds
all coherent inner-root bounds, including those for complex auxiliary roots.
Actual conjugation of the one quadratic extension generated by sqrt(G)
forces the main root g to be rational and hence integral. This argument does
not suppose independent sign changes remain field automorphisms after
numerical specialization.

### Inner recovery and exact inherited map

The condition 1<A<sqrt(Q) holds already for Y>=16. It suffices for the
package44 exceptional-root exclusions: neither x nor its denominator C(x)
can vanish. Their rational formulas recover integer f' and tau'. The
rational Pell saturation lemma, with m=Delta*I and integer V=v*f'-b,
then proves y integral and therefore x integral.

The carrier equality reduced modulo q^2 yields q^2|H*s. Since
H=4sq(X+1)+3 and q=2 modulo 3, gcd(q,H)=1. Hence q^2|s.
Set s_old=s/q^2>0. The original scale Y=s_old*q^3 is now restored.

A particularly short exact bridge finishes soundness. With

t_old=t+s_old>0, the invariant norm identity is

    N_new=q^32*N_lean(t_old).

It follows directly that N_lean(t_old)=0. All retained coordinates and
units are unchanged. Thus the entire old twelve-positive product equation
is satisfied, and package52 Section 7a applies literally. This exact map
avoids any need to enlarge the signed-quotient theorem inherited there.
The longer signed-normalized reconstruction in the new proof reaches the
same conclusion, provided its positive/signed domains remain as stated.

For completeness, canonical old witnesses have

    t_new >= gamma+T(Ig-cf)+(tau-ell)-s_old,
    tau-ell>k/3>XY/3>Y/q^3=s_old.

Thus t_new is positive. The affine restriction J_old=3J+1 is compatible
with the canonical odd number of native cells and odd bit width d.
No assumption that arbitrary cofinal padding preserves a new congruence
is being made.

### Exact degree checked beyond finite sampling

For the unscaled lean norm with Y=sq, the relevant leading degrees are
H:4, ell:7, Q:30, b:26, and V0=I0*T*ell0:15. Write a formal factor as

    2*d0*H*b*Z + d0*Z^2 - H^2*b^2 - H^2*Q*D*v^2
        + H^2 + sf*2*H^2*Q*b*v*f,

where Z=W0-H*b-H*sa*tau-L0*sg*g. Four factors with sf unequal to sg have
degree79. For matched signs, write Z=-sg*H*I*T*g+Z1. The exact cancellation

    d0*I^2*G-Q*D*c^2=Q*(I^2-c^2)-I^2*G

bounds the pure quadratic remainder by degree54. Its cross terms have
degree at most60, and H^2*b^2 has degree60. All are below the smallest
surviving linear degree65. The four matched factors have degrees
71,71,67,65, with the nonzero final bracket 2t-k0-i*T*c0/E0. Thus the
unscaled norm has exact degree590 with the stated nonzero leading form.
This checks that changing the weights did not invalidate the inherited
ordering of lower terms.

The exact factor scaling contributes q^32. The rational t shift s/q^2
has degree -1, so cannot alter the degree-one final bracket. Hence the
new norm has exact degree622 and the product has exact degree629 after
the degree5 index unit and degree2 transport unit. These are uniform
statements for every positive authentic beta, not generic-specialization
claims.

The reviewer ran `check_p12.py`: all 60 modular formal-factor products
matched the circuit, and three complete polynomial rays over primes
10007,10009,10037 had norm degree622 and product degree629. The literal
114-operation count matches the emitted circuit. Those diagnostics
corroborate transcription and lower bounds; the preceding symbolic
argument supplies the uniform upper bound. They do not verify the
unbounded compiler or certify ZFC consistency.

### Review conclusion

No new unresolved mathematical gap was found in the twelve-positive
transformation or its degree proof. Its main extra burden is the
inherited norm root-recovery theory, so the fifteen-positive degree24
sum of squares remains the clearest principal equation. The degree629
companion is a defensible additional tradeoff, with the same explicit
inherited compiler and calibration boundary. Neither construction is
claimed to be globally simplest, externally reviewed, or end-to-end
formalized in a proof assistant.

## 11. Main report review and corrected incumbent

The reviewer subsequently inspected `report/report.tex`, including the
principal six-residual formula, the inherited kernel statement, both
existence directions, the two fifteen-variable companions, the exact
leading forms and gate counts, the coefficient recipe, the domain
translations, and the proof-status language.

No discrepancy was found between the principal mathematical formula and
`code/build.py`. In particular, the old transport coordinate is consistently
the unshifted positive coordinate, the ordinary strong coordinate is
explicitly distinguished from its canonical normalized predecessor, and
the fresh auxiliary quotient is used only as an existential completeness
construction. The gamma positivity proof using n0>=3 is valid: it gives
k>32X^2Y^4, c>32X^2Y^5, and hence c-X>XH under the stated canonical
bounds. The report's principal coefficient-4 monomial
X^6Y^6f^8u^2h^2 is consistent with the degree-24 leading form. The degree-26
and degree-30 leading forms also match the reviewed circuits. The primary
90, 88, 79 operation counts agree with `certificates/BUILD.json`; the more
expensive cancellation-expanded certificates are not substituted into
those costs.

The explicit coefficient specification was compared term by term with
`coefficients/build_coefficients.py` and its binding: B=2^590069,
K0=DC+B*DR, the 41-bit aggregate selector code, every copy/anchor/dummy
position, both clause shifts, the 13 full padding fields and final 19-bit
field, the low-mask special subtraction, and the final MF_native+B-1
shift agree. The prime controller in the preserved native proof explicitly
permits independently large dimensions that are powers of 581197, and
therefore N=581197^n is odd. The same proof explicitly retains R=3 mod4.
Thus the report's canonical congruence promises refer to the actual bound
tuple, rather than to a different historical adapter.

The translations to fifteen nonnegative variables by x->1+x and to sixty
unrestricted integers by four-square positive expressions are correct.
Their exact degrees are respectively 24 and 48. The latter follows from
the injective monomial substitution in the nonzero top homogeneous form.
The report correctly distinguishes this explicit translation from a claim
about the unrestricted-integer variable frontier.

The review found one comparison omission: the first report draft used
source49's degree44/76-operation point as the best supplied comparison,
but source47's minimum-norm supplement has a valid degree44/75-operation
polynomial. This was reported and corrected in the abstract, comparison
table, discussion and cost deltas. The resulting comparisons are
44/75 -> 24/90, 26/88, and 30/79, with operation increases 15, 13, and 4.
The direct root-gap predecessor 44/76 remains identified separately.
A targeted recheck of source directories 46--53, their relevant prose,
and their fifteen-variable scalar JSON objects found no degree below 44
or degree-44 evaluator below 75 operations in that supplied snapshot.
The degree-24 system with sixteen variables was not miscounted as a
fifteen-variable single polynomial.

The report expressly retains the mathematical native-compiler dependency,
notes the inherited Lean/Rocq K215 endpoint without claiming to rerun it,
and declines a new end-to-end formal or external-review certificate.
This is an accurate statement of the review's scope. Final PDF layout,
bibliographic corrections, receipt-count synchronization after added
provenance, and archive hashes are release tasks outside this mathematical
review.
