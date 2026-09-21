# How this document was merged

This package is one article assembled from **nine separately delivered
manuscripts**, all written on 21 September 2026 as independent attempts at the
same subject: a theory of holomorphic functions over the field
`K = No[i]` of surcomplex numbers, built on Hahn-supported series.

Nine runs at one foundational question is a different situation from nine runs
at one theorem.  A theorem either comes out the same way or it does not.  A
*foundation* can come out nine slightly different ways that all look alike and
are not interchangeable, and that is what happened here.

## The ten sources

| id | archive | subtitle | pp |
|---|---|---|---:|
| 01 | `surcomplex_analysis (1).zip` | Hahn-Coherent Holomorphy, Zero Clusters, and Global Rigidity | 31 |
| 02 | `surcomplex_analysis (2).zip` | Local Power Series, Coherent Hahn Families, and Infinitesimal Zero Geometry | 35 |
| 03 | `surcomplex_analysis(1) (1).zip` | Hahn Summation, Analytic Germs, and a Residue Calculus | 30 |
| 04 | `surcomplex_analysis(1) (2).zip` | Hahn-Analytic Germs, Coherent Contours, and Infinitesimal Zero Clusters | 32 |
| 05 | `surcomplex_analysis(1).zip` | Surcomplex Analysis via Hahn-Supported Holomorphic Functions | 30 |
| 06 | `surcomplex_analysis(2) (1).zip` | Hahn-analytic germs, holomorphic profiles, and infinitesimal zero geometry | 33 |
| 07 | `surcomplex_analysis(2) (2).zip` | Infinitesimal Calculus, Hahn-Coherent Holomorphy, and Contour Theory | 37 |
| 08 | `surcomplex_analysis(2).zip` | Local calculus, coherent Hahn functions, and residue theory | 33 |
| 09 | `surcomplex_analysis.zip` | A Hahn-Supported Theory of Holomorphic Functions on No(i) | 28 |

All nine are preserved verbatim under `sources/`, and all nine verification
programs under `code/`; all nine were run and all nine pass.  Nothing was
discarded.  The deduplication is in the article.

## The six notions that are NOT equivalent

This is the important part of this merge.  Of the seventeen load-bearing
notions reconciled below, **six differ genuinely across the sources**, and in
each case a theorem proved under one version is false under another.  The
sources themselves supply the counterexamples.

### 'Hahn-supported holomorphic function' -- THREE inequivalent classes

**Status: not equivalent**

**The variants.** (a) LOCAL/GERM: a normally summable power series sum a_n h^n with ARBITRARY surcomplex coefficients, no growth condition, no ordinary domain. Called 'microholomorphic' (02), 'surcomplex analytic germ' (03), 'Hahn-analytic germ' (04), 'germ-analytic' (06), 'fine-analytic' (07), 'microanalytic' (09). (b) COHERENT: sum f_gamma(Z) t^gamma with each f_gamma ORDINARY holomorphic on ONE common connected ordinary domain U and well-ordered set support, realized on the halo U^#. Called 'Hahn-coherent section' (01), 'coherent Hahn-holomorphic family' (02), 'H_Gamma(U)' (03), 'coherent' (04), 'H(U)' (05, 09), 'holomorphic PROFILE' (06), 'Hahn-coherent' (07), 'coherent Hahn section / A(U)' (08). (c) CANONICAL CLASSICAL LIFT f^# of an ordinary holomorphic f -- the sub-class supported at exponent 0 only. Separately, 01 uses a FOURTH and strictly weaker notion, 'differentially holomorphic': a bare epsilon-delta difference-quotient condition over all positive surreal radii, with NO power-series requirement.

**Adopted.** All four, kept apart by name and symbol: germ-analytic (local), H(U) (coherent), f^# (lift), and differentiable (01's bare differential class). Objects (b) and (c) are written with the same superscript # because a lift IS a section supported at exponent zero; the local class gets no superscript. The inclusions are (c) proper subset of (b) proper subset of (a) restricted to a halo, and (a) proper subset of 01's differential class.

**What breaks if they are confused.** This is the single largest transfer hazard in the merge. Results proved in (b) do NOT hold in (a): the identity theorem, the maximum principle in global form, Liouville, uniqueness of primitives and the open mapping theorem all fail in (a), witnessed by the locally constant L and by 06's b(z) = 1 iff v(z) is an ordinal. Results proved in (c) do NOT hold in (b): the SHARP Schwarz and Schwarz-Pick inequalities are false for general coherent self-maps of the halo, witnessed by (1+t)z, which fixes zero, maps D^# into itself and has |F'(0)| = 1+t > 1. Results proved in (a) do NOT hold in (b): sum n! eps^n is a legitimate germ on m but is not the restriction of any element of H(U) on an ordinary neighborhood of zero with those derivatives, since its exponent-zero coefficient would need Taylor coefficients n!. 01's differential class supports ONLY the calculus rules (uniqueness of the derivative, sum/product/chain) and the counterexamples; no positive theorem about it is proved anywhere, and none may be imported. The one bridge that IS proved and must be imported explicitly is 01 Thm 5.2: for a coherent section, the coefficientwise derivative equals the fine epsilon-delta derivative -- without it, nothing proved with one derivative transfers to the other.

### Residue -- THREE inequivalent notions

**Status: not equivalent**

**The variants.** R1, the FORMAL residue: the coefficient of X^{-1} in K((X)) (finitely many negative powers), at any surcomplex centre. Defined identically in 01, 02, 03, 05, 06, 08, 09. R2, the CLUSTER / profile / coefficientwise residue at an ORDINARY centre: Res^H_a A = sum_s (Res_a a_s) t^s. In 01 (called 'cluster residue' and flagged as attached to an ordinary centre, not to a single surcomplex pole), 04 (Res^co), 06 (called 'profile residue'). R3, the sum of ACTUAL local residues at the actual surcomplex poles inside the monad a + m. In 02, 03, 04, 05, 07, 08. The hypothesis classes also differ: 01 allows any Hahn series whose coefficients are merely MEROMORPHIC on U, with poles free to vary with the exponent; 06 requires a common closed discrete pole set E; 04 requires one fixed FINITE pole set; 02, 03, 05, 07, 08 restrict to QUOTIENTS A/B of coherent families.

**Adopted.** All three, with distinct symbols: Res (formal, R1), Res^H_a (cluster at an ordinary centre, R2), and Res_b for the actual residue at a surcomplex point b (R3). The coefficientwise residue theorem is adopted in 01's maximal generality; the quotient case carries the two bridge theorems.

**What breaks if they are confused.** The most dangerous conflation available. R2 and R1 DISAGREE at the same point: for 1/(zeta - eps) with eps infinitesimal, Res^H_0 = 1 while the local meromorphic residue AT 0 is zero (06 states this flatly; the actual pole is at eps). A merge that writes 'Res_a' for 01's cluster residue and then imports 03's or 06's local statements produces a false theorem. Two bridge theorems repair this and must both be stated. BRIDGE 1 (04 Thm rescluster; also 02 Thm 11.3, 03 Thm residue): for a quotient of coherent families, R2 at an ordinary centre equals the FINITE sum R3 over the actual poles in that monad -- proved by preparation, division and finite partial fractions over the algebraically closed K, never by a limit. BRIDGE 2 (06, unique): R2 at a equals R1 at the exact point a precisely when pole orders are UNIFORMLY BOUNDED in the Hahn exponent, i.e. (z-a)^d f_gamma extends holomorphically for one finite d and all gamma. On 01's larger class M(U), R3 has no meaning at all -- there need be no actual pole, and infinitely many ordinary centres may contribute (the sum is still Hahn summable because each meromorphic coefficient has finitely many poles in the compact closure). So 03's and 02's 'finitely many poles, finite sum' conclusion must NOT be imported under 01's hypotheses.

### The Cauchy estimate: coefficientwise majorant versus pointwise surreal bound

**Status: not equivalent**

**The variants.** 01 Prop 11.1, 03 Prop 12.1, 02 eq. coeffCauchy, 09: estimates are COEFFICIENTWISE, via the majorant B_r(F) = sum_s (max|f_s|) t^s, justified by the Cauchy-Schwarz lemma that B^2 - |Z|^2 has all coefficients nonnegative. 01 adds that B_r(F) is not generally the least upper bound of |F| on a surreal circle and that its coefficientwise definition is part of the statement; 03 adds that the coefficientwise order is much stronger than the surreal order and that the majorant is not a norm; 02 warns the estimates 'must not be replaced without proof by an assertion that a single coarse surreal bound controls every coefficient uniformly.' 07 Thm ML proves something the other eight do not have: a POSITIVITY lemma for the coefficientwise integral, hence a genuine surcomplex ML inequality |int^H F dz| <= L*M from a pointwise surreal bound |F| <= M on the path, hence |D^n F(c)| <= n! M / R^n from a pointwise bound on an ordinary circle.

**Adopted.** Both, clearly separated. 07's positivity/ML theorem is adopted as the primary estimate because it bounds the surreal MODULUS and is what a Liouville argument actually needs; 01's coefficientwise majorant is retained as a second, differently-shaped tool.

**What breaks if they are confused.** A merge that reads 02's warning as a prohibition would delete the strongest estimate in the collection. The two statements are about different things and are both true: 02 forbids 'one surreal bound controls every COEFFICIENT' (false -- F = w(1+it) has pointwise bound 1+t^2 on the unit circle but majorant 1+t), while 07 asserts 'one surreal bound controls the surreal MODULUS of the derivative' (true, by the positivity lemma applied after rotating by alpha = conj(I)/|I|). I checked 02's own cited counterexample, F = eps*Z, against 07's theorem: on |z| = R the bound is eps*R, and 07's estimate gives |F'(0)| <= eps, which is exactly right. No conflict. The positivity lemma itself is the load-bearing step and must be imported with the ML inequality: pointwise nonnegativity of a common-support family forces its LEAST nonzero coefficient function to be nonnegative, and a continuous nonzero nonnegative function has positive integral.

### Boundedness in Liouville-type theorems -- three inequivalent hypotheses

**Status: not equivalent**

**The variants.** (a) a single SURREAL bound on the finite halo: 01 eq. automaticbound and 07 Prop autobounded both show this is VACUOUS, since every nonzero F in H(C) already satisfies |F^#| < t^{v_H(F)-1} there. (b) a single ORDINARY REAL bound: 09 Thm liouville characterizes it exactly -- |F^#(z)| <= M on the finite plane iff F = c + R with c complex and R of positive support, so the algebra of real-bounded macroscopically entire functions is exactly C (+) H_{>0}(C). (c) COEFFICIENTWISE bounds: 01 Prop 11.3, 02 Thm 12.3, 03 Thm 12.2, 06 Thm growth, 07 Thm coeffLiouville, 09 Cor -- each coefficient bounded by its own real constant forces constancy, and coefficientwise polynomial growth of degree d forces a degree-d polynomial. 07's version is a biconditional.

**Adopted.** All three, stated as a hierarchy in one place: (a) vacuous, (b) 09's exact characterization, (c) 07's biconditional growth theorem with (c)'s d = 0 case as the classical Liouville statement.

**What breaks if they are confused.** The three hypotheses are routinely conflated and give three different theorems. Importing (c)'s conclusion 'F is constant' under hypothesis (b) is false: F = tz is real-bounded by 1 on the whole finite plane and is nonconstant. Importing it under (a) is worse -- (a) holds for every F. 09's (b) is the only sharp statement of what a scalar bound buys, and it is the one that reconciles the others: tz = 0 + tz lies in C (+) H_{>0}(C), exactly as 09 predicts. Note also that 02 flags a second, distinct obstruction to unrestricted Liouville statements -- the locally constant L on all of K, as opposed to the coherent tz on the halo of the ordinary plane -- and that these live in different analytic classes on different domains.

### The identity theorem's hypothesis

**Status: not equivalent**

**The variants.** 01 Prop 5.3: F = 0 if it vanishes on one entire MONAD, or if its zeros have distinct standard parts accumulating at an interior point of U. 02 Thm 12.1(ii): F = 0 if F^# vanishes as a germ at even ONE point of U^#. 03 Thm 8.1: three sufficient conditions -- accumulating standard parts, all derivatives vanishing at ONE point, or vanishing on a nonempty FINE-OPEN subset.

**Adopted.** The union, stated as four equivalent conditions in one theorem.

**What breaks if they are confused.** 02's and 03's hypotheses are strictly weaker than 01's, hence their theorem is strictly stronger, and it is correct: the proof runs through preparation (F nonzero has FINITELY many zeros in D^#), which contradicts vanishing on any fine neighborhood, since such a neighborhood contains infinitely many points. 01's monad hypothesis is a special case. Adopting 01's weaker theorem would silently give up the strongest available version. Note that all three formulations keep the accumulation hypothesis on STANDARD PARTS in C -- none of them asserts, and none may assert, the existence of a nontrivial set-sized convergent sequence in the fine topology.

### The logarithm: principal branch on a cut plane versus a global fine-analytic branch

**Status: not equivalent**

**The variants.** 01 Thm 13.2: only local charts Log_lambda on multiplicative monads b(1+m), branch choices differing by 2 pi i Oz, explicitly with no global principal argument and no covering-space structure. 02 Thm 7.3: a PRINCIPAL logarithm on the cut plane K minus No_{<=0}, defined by log_No|z| + i Arg z with -pi < Arg z < pi, inverse to Exp on the strip. 04 Thm globallog, 06 Thm globallog, 07 Thm globallog: a GLOBAL fine-analytic logarithm on ALL of K^x, with the branch chosen from the leading complex coefficient (equivalently from the standard part of the unit direction), which is fine-locally constant.

**Adopted.** The global fine-analytic logarithm of 04/06/07 as the primary object; 02's principal Log recorded as a separate named branch on the cut plane.

**What breaks if they are confused.** These are DIFFERENT FUNCTIONS, not two presentations of one -- see the contradictions field for the explicit 2 pi i discrepancy. The global one is needed and cannot be replaced: 04's contour no-go theorem consumes it, and without the no-go the coefficientwise definition of the contour looks optional. Its defining property must travel with it: it is NOT a coherent primitive of 1/z on (C^x)^#, since the coherent fundamental theorem would then force the unit-circle integral to be 0 instead of 2 pi i. 06 puts the resolution well -- the monodromy obstruction survives in the coherent category and disappears in the more permissive local one.


## The remaining eleven notions

These agree across the sources once the wording is pinned; they are listed so
that a later reader can see the check was made rather than assumed.

- **Hahn / normal / strong summability -- the sole infinite operation** — *equivalent*.  Adopted: Hahn summable, with 'strongly summable' noted once as a synonym. Clause (ii) named explicitly as the finiteness clause and never dropped.
- **Convergence, and whether the fine topology supplies any** — *equivalent*.  Adopted: Fine topology; 02's uniform-separation form of the discreteness theorem.
- **Contour, and the integral along it** — *equivalent*.  Adopted: int^H, with the superscript kept as a permanent reminder that the operation is coefficientwise and is not a limit of Riemann sums.
- **'Coherent'** — *equivalent*.  Adopted: Coherent, meaning exactly: one ordinary holomorphic coefficient function per exponent, all on one common connected ordinary domain, with well-ordered set support. 02's disclaimer against sheaf-coherence is kept verbatim; 06's 'profile' is recorded once as a synonym and then dropped.
- **The support condition: well-ordered set in No, versus inside a fixed set-sized group Gamma** — *equivalent under stated extra hypotheses*.  Adopted: Well-ordered set support as the definition; K_Gamma introduced as a working device when a statement needs to locate objects inside a set-sized subfield, justified by 03 Prop 2.3.
- **The derivative operator** — *equivalent*.  Adopted: F' for the derivative of a coherent section or germ, D_z when the operator itself is the subject. 02's remark and its incompatibility proof are both kept.
- **The domain of the coherent theory: the halo, not a surcomplex ball** — *equivalent*.  Adopted: U^#. Both warnings kept once each, at the point of definition.
- **Preparation: local (one zero, small disk) versus global (whole Jordan domain)** — *equivalent under stated extra hypotheses*.  Adopted: The global Jordan-domain form as the theorem; the local disk form as its corollary.
- **Rouche's hypothesis: where the strict inequality lives** — *equivalent under stated extra hypotheses*.  Adopted: Three named forms: valuation Rouche (any perturbation of strictly larger family valuation, preserving counts fibre by fibre), ordinary-margin Rouche (strict inequality on the leading coefficient functions, preserving the total count), and 05's real-margin Rouche (surreal-valued hypothesis with a real q < 1).
- **Schwarz: lemma versus Schwarz-Pick, and the same-monad case** — *equivalent under stated extra hypotheses*.  Adopted: Schwarz-Pick in the 03/07/08 form, with the Schwarz lemma as its f(0) = 0 corollary, plus 07's stability corollary.
- **All-scale coherence, and what it is not a definition of** — *equivalent*.  Adopted: 07's formulation (fixed disk B(0,2), charts at zero, supports free to vary with the scale), since the converse direction is cleanest there.

## Resolved conflicts

### 1. The logarithm on K: two different functions both called 'the' logarithm

**In the sources.** 02 Thm 7.3 defines a PRINCIPAL logarithm on the cut plane K minus No_{<=0} by Log z = log_No|z| + i Arg z with -pi < Arg z < pi, inverse to Exp on the strip {-pi < y < pi}. 04 Thm globallog, 06 Thm globallog and 07 Thm globallog each define a GLOBAL fine-analytic logarithm on ALL of K^x, choosing the branch from the leading complex coefficient of z, equivalently from the standard part of its unit direction. 01 has neither, offering only local charts Log_lambda on multiplicative monads.

**Resolved.** Both are correct; they are NOT the same function, and they differ by exactly 2 pi i on an explicit set of points. I computed both at z = -1 - i*eps for infinitesimal eps > 0. 02's version: |z| is infinitesimally near 1 and Arg z is infinitesimally near -pi, so Log z is near -i*pi. 04/06/07's version: the standard part of the unit direction is -1, whose principal argument under the (-pi, pi] convention is +pi, and the infinitesimal correction is O(eps), so the value is near +i*pi. The discrepancy is 2 pi i on the lower half of the monad of every negative real. Both are legitimate branches; neither is wrong. The merged document adopts the GLOBAL one (04/06/07) as primary, for three reasons: its domain is all of K^x rather than K minus a class-sized ray; it is fine-locally analytic everywhere, because the branch is chosen by a fine-locally constant quantity, whereas 02's Arg is not fine-continuous on the monad of a negative real; and 04's contour no-go theorem, which justifies the entire coefficientwise contour apparatus, requires a global primitive of 1/z and cannot be run with 02's cut version. 02's Log is retained as a separately named principal branch with its 2 pi i relation to the global one stated. The property that must travel with either is that NEITHER is a coherent primitive of 1/z on the halo of C^x -- 07 gives the cleanest proof (a coherent primitive would force the unit-circle coefficientwise integral to be 0, but it is 2 pi i).

### 2. How strong a Cauchy estimate the coefficientwise integral supports

**In the sources.** 02 §9.2 states that its coefficientwise estimates 'must not be replaced without proof by an assertion that a single coarse surreal bound controls every coefficient uniformly in the ordinary complex variable' and cites a counterexample. 01 Prop 11.1 similarly insists the majorant B_r(F) is not the least upper bound of |F| on a surreal circle and that its coefficientwise definition is part of the statement; 03 Prop 12.1 adds that the majorant is not claimed to be a norm. 07 Thm ML nevertheless proves a Cauchy estimate FROM a single pointwise surreal bound: |D^n F(c)| <= n! M / R^n whenever |F| <= M on the ordinary circle.

**Resolved.** 07 is right and there is no actual conflict, but the two statements look like a direct clash and a merge could easily suppress the stronger one. They are about different quantities. 02 forbids inferring that one surreal bound controls every COEFFICIENT function; that is genuinely false, and I constructed a witness: F(w) = w(1 + it) on the unit circle has |F^#| = sqrt(1+t^2) = 1 + t^2/2 pointwise, so M = 1 + t^2 works, while the coefficientwise majorant is 1 + t > M. 07 asserts only that one surreal bound controls the surreal MODULUS of the derivative, which is a weaker conclusion and is provable. The proof is the positivity lemma: for a common-support family of continuous real coefficient functions that is pointwise nonnegative, the LEAST nonzero coefficient function must itself be pointwise nonnegative (otherwise the value would be negative where it is negative), and a continuous nonzero nonnegative function has positive integral; the surcomplex modulus statement then follows by rotating with alpha = conj(I)/|I|. I also checked 07's theorem against 02's own cited counterexample: for F = eps*Z on the circle |z| = R the bound is eps*R, and 07's estimate gives |F'(0)| <= eps, which is exact. The merged document keeps both -- 07's ML inequality as the primary estimate and the coefficientwise majorant as a separate tool -- and states in the text why 02's caution does not forbid 07's theorem.

### 3. The residue at an ordinary point: 1 or 0

**In the sources.** 01 computes Res^H_0 of 1/(zeta - eps), for infinitesimal eps, to be 1, calls it the cluster residue at zero, and says it 'correctly accounts for the actual pole at eps'. 06 states flatly of the same function that 'its local meromorphic residue at zero is zero'. 04 and 03 make the same observation as 06 in different words.

**Resolved.** Both are correct under their own definitions and the apparent contradiction is entirely one of naming, but it is the sharpest trap in the merge. 01's Res^H_a is a CLUSTER residue attached to an ordinary centre -- the Hahn sum of the ordinary residues of the coefficient functions -- and 01 flags this explicitly at the definition. 06's is the residue of the meromorphic germ at the exact point 0, and 1/(zeta - eps) is regular there, since on the ball |zeta| < |eps| it expands as -(1/eps) sum (zeta/eps)^n with no pole. Adopting a single symbol 'Res_a' for both would turn a correct statement into a false one. The merge uses Res^H_a and Res_b as distinct symbols and states the two bridge theorems that connect them: 04's residue-cluster theorem (the cluster residue at an ordinary centre equals the finite sum of actual residues in that monad, for quotients of coherent families) and 06's criterion (the cluster residue equals the local residue at the exact point precisely when pole orders are uniformly bounded across Hahn exponents).

### 4. How general the coefficientwise residue theorem is

**In the sources.** 01 Thm 9.5 requires only that each coefficient be meromorphic on the connected ordinary domain U, with poles free to vary with the exponent, and allows infinitely many ordinary centres to contribute. 06 requires a COMMON closed discrete pole set E for all coefficients. 04 requires the poles to lie in one fixed FINITE set.

**Resolved.** 01 is right and its hypotheses are strictly the weakest of the three; 04's and 06's extra conditions are unnecessary. I checked 01's proof and it is sound: each coefficient, being meromorphic on U, has finitely many poles in the compact closure of Omega, so only finitely many centres contribute at any fixed exponent; the union of all residue supports stays inside the fixed well-ordered support of A; hence the right-hand side is Hahn summable even when infinitely many centres contribute in total, and the ordinary residue theorem may be summed coefficientwise. The merge adopts 01's version. Importantly, this generality comes at a price that must be stated: on 01's class M(U) there need be no actual surcomplex pole at all, so the finite-sum-over-actual-poles conclusion of 02, 03, 05, 07 and 08 does NOT transfer to it. That conclusion is licensed only for quotients A/B of coherent families, which form a proper subclass of M(U).

### 5. Whether preparation is a local or a global theorem, and what it licenses

**In the sources.** 01 Thm 8.1, 03 Thm 9.1, 06 Thm weierstrass and 09 prepare at a SINGLE zero on a small ordinary disk. 02 Thm 10.1 and 08 Thm preparation prepare on a whole bounded Jordan domain at once, producing ONE monic polynomial of degree equal to the TOTAL zero count of the leading coefficient in that domain, via ordinary Hermite interpolation at all the zeros simultaneously.

**Resolved.** Not a disagreement about truth -- both forms are proved correctly -- but a real difference in strength that determines what else may be imported. The global form is strictly stronger and is REQUIRED by two results in the collection. 02 Thm 11.1's exact weighted argument principle, (1/2 pi i) int^H A * F'/F = sum over the whole cluster of A^#(xi_j) with no error term, is proved by writing F = U*W with a single W over the whole domain; there is no derivation of it from the local form, because that would require assembling local factorizations across distinct zeros without a common polynomial. The Newton-identity reconstruction of W from contour moments (02 Cor 11.2, 06 Thm moments) has the same dependency. The merge therefore states the global form as the theorem and the local disk form as its corollary, so that the argument principle and the moment reconstruction are licensed by what precedes them.

### 6. How weak the identity theorem's hypothesis can be

**In the sources.** 01 Prop 5.3 requires F to vanish on an entire MONAD (or to have zeros whose distinct standard parts accumulate in U). 02 Thm 12.1(ii) requires only that F^# vanish as a germ at ONE point of the halo. 03 Thm 8.1(iii) requires only vanishing on a nonempty fine-open subset, and 03 Thm 8.1(ii) only that all derivatives vanish at one point.

**Resolved.** 02 and 03 are right and 01's hypothesis is unnecessarily strong. The stronger versions are correct and I checked the mechanism: preparation gives a nonzero coherent section finitely many zeros in the halo of a bounded Jordan domain, whereas any fine neighborhood of a point contains infinitely many points, so a vanishing germ at even one point forces F = 0. 01's monad hypothesis is a special case of a vanishing germ. The merge states the four conditions together as one theorem. One clause is shared by all three and must not be weakened: the accumulation hypothesis is on STANDARD PARTS in C, and none of the manuscripts asserts, or may assert, the existence of a nontrivial set-sized convergent sequence in the fine topology -- the discreteness theorem forbids it.

### 7. Whether an arbitrary formal series is or is not representable by a coherent section

**In the sources.** 01 asserts that sum n! eps^n is a legitimate function on the infinitesimals but 'cannot be the restriction of a coherent section on an ordinary neighborhood of zero having those same derivatives'. 02 Thm 8.5 and 07 assert that EVERY formal series over K, including this one, becomes after a single monomial rescaling a coherent family on ALL of C whose coefficient functions are polynomials.

**Resolved.** Both are correct and the tension is only apparent, but it is severe enough on the page that the merged document must state the two adjacently with the reconciliation attached. 01's claim concerns the ORIGINAL chart: a coherent section on an ordinary neighborhood of zero whose derivatives at zero are n!*n! would need an exponent-zero coefficient function with Taylor coefficients n!, and no such holomorphic function exists. 02's and 07's claim concerns a RESCALED chart: after substituting z = rho*zeta with rho = t^lambda chosen by the block-separation lemma, the degree-n term lands in its own Hahn exponent band, so each Hahn coefficient is a finite sum and is therefore a polynomial in zeta. The rescaling changes which function is being represented. 07 states the limit of the positive result exactly: a germ has SOME sufficiently small coherent chart, but there is no implication that it has a chart of every larger radius -- which is precisely the content of the all-scale rigidity theorem.

### 8. Whether a Picard-type theorem is available

**In the sources.** 01 Thm 14.1 proves an exact value-distribution theorem for Exp(1/z): every nonzero surcomplex value is attained on a proper class of points in every ball of positive surreal radius about zero, and the singularity is neither removable nor a pole. 07 and 08 both explicitly decline to prove anything of the kind, 08 listing 'a general theory of essential singularities with a Picard theorem' among assertions deliberately not made, and 07 observing that for a twisted exponential E_alpha(1/z) the values depend on the phase convention -- E_0 and E_pi differ at z = -i/omega.

**Resolved.** No contradiction; the two are answering different questions, and both belong. 01's theorem is about ONE specified function and is correctly stated for the canonical Exp, not for the twisted family. I checked that this restriction is necessary rather than incidental: the construction places the solutions at z_q = 1/(lambda + 2 pi i q) for omnific q, which requires 2 pi i Oz to lie in the kernel, and for E_lambda with lambda not in 2 pi Z the kernel is strictly smaller, since E_lambda(iy) = e^{i*lambda*y_{-1}} differs from 1 for purely infinite y with nonzero omega-coefficient. 07's and 08's disclaimers concern a GENERAL classification of essential singularities for all analytic functions, which would be incompatible with the locally constant counterexamples. The merge keeps 01's theorem with its own scope note (an exact value-distribution theorem for a specified function, not a general Picard theorem) and adds 07's observation about the phase dependence of the twisted variants.

### 9. Where the strict inequality in Rouche's theorem may be placed

**In the sources.** 01 Thm 9.4(ii), 04 Cor rouche and 08 Thm Rouche place the strict inequality on the ORDINARY leading coefficient functions, |g_0| < |f_0| on the boundary. 05 Cor marginrouche places it on the SURCOMPLEX values, |G(a) - F(a)| <= q|F(a)|, but requires an ordinary REAL margin 0 <= q < 1.

**Resolved.** No manuscript states the false version, and both formulations are correct, but they are making the same point from opposite directions and the merge must not average them into something weaker than either. 05 supplies the reason the real margin is needed and it is the right one: a bare strict surreal inequality |G - F| < |F| does not reduce to a strict complex inequality after taking standard parts, because strictness can disappear in the reduction. 01 states the matching warning from the other side. The merge keeps three separately named forms -- valuation Rouche, ordinary-margin Rouche and 05's real-margin Rouche -- and preserves 03's further distinction, which is easy to lose: the valuation form preserves the zero count FIBRE BY FIBRE over each ordinary zero, while the ordinary-margin form generally preserves only the TOTAL count.

### 10. The kernel of the canonical exponential, written two ways

**In the sources.** 01 and 02 give ker Exp = 2 pi i Oz with Oz = J + Z the omnific integers. 04 gives ker E_0 = i(J + 2 pi Z).

**Resolved.** These are equal, and the discrepancy is only apparent -- but it is worth flagging because the two forms invite different and incompatible readings. 2 pi(J + Z) = 2 pi J + 2 pi Z, and J, the additive group of purely infinite surreals, is a real VECTOR SPACE, so 2 pi J = J and the expression equals J + 2 pi Z. Written as '2 pi i Oz' the kernel looks like a uniform scaling of a discrete group, which would suggest the purely infinite part also scales; it does not. The merge writes ker Exp = 2 pi i Oz = i(J + 2 pi Z) with the identity 2 pi J = J stated once at the point of definition.

### 11. Whether the coefficientwise residue theorem's class is closed enough to carry the actual-pole conclusion

**In the sources.** 01 develops the residue theory on M(U), Hahn series with arbitrary meromorphic coefficients on U. 02 §Cor 11.4 warns that 'arbitrary normally arranged collections of meromorphic coefficients with independently moving or accumulating poles are not being included without a common domain condition' and restricts its residue theorem to quotients of coherent families.

**Resolved.** Both are right about their own theorems, and the resolution is a containment I verified rather than a choice between them. Quotients of coherent families DO lie in M(U): if B = t^beta f_beta(1 + E) with f_beta not identically zero, then 1/B = t^{-beta} f_beta^{-1} sum (-E/f_beta)^n, and at each Hahn exponent the sum is finite by Neumann's lemma, so each coefficient of 1/B is a finite sum of meromorphic functions and hence meromorphic. So the quotient class is a proper subclass of M(U), and on it both theorems apply and agree -- which is exactly the content of the bridge theorem. What 02's warning correctly denies is the converse: an arbitrary element of M(U) need not be such a quotient, so its cluster residues need not be sums of residues at actual poles, and 01's theorem must not be read as producing actual poles. The merge states the containment explicitly so that each theorem's reach is visible.


## Notation

| concept | this document | in the sources |
|---|---|---|
| The surcomplex field | `K = No[i]` | K in 01, 02, 04, 05, 06, 08, 09; \SC in 03 and 07. Majority and clarity both favor K. NOTE: 01 warns that S must never denote the field, because S is its symbol for a support; the task brief's use of 'S' for the field is exactly the collision 01 is guarding against and is not adopted. |
| Well-ordered set support of a normal form or a family | `S, with supp(z) and supp(F) for the operators` | S throughout 01, 02, 03, 05, 06, 08, 09. Free once the field is written K. |
| Conway monomial scale | `t^gamma := omega^{-gamma}, t = omega^{-1}` | t^gamma in 01-05, 07-09; \tmon^gamma in 06. Universal agreement on meaning. The standing warning is kept: this is Conway's monomial map, not Gonshor exponentiation with base omega^{-1}, and t^{gamma+delta} = t^gamma t^delta is a convention, not a theorem about surreal exponentiation. |
| Valuation ring of finite elements, and its maximal ideal | `O for the valuation ring, m for the infinitesimals` | V (01), O_K (02), \OO (06), \fin (08), \Fin (09), O (03, 05, 07). CLASH RESOLVED: 01 and 02 also use O(U) for ordinary holomorphic functions on U, which collides with O for the valuation ring. The merge writes Hol(U) for ordinary holomorphic functions (as in 05 and 08) and reserves O for the valuation ring. |
| The halo / tube over an ordinary domain | `U^# = st^{-1}(U)` | U^mu (01), U^# (02, 03, 05, 06, 07, 09), halo(U) (08), D^# (04). The superscript # is the clear majority and reads well beside F^#. |
| Evaluation of a coherent section, and the canonical lift of an ordinary holomorphic function | `F^# for both` | ev(F) or plain F(z) (01), F^# (02, 03, 05, 07, 09), ev F (08), the 'lift' (06); the classical lift is tilde-f in 01 and f^# in 02, 03, 07, 09. Using one symbol is correct rather than merely convenient: a canonical lift IS a section supported at exponent zero, so f^# is the special case of F^# and the notation should say so. |
| The coherent algebra over an ordinary domain | `H(U), with H_{>0}(U) for positive-support elements and M(U) for meromorphic coefficients` | H(U) in 01, 02, 03, 05, 06, 07, 09; A(U) in 08; 04 uses the adjective 'coherent' without a symbol. M(U) is 01's notation for the meromorphic-coefficient class and has no competitor. |
| Valuation of a family (least exponent) and its leading coefficient FUNCTION | `v_H(F), with f_{v_H(F)}` | nu(F) (01, 08), v_H(F) (03, 07), vprof (06), 'least exponent' in prose (02, 05, 09). v_H is the clearest -- it names the object as a valuation and marks it as the Hahn-family one. 03's warning is attached at the definition: v_H and the leading coefficient FUNCTION are not the pointwise valuation and leading coefficient of a value. |
| Derivative | `F' for the derivative; D_z when the operator is the subject` | F' (01, 03, 05, 09), D or DF (02, 07, 08). CLASH RESOLVED: in 02 the letter D denotes both the derivative operator and the bounded Jordan domain. The merge writes D only for the ordinary unit disk, Omega for the Jordan domain (01's choice), and reserves D_z for the operator. |
| Neumann monoid generated by a positive well-ordered set | `<S> (angle brackets)` | E^* (01), B^* (02), M(S) (03, 05, 06), <T> (04, 08). M(S) is rejected because M is already the meromorphic class M(U); angle brackets are unambiguous. |
| Coefficientwise contour integral | `int^H and oint^H` | int^H / hint (01, 03, 07), int^co (04), unadorned integral with an attached definition (02, 05, 08, 09). The superscript is kept permanently, since the whole point is that this operation is not an ordinary or Riemann integral. |
| The three residues | `Res (formal, in K((X))); Res^H_a (cluster, at an ORDINARY centre a); Res_b (actual local residue at a surcomplex point b)` | Formal: Res_{X=0} (01, 02, 03, 05, 06, 08, 09). Cluster: Res_a^H (01), Res^co_a (04), Res^H_a 'profile residue' (06). Actual: Res_{z=b} (02, 03, 04, 05, 07, 08). Three distinct symbols are mandatory -- see the definitionReconciliation entry; the same symbol for the first and second produces a false theorem at 1/(zeta - eps). |
| Standard part and the finite decomposition | `st, with z = a + eps for a = st(z) in C and eps in m` | st in all nine. No conflict. |
| The canonical exponential and its twists | `Exp for the canonical one; E_lambda for the real-parameter twisted family, with E_0 = Exp` | Exp_0 / Exp_c (01), Exp / E_a (02), E_lambda (04), Exp_S (05), E / E_alpha (06, 07). Indexing by a real parameter with E_0 canonical is the clearest, and it makes the value statement E_lambda(i omega) = e^{i lambda} read directly. |
| Omnific integers and purely infinite surreals | `Oz = J + Z, J the additive real vector space of purely infinite surreals` | Oz, J (01), Oz = No_PI + Z (02), J (04), No_PI (02, 06). The kernel is written ker Exp = 2 pi i Oz with the equality 2 pi i Oz = i(J + 2 pi Z) stated explicitly, since J is a real vector space and the first form otherwise invites the false reading that the whole kernel scales by 2 pi. |
| The ordinary disk, the Jordan domain, and the neighborhood of its closure | `D for the ordinary unit disk; Omega for a bounded Jordan domain with piecewise-C^1 boundary; Gamma = boundary(Omega); V for an ordinary neighborhood of the closure of Omega` | D and Omega both used for the Jordan domain across 02, 03, 04, 05, 07, 08; D also the unit disk in 01, 02, 09. Fixing D = unit disk and Omega = Jordan domain removes the collision noted under 'Derivative'. |
| Hermite division data used in preparation | `P_0 (monic complex zero polynomial), u_0 = f_0/P_0, T (remainder of degree < d), Q_0 (quotient), d = deg P_0` | P_0, u_0, R_0, Q_0, d (02); P_0, u_0, T, Q_0, N (08); T_m, R_m for the single-zero Taylor operators (01). The merge uses 08's T for the remainder to avoid clashing with R for a remainder polynomial elsewhere, and records 01's T_m, R_m as the single-zero special case. |
| The local germ class and the coherent class, as adjectives | `germ-analytic (local) and coherent (H(U)); 'differentiable' reserved for 01's bare epsilon-delta class` | microholomorphic (02), analytic germ (03), Hahn-analytic (04), germ-analytic (06), fine-analytic (07), microanalytic (09), differentially holomorphic (01). Six names for one class is the worst duplication in the collection. 01's term is NOT a synonym and must not be absorbed into the list. |
| The topology | `fine topology` | full surreal topology (01), fine topology (02-09 predominantly), neighborhood topology (02), all-radii topology (09). |

## Bibliography

The nine reference lists hold 94 entries naming 44 distinct works.  The most
cited are Gonshor and Alling on the surreals, Neumann on ordered division
rings (the ancestor of the Hahn-series machinery used throughout),
Rubinstein-Salzedo and Swaminathan on analysis over the surreals, and
Mueller and Strohmaier on Hahn-meromorphic functions.  The merged
bibliography lists each work once and records which of the nine cited it.

