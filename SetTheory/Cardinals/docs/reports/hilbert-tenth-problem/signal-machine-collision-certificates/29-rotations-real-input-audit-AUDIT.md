# Independent audit of the five signal real input obstruction

Date: 4 October 2026

## Verdict

**PASS for the companion's stated mathematical conclusions, conditional only on its explicitly imported exact physical chamber and return characterization.** The all-real positive-gap validity set is properly G_delta, the proposed finite existential mixed integer/real polynomial certificates cannot define it, and the set is properly co-semidecidable in the specified ordinary BSS model. The transfer to every fixed member of the audited rational-rotation family is valid, including members whose critical circle has zero-gap contact points.

No substantive mathematical correction is required. One optional wording refinement is identified in Section 9. This is an independent conventional mathematical review, not a proof-assistant certificate, a new physical rule-table audit, or a novelty claim.

## 1 Scope and binding

The reviewed companion is bound to these SHA-256 values:

- `five-signal-real-input-obstruction-20261004/PROOF.md`: `58e75fba06c017fb8e2e59925b03a3b96e389e268ea257db79d1f5201b3a7b1d`
- `five-signal-real-input-obstruction-20261004/SOURCE_NOTES.md`: `0858029ba8887be502039f2f16424ce39f29c2b0fe0ba22bdcbca236edf8cb0f`
- `five-signal-rotation-family59-20261004/PROOF.md`: `14c3d694d9e0c21f3ad3b125c0d1f2bbf47793e1283c9314aa3855ef60c89fc5`

`INPUT_SHA256SUMS.before` records the absolute paths and hashes of these three files and the four further frozen dependencies actually consulted. Every value stated in the companion's source notes matches the corresponding local file. The prior physical audits' verdicts are bound to the same Report 57 and Report 59 proof bytes used here. The companion's own two-entry manifest also matches its two files.

I independently checked the topology, projection argument, BSS finite-path proof, rational complement semidecision, family transfer, and the compatibility of the real-input result with encoded rational decision. I checked the companion's concrete chamber-test formulas against the upstream mathematical presentation and expanded guard list. The underlying full physical construction and the Pell-based integer certificates remain imported dependencies; this review does not claim to have rechecked every collision rule or every arithmetic-certificate module.

No upstream or author program was executed. No physical simulator, event scheduler, saved collision schedule, proof assistant, or mathematical test script was run. Local operations were read/list/hash operations and creation of this new review directory. Primary BSS research papers and an author-hosted real quantifier-elimination statement were inspected through their published texts. The sources were preserved; final hash verification is recorded separately.

## 2 Consistency of the imported concrete geometry

Write d=g1+g2+g3, x=g1, y=g1+g2, xi=x-d/3, and eta=y-2d/3. Directly from the displayed gap matrix,

    d' = d/2,
    x' = (9x-12y+10d)/30,
    y' = (12x+9y)/30.

Consequently

    xi' = 3xi/10-2eta/5,
    eta' = 2xi/5+3eta/10.

Thus the claimed centered return diag(1/2,R/2), and the normalized update z'=Rz, have the correct orientation and scale. The tangency point satisfies

    ||p||^2 = (12^2+26^2)/615^2 = 4/1845 > 0.

The trace/root-of-unity argument is valid: a root of unity plus its inverse is an algebraic integer, whereas the rational number 6/5 is not an integer. Hence R has infinite order. For a planar rotation this gives dense positive and negative semiorbits on each nonzero circle; no property of a general higher-dimensional orthogonal map is being assumed. The points R^(-n)p are pairwise distinct.

The normalized positive-gap triangle is exactly

    D = {1/3+u>0, 1/3+v-u>0, 1/3-v>0}.

The displayed reconstruction map from (0,infinity) times D to the positive cone is a homeomorphism: the gaps sum to d and recover u,v by the stated normalization. On the radius-rho closed disk the three gaps are bounded below by 1/3-rho, 1/3-sqrt(2)rho, and 1/3-rho. All are strictly positive because rho^2=4/1845<1/18. Therefore the full critical circle really is available as a positive-gap fixed-scale section for Report 57. The proof does not mistakenly use inadmissible inputs for this obstruction.

### Concrete chamber test

The A/B/A endpoint specification in companion Section 6 exactly matches the upstream chamber specification. In centered coordinates the first A changes x to

    d/3+xi-eta/2.

The next B changes y to

    2d/3+4xi/5+3eta/5.

The last A has first intermediate endpoint d/6+4xi/5-13eta/20 and final endpoint d/3+3xi/5-4eta/5. Substitution gives the expanded 12 rows in each of the A, B, and final-A blocks, including their upper-bound rows, as listed in GUARDS.txt. There are 36 strict comparisons. The local updates only evaluate the chamber; the persistent gap iterate is subsequently replaced by Mq. This avoids the possible double-update error.

For an additional arithmetic cross-check, the squared supporting-line distances for the rows in their given order are:

    A: 4/9, 1/9, 1/9, 1/18, 4/153, 4/41,
       16/153, 16/369, 1/45, 1/13, 4/45, 4/117
    B: 16/45, 4/45, 1/9, 4/117, 9/20, 4/1845,
       5/36, 20/369, 9/25, 4/1125, 1/9, 4/45
    C: 4/9, 1/9, 4/45, 4/45, 4/153, 4/25,
       16/153, 16/225, 1/36, 1/8, 1/9, 1/18.

These use the formula alpha^2/(beta^2+gamma^2) for alpha*d+beta*xi+gamma*eta>0. The unique minimum is B's first translation upper row, d/15-3xi/5+13eta/10. Its perpendicular contact is the stated p. This cross-check supports consistency of the imported normalized disk and contact; it does not substitute for the upstream proof that these inequalities are physically necessary and sufficient.

## 3 Proper Borel classification

Let S be the nondegenerate radius-rho circle, let E={R^(-n)p:n>=0}, and let K be its closed disk with E deleted. E is countable and dense in S.

The complement of K is the union of E and the strict exterior of the disk. The latter equals the union, over positive m, of the closed sets with squared radius at least rho^2+1/m. Thus the complement is F_sigma and K is G_delta. The companion's explicit countable intersection of open sets gives the same result, with the boundary retained except at the deleted orbit points.

For non-F_sigma, suppose S minus E were the union of relatively closed sets F_j. Every F_j has empty relative interior because it misses dense E; being closed it is nowhere dense in S. Each singleton of E is nowhere dense since S has no isolated points. Their combined countable family would cover the nonempty compact metric circle with closed nowhere dense sets, contradicting Baire. This is the decisive obstruction, stronger than mere nonsemialgebraicity. The nested-arc explanation is a valid elementary version of the same argument.

The continuous d=1 embedding i(u,v)=(1/3+u,1/3+v-u,1/3-v) has image in the positive cone G and pulls V back to S minus E. An F_sigma description of V relative to G would therefore make S minus E F_sigma, a contradiction. An ambient F_sigma description would in particular be relative F_sigma, so the ambient negative result follows too.

For the upper bound, normalization is continuous on G, so V is relative G_delta. Because G is open, the relative open sets in its representation can be taken ambient open after intersecting with G. Hence V is G_delta in R^3 as well. Independently, the original guard formula G intersected with the countable intersection of (M^n)^(-1)(C) gives this ambient G_delta representation immediately.

Taking complements gives exactly the stated proper F_sigma classification, relative to G or ambiently when nonpositive inputs are deemed invalid. No assumption that a projection preserves F_sigma, and no inference from nonsemialgebraicity alone, enters the argument. The proof establishes the proper Borel class; it makes no completeness or reduction-hardness claim.

## 4 Mixed integer and real existential certificates

The key intermediate claim is correct: every finite Boolean combination of polynomial sign conditions over R is F_sigma. For a polynomial f, the strict positive set is the union of the closed sets f>=1/j; the strict negative case follows by negation of f. Equalities and non-strict inequalities are closed. Disjunctive normal form, finite intersections, and countable unions give the result. Arbitrary real coefficients cause no issue because their polynomials are still continuous.

For each fixed natural or integer tuple n, the set of g admitting a real witness y for Phi(g,n,y) is semialgebraic by real quantifier elimination. There is no compactness requirement on the real witnesses. This is projection of a semialgebraic set, a crucial stronger hypothesis than being F_sigma.

The possible integer tuples form a countable set, including the zero-arity case as a singleton. Their semialgebraic projections therefore have F_sigma union A. If the proposed formula agreed with validity on every positive real g, then V=A intersect G would be F_sigma relative to G. Section 3 disproves that. The same proof works for signed integer witnesses, finitely many existential real witnesses in any finite dimension, arbitrary fixed real coefficients, and countable disjunctions of such finite formulas.

The extension to finite real quantifier blocks after fixing the integer tuple is also valid. It must not be read as a result for arbitrary alternation of real and integer quantifiers; the companion explicitly preserves that boundary. For a single polynomial equation without real witnesses, the fixed-integer fibers are closed zero loci and no projection theorem is needed.

Agreement only on integer gaps or a discrete encoding of rational gaps is a different hypothesis. Such agreement supplies no all-real F_sigma representation of V and cannot trigger this contradiction. Consequently the integer certificates are not refuted. The report preserves this distinction correctly throughout.

## 5 Exact BSS lower bound

For a fixed ordinary finite-time BSS program, each finite computation path has only finitely many arithmetic instructions, comparisons, and register accesses. Conditioned on that path, the accessed real registers contain rational functions of the fixed-dimensional input and the finitely many real program constants. The path's comparisons and every required denominator nonvanishing condition form a finite semialgebraic description. Intermediate division-domain restrictions must be retained even if the final expression cancels a denominator; the companion explicitly does so.

Finite halting paths form a countable collection, hence their input domains have F_sigma union. Intersecting with a promised domain yields a relative F_sigma set. In the present case G itself is semialgebraic, so even the individual path domains restricted to G remain semialgebraic.

This proves the needed necessary condition for semidecidability. Since V is not relative F_sigma, no such program semidecides V, including one with arbitrary finitely many fixed real constants. Decidability is excluded because it would imply semidecidability. These are exact all-real-register conclusions, not assertions about Turing machines on rational encodings.

The model qualification is appropriate. Finite algorithms that extract individual digits or implement other discrete work through the allowed comparisons and arithmetic are not excluded. What is unavailable is a completed infinite operation or an arbitrary oracle primitive. A real constant may encode information, but every finite halting computation still has a semialgebraic path domain, so such constants cannot defeat this topological argument. No converse claiming that every F_sigma set is BSS-semidecidable is needed or asserted.

The research-source checks in SOURCE_VERIFICATION.md corroborate this precise model and the relative upper bound, independently of the companion's self-contained proof.

## 6 Semidecision of invalidity

The strict guard algorithm is a valid rational-constant BSS procedure. It tests the finite rational chamber rows at q=M^n g. If any guard is zero or negative it halts; otherwise it advances to the next iterate. Invalidity means failure of at least one finite iterate by the imported exact intersection characterization, so every invalid positive input is eventually recognized. A valid input never triggers a halt.

The normalized alternative is independently sufficient: compute z using d>0; compare ||z||^2 with rational rho^2; halt outside the disk; otherwise enumerate the rational points R^(-n)p and test exact equality. A point in E is reached after a finite number of iterations. A point in the open disk or on S minus E never halts. The algorithm needs no square-root operation and no irrational circle-radius constant. It can explicitly loop forever on the open disk if desired.

Combining this upper bound for G minus V with Section 5 gives proper co-semidecidability, exactly as claimed. Ambient classification follows by first halting on nonpositive gaps, before normalization. Equality is essential: an algorithm that only notices strict escape would miss the forbidden tangency orbit.

The classification concerns failure of the prescribed indefinitely repeated complete word. It says nothing about whether the physical machine has another evolution after failure, and it does not inspect any Zeno limit. The uncontracted claim is appropriately qualified as the correctly reclosed variant, rather than repetition of an unchanged prefix with an incorrect messenger label.

## 7 Compatibility with encoded rational decision

On the critical circle, the complex quotient w=z/p is excluded exactly when w=((3-4i)/5)^n for n>=0. Modulo 5, 3-4i equals 3+i and (3+i)^2=3+i. Thus for every positive n the two integer coordinates of (3-4i)^n are nonzero modulo 5. No power of 5 cancels in either coordinate, and the least common reduced denominator is exactly 5^n. For n=0 it is 1.

The common denominator q therefore determines at most one candidate exponent. Repeated exact division checks whether q is a power of 5; a successful exponent has size O(L) for rational input encoding length L. Computing that one Gaussian-integer power and comparing exact rational coordinates is polynomial time. Fixed-many initial rational operations and gcd/lcm reductions keep all relevant integers to O(L) bits. No hidden integer factorization, orbit search, or approximation test is used.

In particular q=1 admits only candidate n=0, and w=1 is rejected. Strictly positive forward powers give accepted boundary examples because an infinite-order rotation cannot identify a positive exponent with a nonpositive exponent.

An exact arbitrary real register is not a rational numerator/denominator encoding. The two input models therefore support different algorithmic conclusions without contradiction. This review checks that separation; it does not re-audit the separate existential-positive arithmetic templates.

## 8 Rational rotation family specialization

For each fixed family member, write T for the finite nonempty tangency list, to avoid confusing it with the infinite forbidden set

    F = union over p in T of {R^(-n)p:n>=0}.

The family proof supplies a nonzero circle S, rational rho^2, rational tangencies, rational infinite-order R, and a finite strict rational chamber. Every individual backward orbit is infinite and dense in S, so F is countable and dense. Intersections between orbits or duplicate representatives cannot spoil those properties.

The family does not need the entire critical circle to lie in the open positive-gap triangle. Its initial-order rows are positive at the center and nonnegative throughout the closed disk. For an initial-gap form alpha+v dot w, nonnegativity on the disk gives alpha>=rho||v||. A zero on the circle forces equality in Cauchy-Schwarz and fixes the single point w=-rho*v/||v||. Thus each of the three initial-gap forms can vanish at at most one circle point. There are at most three inadmissible circle points. Removing them leaves a nonempty open collection of arcs, inside which one may choose a nondegenerate closed arc J.

The compact arc J has no isolated points, including its endpoints. F intersect J remains countable and dense in J. The Baire argument from Section 3 therefore applies to J minus F, and its d=1 embedding pulls family validity back to precisely that set. This proves non-F_sigma relative to the positive cone; G_delta follows from the family guard intersection. The same open-cone argument gives the ambient classification.

The mixed-certificate and BSS lower bounds then follow without alteration. For the complement, enumerate all finitely many rational tangencies in parallel through R inverse, or simply iterate the rational return and strict guard list. Both are finite rational-constant BSS programs. Positive scaling lambda cancels in normalized coordinates and preserves positivity of d at every finite iterate, so contracting, unscaled, and expanding members all satisfy the real-input classification.

The cited final family proof hash and its independent audit hash agree with SOURCE_NOTES.md. The companion correctly avoids replacing Report 57's chamber by the different chamber produced by the family constructor at the same rotation and scale. Their differing radii and event counts do not affect the abstract argument. This is a valid specialization of the audited family geometry, not a new audit of its physical constructor or its integer certificates.

## 9 Findings and limits

There are no substantive corrections. The following distinctions should remain explicit when summarizing the result:

- The all-real quantifier is indispensable to the certificate obstruction
- The negative BSS result is for ordinary finite-time field-operation computation, with finitely many fixed real constants allowed
- Invalidity means failure of the specified complete word, including equality guards
- The family extension uses an admissible compact arc, so zero-gap tangencies do not invalidate it
- The proof gives a proper Borel class, not a Borel or BSS completeness classification
- Physical exactness remains the explicit upstream dependency

One optional editorial refinement: companion Section 7 says that forward powers of (3+4i)/5 are accepted boundary examples. The intended meaning is strictly positive powers. Its immediately preceding sentence explicitly rejects the zeroth power w=1, so this is not a proof error or conflicting algorithm, but writing “strictly positive forward powers” would remove any isolated ambiguity.

The review's final verdict is PASS for every requested real-input conclusion and for the stated family specialization. Preservation hashes and the independent source-verification note accompany this report.
