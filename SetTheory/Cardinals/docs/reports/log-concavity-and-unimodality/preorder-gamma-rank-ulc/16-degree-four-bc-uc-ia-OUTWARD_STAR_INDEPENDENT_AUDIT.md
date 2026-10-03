# Independent audit: the last Newton inequality for outward 1+3 core stars

## Verdict

APPROVED. Every unit-activity directed graph of the stated one-source/three-sink outward-star form, with arbitrary independent exterior neighborhoods, satisfies 3Γ_3²≥8Γ_2Γ_4. The core star may have any neighborhood J⊆Q, including empty J, and reversal preserves the conclusion.

In the canonical four-attachment dataset this settles gap three for templates 1,4,10. Their gap-two certificates have separately passed full independent replay, so all three templates are completely proved. No general real-rootedness or arbitrary weighted full-Γ theorem is inferred.

## 1. The exact decomposition has no matching multiplicity

A support with no exterior head is exactly a Q-side support in which the source p is available as one extra exterior tail with neighborhood J. This is Q⁺. Any support having an exterior head has exactly one such head x, because only p can enter an exterior vertex. The edge p→x is forced, and the remaining support is a Q-side support with x deleted. Choosing x fixes a distinct head support, and deleting it prevents double use of the same physical vertex.

Thus Γ=Q⁺+tΣ_(x∈H)Q_(−x) exactly. It remains true when x has no Q-neighbor and when J is empty. The latter makes the extra tail a Q-loop. Each feasible ordered support is counted once, independently of the number of realizing matchings.

## 2. Correct polarization for the deletion sum

The three private dummies force rank three in the Q-side transversal matroid, including when physical exterior vertices are loops. A basis with k physical elements and the complementary dummy set specifies both the physical support and the selected sink subset uniquely. Its ordinary squarefree basis coefficient is one.

After dummy variables become z, the variables of the specified eligible set H become s, and all other exterior variables become t, the polynomial q(z,s,t) is homogeneous of degree three and Lorentzian. Its s-degree is at most m=|H| even if some eligible vertices are Q-loops.

Polarization must use the degree bound m, not the actual s-degree or the number of nonloop eligible vertices. The replacement s^k↦e_k(s_1,...,s_m)/binom(m,k), followed by s_1=0 and all other slots equal to t, multiplies each term by (m−k)/m. Multiplying by m gives precisely the deletion sum, because a support using k eligible physical vertices survives exactly m−k deletions.

This also explains why eligible Q-loops must remain in the slot count. They occur in no support but their deletion leaves every support unchanged. The m=0 case is handled separately and never invokes division by m.

The result is the exact degree-three homogenization m z³+A z²t+C zt²+D t³. The derivative in t is A z²+2Czt+3Dt²; the Lorentzian Hessian condition gives C²≥3AD. Nothing is divided by a homogenizing monomial, and no claim is made for a deletion-sum polynomial retaining every physical variable separately.

Brändén--Huh Proposition 3.1 was checked in the primary Annals text: polarization preserves the Lorentzian property with any coordinate degree bound. One-variable polarization follows by polarizing all needed blocks and immediately depolarizing the untouched blocks. Their Theorems 2.10 and 3.10 justify the substitutions and matroid basis polynomial: https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf .

## 3. Rayleigh gives the needed ratio monotonicity

Wagner's primary Theorem 1.1 states that every rank-three matroid is Rayleigh. Its basis-polynomial definition was inspected directly: https://arxiv.org/pdf/math/0403216 . Loop elements are immaterial to the basis polynomial; parallel elements are included. Polynomial continuity extends the positive-variable inequality to nonnegative boundary values.

Build the rank-three transversal matroid on the old physical exterior vertices, the three private dummies, and one proposed new exterior vertex e. At old exterior weights one and e=d_1=d_2=d_3=0, the exact derivative identities are

f=T,  f_e=ΔT,  Σ_i f_(d_i)=B,  Σ_i f_(e,d_i)=ΔB.

The first identity selects bases containing only old physical vertices. The second selects e plus two old physical vertices. A two-edge support has exactly one complementary private dummy, so it contributes once to the third sum. The last sum counts exactly the new two-edge supports involving e. All higher-dummy contributions vanish at the boundary, and squarefree derivatives introduce no factorials.

Summing f_e f_(d_i)−f f_(e,d_i)≥0 gives ΔT·B−T·ΔB≥0, or T_new B−T B_new≥0. This proves all neighborhood additions, with empty-neighborhood equality. The same side-monotonicity statement holds for arbitrary nonnegative old exterior activities, but that fact alone is not promoted to a weighted full-star theorem.

## 4. Zero cases and the final square

If D=0 then Γ_4=0 and the desired inequality is immediate. If D>0, at least one deleted side has a feasible triple support, so the original T and B are positive and C>0. Adding x back, then adding the J-neighbor vertex, gives

T_x B≤B_x T and T B⁺≤B T⁺.

Multiplying these inequalities and cancelling only the positive B proves T_x B⁺≤B_x T⁺. There is no division by B_x; if B_x=0 its triple coefficient is zero. Summing over x gives D B⁺≤C T⁺. Q-loops use equality in the first step.

Finally Γ_2=A+B⁺, Γ_3=C+T⁺ and Γ_4=D. Applying C²≥3AD and D B⁺≤C T⁺ yields

3Γ_3²−8Γ_2Γ_4≥C²/3−2CT⁺+3(T⁺)²=(C−3T⁺)²/3≥0.

All inequality directions, factors, and strict-positivity requirements are correct. The argument does not use transitivity; the legal preorder templates form a covered subfamily. Their rows and direction masks agree exactly with source p=3, sinks 0,1,2, and core neighborhoods of sizes one, two, three for IDs 1,4,10.

## 5. Independent finite algebraic backup

The seven ordinary-population monotonicity identities were independently reconstructed using Boolean Hall conditions, not the producer's matching-permutation routine. The checker obtains 28 pair kernels, 84 triple kernels, seven one-old-vertex universal increments, and 28 two-old-vertex universal increments with exact binomial population factors.

A standard-library Fraction verifier expands every supplied falling-factorial term and parses the three declared half-squares with a restricted arithmetic parser. All seven addition identities and the redundant universal side identity match the independently constructed polynomials exactly. There are 1,376 positive falling terms in the seven essential identities and 1,642 including the redundant record, plus precisely three half-squares. The universal side expression is independently verified to equal the type-seven addition expression.

The checker, Hall kernels, log and receipt are in `/workspace/shared/three-center-gap/independent-audit/`. These certificates corroborate the ordinary Rayleigh argument and are not a necessary computational premise of the approved all-population theorem.
