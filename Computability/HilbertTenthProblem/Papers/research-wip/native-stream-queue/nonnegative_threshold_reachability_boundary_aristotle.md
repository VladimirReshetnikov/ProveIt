# An exact finite quotient for nonnegative polynomial history systems

This note rules out one proposed route to a cheaper uniform compiler: making every update a polynomial with nonnegative integer coefficients, while retaining only finite control, fixed threshold tests and fixed congruence tests. Arbitrarily long histories in that model have decidable acceptance, including exact positive targets. The result supplies no new paid arithmetic source, no operation lower bound, and no obstruction to the existing signed group or Markov constructions.

The prior `group_gram_zero_mortality.md` already records the Boolean-support obstruction for nonnegative matrix mortality. The present argument extends that specific boundary to nonzero targets, finite guards, nonlinear nonnegative polynomial updates, and effectively input-dependent finite thresholds and moduli. Root requested the exact path-lifting and input-quantifier clarification. No external universality theorem or novelty claim is needed.

## 1. The finite-instance interface

Write N={0,1,2,...}. An instance consists of:

* a finite control set Q, dimension d, and a specified initial configuration (s0,v0) in Q×N^d;
* finitely many directed control edges. Each edge has a deterministic update F:N^d→N^d whose coordinate polynomials lie in N[X1,...,Xd], and a guard;
* an accepting predicate for each control state.

Each guard and accepting predicate is a finite Boolean combination of atoms

    P(v) ⋄ c,                    P(v) ≡ a (mod m),                 (1)

where P has nonnegative integer coefficients, c is a nonnegative integer, ⋄ is any of =, ≠, <, ≤, >, ≥, and m is a positive integer. All polynomials, coefficients, thresholds, residues and moduli are explicitly given finite data. A guard is tested before its edge update. A post-update test of the same form can instead be composed with F, remaining in the same class. Finite regular restrictions on edge words can be put in the control state.

One asks whether some finite legal path from the specified initial configuration ends at an accepting configuration. Its duration is unbounded. Updates need not be invertible or strictly increasing: constants, zero coefficients, zero coordinates and resets are allowed. Positive coordinate requirements are tests Xi≥1 and are included when desired. A fixed exact target, a positive target, or equality on only selected coordinates is covered by (1).

All of these finite data, including d, Q, v0, thresholds and moduli, may be produced by a total computable map from a finite program description and ordinary integer input. Once that particular instance has been produced, its data are fixed throughout the path. No bound on the size or running time of this compilation is assumed.

## 2. A finite semiring quotient

Choose

    K=max({1} ∪ {c+1 : c occurs in a threshold atom}),
    M=lcm({1} ∪ {m : m occurs in a congruence atom}).               (2)

Put κ(n)=min(n,K). On {0,...,K}, use capped addition and multiplication:

    a⊕b=min(K,a+b),              a⊗b=min(K,ab).

For all nonnegative integers a,b,

    κ(a+b)=κ(κ(a)+κ(b)),
    κ(ab)=κ(κ(a)κ(b)).                                           (3)

For addition, either both arguments and their sum are below K, or both sides saturate. For multiplication, a zero argument makes both sides zero. If both arguments are positive and one is at least K, both products saturate; otherwise the ordinary product is capped identically. In particular, no erroneous rule K·0=K is used: the correct result is zero, which is why resets cause no problem.

The residue map modulo M also preserves addition, multiplication and constants. Consequently

    π(n)=(κ(n), n mod M)                                         (4)

is a semiring homomorphism into the product of the capped semiring and Z/MZ. Its image A has exactly K+M elements: the K individual values 0,...,K−1 each have their forced residue, while the saturated value K can occur with any of the M residues. The latter claim follows by taking sufficiently large representatives in each residue class. The image is closed under both componentwise operations by (3).

Every P in N[X1,...,Xd] therefore has a well-defined finite evaluation Pbar on A^d, with

    π(P(v))=Pbar(π(v1),...,π(vd)).                               (5)

This follows by induction on its finite additions and multiplications, including constants. Reuse of intermediate expressions is harmless. It does not assume a fixed degree bound. The same identity holds coordinatewise for every update F.

For a threshold c<K, κ(n) determines all six comparisons of n with c: a saturated value is strictly greater than c, and an unsaturated value is n itself. The residue component determines every congruence in (1), since its modulus divides M. Hence each entire guard and accepting predicate has an exact evaluation on A^d, including arbitrary Boolean negations and combinations.

With no modular guards, M=1 and A is just the usual K+1-element capped quotient. For zero tests only, K=1 distinguishes exactly zero from nonzero.

## 3. Exact path simulation and a terminating decision algorithm

Construct the finite abstract graph on Q×A^d. For each original edge s→s', its abstract guard is the exact finite guard above and its abstract update is Fbar. This is a computable graph with

    Nstates=|Q|(K+M)^d                                           (6)

vertices. Start at (s0,π(v0)).

Every concrete legal path maps to an abstract legal path by (5). Conversely, take any abstract edge sequence reachable from that abstract initial configuration. Starting from the actual concrete v0, follow those same edges in order. Inductively the current concrete state maps to the current abstract state. Guard preservation makes the next concrete edge legal, and (5) makes its successor map to the specified abstract successor. Thus the entire abstract edge sequence lifts to a concrete path from the actual input. Exact accepting-predicate preservation finishes the converse.

This lifting is stronger than checking whether an abstract vertex has some representative. It uses the actual initial vector and the actual chosen edge sequence; no arbitrary representative, divisibility witness or existentially guessed large value is inserted at a saturated state. A reset after a large value is handled by the same identity (5).

Breadth-first search in this finite graph decides acceptance. If an accepting abstract path exists, a shortest one has no repeated vertices and has length at most Nstates−1; the lifting argument produces a concrete accepting path with that edge sequence. A requirement of at least one transition can be encoded first by adding a two-valued “a transition has occurred” flag to the control. This may double the bound but keeps it finite and exact. No polynomial-time, manageable-space, or small-integer claim is made.

**Corollary (uniform compiler boundary).** There is no total computable faithful translation of arbitrary ordinary-input recursively enumerable languages into these finite-instance reachability problems. Such a translation followed by the finite search would decide every translated language, including a nonrecursive one. The obstruction remains when the finite cap, modulus, dimension and control graph depend computably on the ordinary input. Their enormous possible values affect efficiency, not termination.

The claim does not deny a decidable language having an existential Diophantine description. It denies a uniform faithful representation of a nonrecursive language by this particular restricted reachability model.

## 4. Relation to the current arithmetic substrates

For nonnegative integer matrix mortality, take the matrix entries as coordinates, start from the identity matrix, update by multiplication by any chosen fixed nonnegative generator, and accept when all entries are zero. These are nonnegative linear updates and zero tests. Taking K=M=1 recovers the earlier Boolean-support finite-state argument. A control flag handles the convention that the mortal word must be nonempty. The new content here is the extension to nonzero targets and the broader update/guard class, not a claim to have first proved the mortality special case.

The positive Markov-mask lift does not meet the coefficientwise hypothesis: it represents arbitrary **signed** integer matrix actions in signed Fourier coordinates, up to a rational duration scale. For example, its r=1 construction with M=[−1] gives the strictly positive mask 1−(2/3)cos(4πx), whose chosen coordinate is multiplied by −1/3. Positivity of the averaging mask does not turn that coordinate update into a polynomial over N.

The actual guarded counter papers likewise retain the signed update C'=C−1 at C≥2. Their improved 8-operation local graph and 9T+1 direct fixed-duration certificate use positivity to recover a Boolean selector, but still contain signed residuals. Their ordinary-input language is exactly x≤T, and their number of rows and witnesses grows with T. Neither those savings nor the finite Markov lift supplies a fixed-arity universal history for free.

The current group-history note has a complete illustrative 244-operation, 36-witness certificate with unbounded duration and an explicit fixed-table scope; it does not instantiate a numerical universal alphabet. Its signed native norm equations and general polynomial equalities do not fall under (1). The existing unsquared finalizer W(1+ΣRi²)−1 preserves the integer zero set using a positive factor, but that sign argument does not make its expanded residual polynomials have nonnegative coefficients. This note neither alters nor reaudits those complete source arrays.

## 5. Numbered boundaries and a ruled-out simplification

**Review remark 1 (the proposed nonnegative universal-history simplification).** Retain the proposal in its precise form: “replace the signed affine or matrix history by nonnegative integer polynomial updates, preserve finite control and only fixed threshold/congruence acceptance, and thereby obtain a universal ordinary-input compiler.” Under the total effective compilation and specified-initial-state hypotheses of Section1, this proposal is false by Section3. Merely making a sentinel or the supplied witness coordinates positive is a different proposal and is not refuted. No global gate lower bound follows.

**Review remark 2 (positive values are not nonnegative coefficients).** On the positive counter domain C≥2, decrement remains positive, yet it breaks the cap congruence already for K=2,M=1: C=2 and C=3 have identical caps while their decrements have caps1 and2. Likewise division by2 on the even values2 and4 has successor caps1 and2. These are explicit boundaries of the cap model; no theorem about arbitrary rational maps is asserted. For the full quotient at any K≥2,M≥1, the equal-quotient values K and K+M can undergo K−1 legal decrements, reaching1 and M+1, which have different caps. Thus no finite quotient (4) can simulate all such decrements exactly.

**Review remark 3 (variable comparisons and nonnegative residual values).** At K=2,M=1, the pairs (2,2) and (2,3) have the same capped coordinates, but only the first satisfies X=Y. More generally (K,K) and (K,K+M) have the same quotient (4) and different equality truth values. Variable-variable comparison is not a fixed threshold atom. Nor can one apply this theorem to an arbitrary sum of squares just because its values are nonnegative: (X−Y)² has coefficient −2 on XY. Restricting a signed formula to its positive locus does not change its coefficient class.

**Review remark 4 (quantifiers not covered).** The theorem fixes the concrete initial vector by a total computable input map. It does not address an unbounded existential choice of initial witness coordinates subject to additional constraints, thresholds or moduli chosen existentially rather than fixed effectively from the input, variable divisors, an unbounded history supplied only by relational equations, or arbitrary nonregular external word-admissibility conditions. Some special cases could have separate finite reductions, but none is being claimed here. A source that uses those devices has not been excluded by this note.

**Review remark 5 (no regularity claim on ordinary inputs).** Decidability here is not a semilinearity assertion about input sets. The update v↦2v from v0=1 with target v=x accepts precisely positive powers of two. For each specified x, the cap K=x+1 gives the terminating search above. The accepted input set is not ultimately periodic: if it had positive eventual period p, then for sufficiently large 2^n>p, both 2^n and 2^n+p would be powers of two, although the latter lies strictly between consecutive powers. Fixed/input-dependent finite quotients must not be conflated.

The resulting next-action restriction is concrete: a proposed universal positive-coordinate adapter cannot remove *all* signed cancellation, division/normalization, variable comparison and unbounded initialization mechanisms while leaving only Section1's model. Some feature outside that model must remain, and its arithmetic/history costs must be paid. This does not identify which feature yields the best compiler, and it supplies no improvement to U9's complete operation count.

## 6. Inert source binding and evidence limits

The following files are in `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`. Inclusive read spans bind the interfaces used above; the accompanying JSON pins their exact bytes and span hashes. They are context and prior art, not executable dependencies of the finite-quotient proof.

| File | Exact read spans used here | SHA-256 |
|---|---|---|
| `group_gram_zero_mortality.md` |180–235|`e8fadc6769a30e3ca1f3bd8c6b7757c980f4e6d116fc378ed7659358b79f06f8`|
| `markov_mask_matrix_lift.md` |1–104 (full)|`5dca0ea91dc1d05b7e1a784e2933a67c059e99f3db0dad74f8491849345e69e6`|
| `markov_projective_counter_step.md` |1–120|`01003a2063d442fa71d4a5e80dfd8218edb7940c22fcc90d6b847079fd63a5d2`|
| `markov_positive_guard_savings.md` |1–158 (full)|`901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15`|
| `group_projective_tail_quotient_shift.md` |1–115|`a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a`|
| `group_projective_unsquared_outer_product.md` |1–90|`1c2b73853f09f42ff4603d4ae6f87ae0c7a905eef68928cf276b6ad1ad2cd13f`|

The polynomial/quotient/path proof above is self-contained. No supplied, archived, committed, frozen or predecessor helper/program was executed or imported. No saved source array was evaluated or symbolically propagated, no manuscript was rebuilt, and no repository or Git object was changed. Only inert document reading and fresh byte/span metadata collection were used. No full dynamic simulator, finite sample sweep, external universality proof, or whole ancestral-source audit is claimed. The displayed small examples are exact hand calculations, not extrapolations from tests.
