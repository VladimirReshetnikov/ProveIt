# A bounded joint strong/auxiliary factoring census on complete86

No arithmetic saving occurs in this declared family. Across **292,320 schedule choices**, the best complete polynomial still costs **86=48M+38A**, with the same19 positive witnesses, ordinary positive input, fixed compiler numerals and exact degree179. The census crosses the two factors through six-monomial expansion, term partitioning, Horner evaluation and shared square-root ports. It is not a lower bound for arbitrary circuits or coordinate changes.

The [checker](complete86_joint_strong_auxiliary_scout.py) and [receipt](complete86_joint_strong_auxiliary_scout.json) authenticate the complete source/proof/receipt of [the86-operation first-root construction](complete86_factored_first_root.md), read its actual normalized first form, and import no historical compiler. All complete sources in this packet are exactly the parent's polynomial, on every integer or rational tuple; there is no new zero-set or witness-map argument.

## Actual coupled block and scope of novelty

In the source's notation, `A` means the discriminantDelta, not its Pell parameter. Write

```
Delta=(a+2)^2−1, c=kY+eta,
t=i*c², Q=Delta*t², H=Delta*t, K=Delta*Q=H²,
V=o*f−c,
Ns=f²−Q,
Na=K*(V²−y²)+y².
```

The actual gates are `ic2=t`, `ic22=t²`, `strong_difference=Q`, `R16=K`, `aux_u_rhs=V`, `norm_strong=Ns` and `norm_aux=Na`. The source already needs `c2=c²` and `Ac2=Delta*c²` in its main norm. The alternate root `shared_H=i*Ac2` is **computed and paid**, with no new input. The helper checks these literal definitions and checks that the two factor outputs are consumed only by their respective product-finalizer rows.

The [earlier coefficient census](complete87_shared_coefficient_scout.md) permitted only multiplication of monomials to produce Q and K. The [independent five-gate auxiliary bound](auxiliary_norm_five_gate_lower_bound.md) fixed independent ports K,V,y. Neither covers evaluating the joint product NsNa through cross-factor additions, distributive expansion or the actual root H. The present family permits those operations, while leaving the supplied coordinates and every mathematical condition unchanged. The earlier common-discriminant norm compositions and auxiliary-ordinate translations are not rerun.

The original12-gate joint evaluator from paid ports Delta,c²,Delta*c²,i,f,V,y is9 multiplications and3 additions/subtractions: four coefficient multiplications, three squares f²,V²,y², one coefficient-times-gap multiplication, three subtractions/additions, and the final product. These are local cuts for describing the search, not free ports in the complete cost. Every actual prerequisite survives or is pruned according to its complete downstream use.

## Exact declared family

Let Ff=f², VV=V² and YY=y². The symbol Ff here is unrelated to the parent's supplied packed-field coordinate named `F`.

| Chart | Five local ports | Joint target |
|---|---|---|
|QK|Ff,Q,K,VV,YY|`(Ff−Q)*(K*(VV−YY)+YY)`|
|QA|Ff,Q,Delta,VV,YY|`(Ff−Q)*(Delta*Q*(VV−YY)+YY)`|
|T2A|Ff,t²,Delta,VV,YY|`(Ff−Delta*t²)*(Delta²*t²*(VV−YY)+YY)`|
|tH|Ff,t,H,VV,YY|`(Ff−t*H)*(H²*(VV−YY)+YY)`|
|Raw tH, separate powers|f,t,H,V,y|`(f²−t*H)*(H²*(V²−y²)+y²)`|
|Raw tH, joint squares|f,t,H,V,y|same target, alternate monomial evaluation below|

Each expanded target has exactly six signed monomials. For each chart the helper uses:

- All203 set partitions of these six monomials, with the terms in fixed descending lexicographic order and partition blocks in canonical restricted-growth order. Block results are accumulated in that fixed order; other block orders or sum bracketings are not enumerated.
- All120 permutations of the five local variables as a **common Horner order across every block**.
- Two factoring modes. Both remove the common monomial of a block recursively. The second also forms candidate primitive binomials from pairs of remaining monomials, sorts those candidates, and uses only the **first exact divisor** with a nonconstant quotient. This is deterministic binomial factoring, not enumeration of all possible factorization schedules. The rule is applied to polynomials with at least three terms; it does not add a general difference-of-squares optimizer for two-term blocks.

Powers use a fixed binary powering recursion, and ordinary monomials multiply the resulting variable powers in the chosen order. The raw joint-square chart additionally replaces a monomial all of whose exponents are even by the square of the monomial with halved exponents, recursively. This permits such shared products as `(H*V)²` when the declared factoring exposes that monomial. It does not enumerate arbitrary addition chains or arbitrary algebraic intermediates.

Thus the number of declared choices is

```
6 charts ×2 factoring modes ×203 partitions ×120 orders =292,320.
```

There are58,113 distinct literal local DAGs **summed within the twelve chart/mode groups**. This is not a claim that all58,113 are globally distinct or represent different polynomials. All represent the stated joint factor after their chart substitutions.

Each local DAG is installed into the actual complete86 source. The new finalizer combines NsNa once with precisely the six other original factors. Exact commutative common-subexpression reuse, integer constant folding, zero/one identities and dead-gate pruning are applied to the whole emitted source. The same pass leaves the original baseline at86. Every surviving square, fixed nontrivial scalar multiplication, sum, difference, factor multiplication and final subtraction of1 is charged. The paid H, all retained strong/ratio/input quantities, and all ordinary-input and compiler ports remain subject to this full accounting.

## Complete counts and polynomial proof

| Chart | Monomial factoring only | With deterministic binomial factoring |
|---|---:|---:|
|QK|87=49M+38A|86=48M+38A|
|QA|87=49M+38A|86=48M+38A|
|T2A|88=50M+38A|87=49M+38A|
|tH|87=49M+38A|86=48M+38A|
|Raw tH, separate powers|87=49M+38A|86=48M+38A|
|Raw tH, joint squares|87=49M+38A|86=48M+38A|

These are minima within each declared group, ordered first by total operations and then by M/A. The receipt saves the complete best source for each of the twelve groups, every cost histogram, and hashes of the deterministic ordered censuses. None of these schedules gives85 operations.

The proof has three separate literal-source checks:

1. Six exact sparse-polynomial substitutions show that each chart's target is NsNa under the **computed** source ports. In particular H=i*Ac2=Delta*t and K=Delta*Q; these equalities need no unit or zero premise.
2. Each of the58,113 local DAGs is expanded exactly and compared with its chart's full six-term polynomial. Independently, the complete emitted DAG has the same structural expressions for each of the six other factors: first norm, main norm, input norm, packed index, transport and coupled linear unit. This gives348,678 retained-factor DAG comparisons.
3. At those six proved cuts and the joint NsNa cut, every complete product-minus-one output is expanded and checked against the parent's eight-factor product-minus-one. There are58,113 such complete finalizer identities. Source closure, gate liveness and **equality of the complete free-coordinate set** are checked for every distinct emitted local schedule.

Consequently no norm-sign or Pell-order argument is changed. The parent's complete positive zero set, ordinary-input relation, fixed-program requirements and exact degree179 transfer by equality of the entire polynomial. In particular this packet does not replace `i*c²` by a free witness, remove its divisibility condition, weaken the strong-rank lemma, or infer an old positive coordinate from a new one.

The supplemental numeric checks evaluate each of the twelve complete best sources on32 assignments:384 complete output comparisons,192 with signed inputs, including96 rational tuples. These are algebra checks; **no imported universal zero is materialized**. The coefficient and DAG identities, not finite sampling, prove the equalities.

## Limits and replay

This is a negative result for the explicit partition/Horner/factoring/power grammar. It does not exclude better arbitrary circuits, additional paid-register sharing, other polynomial factorizations, different finalizers, positive-coordinate changes or an improved universal representation. The apparent one-gate projection replacing `i*c²` by a free positive quantity is not justified by this search; the existing [linear-strength target obstruction](complete75_linear_strong87_target_crt.md) explains why losing the rank condition cannot be dismissed as a harmless renaming.

The helper is a standalone research CLI, not a general hostile-packet compiler API. It reads three pinned parent files, executes no imported parent code and writes only an explicitly requested output path. Python's standard library suffices. Optimized `-O` execution is rejected; saved-receipt comparison is recursively type-sensitive.

```sh
python3 complete86_joint_strong_auxiliary_scout.py \
  --root /path/to/native-stream-queue \
  --expect complete86_joint_strong_auxiliary_scout.json
```

`--output /path/to/new.json` saves a fresh deterministic receipt. The source/hash pins, exact coverage and complete twelve best sources are recorded there. Repository sources and existing frontiers are unchanged by the scout.
