# A completeness obstruction in the second successor padding slot

Status: written mathematical proof, independently reviewed by model agents; not a Lean proof. Snapshot: ProveIt `7a7633980dbca7f599322a5e7f1e65fb1cddb7c8`.

## Statement

Consider the native sorted-arity proof protocol, with either canonical zero 0 or the uniform-zero-1 codec, and its exact-integer/list input contract. Keep all of its existing inference and scope checks. Its standard reading gives every dummy slot the value 0.

For each natural number c, change the reading in just one place: a successor array `[a]` evaluates its child below the two padding slots **(0,c)**, with the first listed slot the innermost. Every iterator-counter/initializer padding slot still has value 0. Actual iterator-state variables, the paired D variables, and Q variables are unchanged. Numeric zero is still 0; in the uniform-zero codec scalar 1 denotes zero. Every raw term is still read as an ordinary primitive-recursive arithmetic term, now possibly containing the extra constant parameter c.

**Parametric soundness theorem.** Every accepted closed public goal of the native protocol is true under this modified reading for every c. More strongly, the usual soundness induction on successful runs holds with this reading: an accepted goal is a consequence of the readings of the retained assumptions, with c fixed throughout. This is a statement about all accepting runs, not a bounded test result.

**Corollary.** In the uniform-zero-1 codec the raw formula `[[5],[1]]` passes the published P^ed_1 public-goal validator and reads as S(0)=S(0) under the standard reading, but no proof certificate for that raw goal is accepted. Under the reading above it is S(c)=S(0), false at c=1. Therefore P^ed_1 validation is strictly broader than a syntax on which the native checker is complete for every spelling under its stated standard reading. This does not refute canonical completeness: the canonical encoder never emits an occurrence of a padding-slot variable.

## Detailed proof of parametric soundness

The proof is a modification of chapter 11's opening, exposure, freshness, zero-instance-computation and successful-run lemmas. It is important to change only the *second* successor slot: changing all dummy slots, or the first successor slot, is unsound.

### 1. Locality of a validated tree

At a term root below p protected slots the depth is 3+2p (or the corresponding even offset). Below q binders belonging to the tree itself, a validated scalar can reference a rigid parameter, a zero spelling, one of those q internal slots, or one of the p existing outer slots. It cannot reference a newly inserted outer slot beyond these p slots.

The semantic values attached to a tree's internal slots remain the same after the tree is moved below more outer slots: in particular its own successor slots remain (0,c). This is the only change from the ordinary reading. Consequently inserting an image validated at root term depth into a hole does not capture any newly available outer slot. The structural induction proving the opening/substitution lemma is unchanged.

Exposure of one or two *actual* logical/state slots is also unchanged. Neither the numerical names of rigid parameters nor the freshness discipline depends on c. Arrays at formula positions that denote administrative truth still denote 0=0.

### 2. Computation at zero

A zero-computation packet generates the raw equation `[[s,u,t],u]`, where s is false-valued. The two occurrences of u are read below one additional iterator padding slot on the left and without that slot on the right. That additional slot is **still 0**.

A scalar of u referring to this outer iterator padding slot therefore reads as 0 on the left and as the exposed image on the right. The protocol's image is either literal zero or a fresh administrative parameter b. Substitution b:=0, when b occurs, makes the readings coincide. Internal successor slots of u are (0,c) on *both* sides and are never removed by this comparison. The initializer readings therefore agree after the same zero-instance substitution used in the upstream proof, and the generated equation becomes an actual zero-iteration equation. No substitution c:=0 is made.

### 3. Successor computation when the update uses its state

The generated raw equation is

    [[[s],u,t], O(t; [s,u,t], 3)].

If the interpreted update t depends on a meaningful occurrence of its state slot, evaluating the right-hand opening must consult its image, and therefore validates `[s,u,t]` at root term depth 3. An occurrence in an ignored annotation can force the same validation even when the interpreted update is independent of the state; that only adds a check and does not affect the argument. Thus its predecessor s is validated at depth 5, below **one** iterator padding slot. At a descendant position below q slots belonging to s itself, this gives the upper bound

    scalar < 5+2q.

In the constructed successor `[s]` on the left, s is read below the three outer slots

    (0,c,0): successor first padding; successor second padding; iterator padding.

Only the first of these can be referenced by s. Indeed the first has index 3+2q and corresponds to the sole iterator padding slot in the recursively constructed predecessor; both values are 0. The second has index 5+2q, exactly the excluded upper bound, and the third has still larger index. Hence no occurrence in a successfully validated s can observe c through the *newly added* second successor slot.

This remains true when s contains nested iterators or successors: q counts their internal slots, and those internal slots have the same values in both readings. Thus the predecessor has the same value sigma on the two sides. The initializer readings agree by the same argument used at zero. The state's exposed image is the recursive iterator. The generated equation is precisely the successor-iteration equation for sigma, the interpreted initializer, and the interpreted update. The ordinary parameter c may occur inside these terms, but that does not affect the validity of the equation.

### 4. Successor computation when the update does not use its state

In this case the right-hand opening has the reading eta independent of the state, whether or not an ignored annotation causes the implementation to validate the unused image. The predecessor may use the second successor padding slot; no equality with a recursively constructed predecessor is needed. Whatever its value sigma, iteration of a constant update at S(sigma) equals eta. Any exposed administrative parameters are specialized to 0 just as in the upstream zero-instance supply argument. Hence the equation remains valid for every c.

These two cases are exhaustive. Evaluation of an unused image may add rejection to an eager implementation, but cannot add a false accepting inference.

### 5. Hypotheses, equality and logical rules

Literal equality of raw trees gives equality of their readings at the same sort and depth. Therefore hypothesis lookup is sound. The opening lemma gives the ordinary substitution interpretation for equality transport and closure specialization. The auxiliary closure formula retains its ordinary or progressive reading, exactly as in the selected native or guarded protocol.

Opening D introduces an actual fresh numerical parameter; c is a fixed constant independent of the fresh-name supply, so existential elimination is sound. Introduction by cases is sound by zero-or-successor coverage in the natural numbers. Introduction by progress remains restricted to a literal equation, whose interpreted terms are primitive recursive with c as an additional fixed parameter, so equation induction is sound. No arbitrary-formula induction is introduced.

Administrative truths remain 0=0. A computation-supply branch concludes an old goal from H(b) with b fresh. By sections 2–4, H(0) is a true computation equation with c fixed. Apply the induction hypothesis at b=0; the old assumptions and goal are independent of b. This is exactly the original supply argument.

Induction on the finite successful run now establishes the theorem. For a refined checker, the argument transfers whenever its opening and inference steps have the stated semantics; a proof only of canonical-goal equivalence is not, by itself, a transfer theorem on noncanonical roots. In particular, the original native protocol already suffices for the corollary about the published strict interface.

## The public-goal check

For `[[5],[1]]`, the formula root has even depth 0 and arity 2. Each side is a successor array of arity 1 at term depth 3. Its child has depth 7. Both 5 and 1 are positive odd integers less than 7, exactly the leaf condition of P^ed_1. The left child 5 denotes slot 1, the second successor padding slot. The right child 1 denotes zero. Thus the root passes the published validator without any malformed type, scope violation, reserved zero spelling, or nonnative formula tag.

The original zero-0 version is `[[5],[0]]`.

## Why two tempting stronger models fail

1. Assigning c to the iterator dummy is refuted by the accepted original strict stack

       [[0,0,3,1], [[1,3,1],1]].

   The conclusion becomes I(0,c;u.0)=0.

2. Assigning c to the *first* successor dummy is refuted by the accepted successor-computation stack

       [[0,3,1,[7]], [[[3],1,[7]], [[3,1,[7]]]]].

   Its conclusion becomes I(S(c),0;u.Su)=S(I(0,0;u.Su)), hence c+1=1.

The analogous predecessor 5 is rejected by the recursive-image scope check. This is why the second-slot distinction is essential.

## Consequence for a corrected interface

A theorem checker with completeness for every syntactically admitted goal can either restrict its syntax to the exact canonical encoder image, or add a proved normalization/identification of padding references. Exact canonical validation can track a Boolean availability mask of slots: successor prepends two unavailable slots; iterator counter/initializer prepend one unavailable slot; iterator update prepends one available slot; D prepends two available slots; Q prepends one available slot. An indexed variable must select an available slot. The extra validator must be counted if the advertised contract includes this property.
