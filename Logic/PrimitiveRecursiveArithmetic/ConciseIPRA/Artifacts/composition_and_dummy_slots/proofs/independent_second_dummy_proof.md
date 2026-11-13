# A spare successor slot obstructs completeness for parsed aliases

## Precise claim

Consider the native raw certificate protocol of the pinned ConciseIPRA article, its strict uniform-zero profiles, and the four new profiles obtained by the reviewed eager/three-field/normalized-terminal compositions. The native public validator admits the closed equation

    [[5],[1]].

Under the published sorted reading, in which every dummy slot denotes zero, this equation reads S(0)=S(0). Nevertheless no finite successful certificate for this goal exists in these protocols. The proof uses an alternative sound interpretation of auxiliary raw syntax.

This is a theorem about the gap between the parsed alias grammar and the canonical native encoding. It does not refute completeness for canonical native codes, and it does not refute the repository's Lean bi-interpretation of the native calculus with iPRA. It refutes extension of canonical completeness to every parsed spelling under the published all-dummies-zero reading.

## Modified reading

Fix c in the standard natural numbers. Keep the article's raw-tree interpretation, negative rigid parameters, exposed-hole convention, real quantifiers, arithmetic equality, zero, and standard numerical iteration. Change only the second dummy slot introduced beneath a successor array.

At a term position, with an existing slot stack sigma ordered innermost first:

* The unary array [a] denotes 1 + value(a, (0,c) + sigma).
* The ternary array [n,a,h] denotes the standard iteration whose counter and initializer are read under (0) + sigma, and whose step body h is read under (state) + sigma.
* The other arities, scalar-zero aliases, and rigid negative parameters have their usual auxiliary readings.

In particular, the first successor dummy and every iterator dummy still denote zero. Real slots introduced by D or Q retain their usual bound-variable meanings. Formula scalars and neutral auxiliary array shapes continue to denote truth.

All finite raw term trees denote total numerical functions by structural recursion on the tree and ordinary finite iteration. No total universal evaluator is being added to the object theory.

## Opening, exposure, and freshness

The usual semantic-opening proof is unchanged after replacing the term environment clause for a successor by (0,c)+sigma. A successfully validated image at root term depth 3 contains no references to external slots. Copying it below further slots therefore preserves its value: its own successor dummy remains c wherever the image is copied. Exposing the outermost real slot does not change the positions or interpretations of any constructor's own dummy slots.

The uniform-zero operation on a retained scalar, a -> a or 1, still preserves the value of every numerical-zero alias. For the eager opener, an even-depth fallback returns 0 or []; both are formula truth, and the extra image validation only narrows the successful domain. The ordinary closure, exposure, and freshness lemmas therefore hold for this modified reading.

The argument concerns successful traversals and semantic readings. It does not identify the Python values 0 and [].

## The computation lemma

This is the essential case; changing both successor dummy slots would make it false.

Write the raw packet fields as (s,u,t). The generated computation candidate is

    H = [[s and [s],u,t], O(t;[s,u,t],3) if s else u].

The protocol may open H at newly allocated administrative parameters. Set those parameters to zero, exactly as in the inherited zero-instance supply lemma. The following argument also applies when a terminal profile successfully validates H without an image.

### Zero branch

If s is false-valued, its counter field reads as zero. The iterator initializer has one added dummy slot, which remains zero in the modified reading. On the right, the corresponding exposed references are opened or specialized to zero. The intrinsic successor slots of u are the same in both occurrences. Hence H at the zero administrative instance reads as the zero computation equation.

### Successor branch, with actual state dependence

Suppose the step body t semantically uses its outer state slot. Then computing O(t;[s,u,t],3) must visit a numerical hole and validate the recursive image [s,u,t] at root term depth 3, with no further image. This validation has three consequences:

1. s is validated below exactly one added iterator dummy slot;
2. u is validated below exactly one added iterator dummy slot;
3. t is validated below exactly one added state slot.

In particular, s can reference its one permitted outer slot, but cannot reference a second or third outer slot. Its allowed outer slot has value zero in the recursive counter. In the left counter [s], the same raw s lies under the stack (0,c,0), introduced by the successor and iterator together. Its only accessible outer slot is the first zero. The extra c slot and third zero slot are not referenced. Thus the predecessor value is the same on both sides.

This argument is applied after any genuinely external variables have been represented by negative rigid names; those names are unaffected by the extra slot stacks. Intrinsic binders and dummy slots inside s are unchanged.

The initializer and step-body readings also agree by the successful recursive-image validation and semantic opening. Consequently H is exactly the successor computation equation for standard iteration in the modified reading.

### Successor branch, without actual state dependence

If the step body is independent of its state slot, one or more iterations of it have the same result, irrespective of the initializer and the predecessor. The left counter is a successor, so its iteration applies that constant update at least once. The opened right endpoint has the same constant value. Thus H is true even if a recursive image need not be visited or validated.

If an otherwise irrelevant annotation causes validation anyway, that adds a restriction and does not invalidate this argument. Conversely, an actual state occurrence always lies on a semantically meaningful numerical path, so it cannot be skipped by an even-depth fallback.

### Why code 3 is not an obstruction but code 5 is

The accepted packet

    [[3,1,[7]], [[[3],1,[7]], [[3,1,[7]]]]]

would be false if the FIRST successor dummy were nonzero: it would compare an iteration of length c+1 with one of length 1. This is why the first successor dummy must remain zero.

Trying to replace the predecessor 3 by 5 while keeping the state-using body [7] fails. The recursive image [5,1,[7]] is not validated at root term depth 3: its predecessor 5 is outside the one permitted iterator-dummy slot. Therefore the computation rule cannot force the second successor dummy to be zero by this route.

## Soundness of the remaining protocol

The hypothesis/neutral cases remain true-resource cases. Equality transport is valid because the opener still implements capture-free numerical substitution. Closure specialization and D elimination use the unchanged logical meanings and freshness lemma. Introduction by cases is sound on the standard natural numbers, and the progress branch is still restricted to equations and is sound by numerical induction. These arguments depend on numerical values, not on the interpretation of unused dummy slots.

For computation supply, apply the continuation's soundness induction hypothesis and specialize every newly admitted administrative parameter to zero. The old context and exported conclusion contain none of those parameters. The computation lemma makes H(0) true, so it can be discharged. It is unnecessary, and generally incorrect, to claim that H(b) itself is always an axiom before specialization.

The reviewed new profiles preserve exactly these ingredients: eager semantic opening, the empty true neutral, branch-specific three-field reconstruction, and the closed-candidate terminal computation test. Their previously established finite-call soundness inductions therefore apply to every fixed c.

## The separating goal

The scalar 5 in [[5],[1]] is the second dummy beneath the left successor. The scalar 1 in the right successor is numerical zero. Thus this goal reads

    S(c) = S(0)

under the modified interpretation. For c=1 it is false. Soundness proves that no finite successful certificate for it exists.

The strict public validator nevertheless admits the tree: its root has equation arity 2; both term roots have successor arity 1; their leaves are odd nonnegative integers below depth 7. Under the original reading c=0, the equation is reflexive. Its canonical encoding [[1],[1]] is an ordinary native theorem.

Accordingly, a map that erases every dummy-slot reference to zero does not yield an internally reversible representation normalization on all parsed public codes. The native canonical theorem language and the larger parser-admitted grammar must be distinguished in correctness and size claims.

## Finite adversarial evidence

The accompanying audit_second_dummy.py enumerates all ordered triples drawn from its explicit finite sample of small exact-integer/list trees, with a truthy initializer field. It constructs the eager computation-supply candidate, opens it at one fresh administrative parameter, specializes that parameter to zero, and evaluates it using successor dummy slots (0,1) and iterator dummy 0.

The run examined 22,707 packets. Of these, 15,630 successfully opened; all 15,630 evaluated to true, and none exhausted the audit's evaluation budget. The exact sample, counts, Python version, and script hash are recorded in second_dummy_computation_audit.json. This finite check is supporting evidence for the computation lemma, not a substitute for its proof or a search over all certificates.
