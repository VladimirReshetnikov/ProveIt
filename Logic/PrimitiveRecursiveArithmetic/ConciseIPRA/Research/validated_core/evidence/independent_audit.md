# Independent review of the candidate checker reductions

## Scope and provenance

This review is by a parallel assistant, not an external human review or a proof-assistant verification. It inspects the proposed Python changes and proves their relevant mathematical invariants. Finite test runs are reported separately by the implementing agent.

The inspected repository is VladimirReshetnikov/ProveIt at commit `a4e5e96c456303cf231eab2aeeb3291d8889833f`. All six incoming ZIP files were obtained through GitHub's base64 file interface. Their decoded byte counts and Git blob SHA-1s were recomputed and matched the repository metadata. `reference/source_provenance.json` records every ZIP's repository path, pinned commit, Git blob ID, SHA-256, byte count, and selected extracted checker hashes.

The genuine compact incoming envelope is 257 significant tokens / 279 AST nodes / 522 normalized bytes, attained by three guarded_source programs. It is not the older 259 / 283 / 526 envelope in the main README. The strict full Eq/Q/D typed control is the byte-exact delivered controls/control_shared_typed.py in the incoming reversal package; it is 1049 normalized bytes. This actual delivered control is the primary comparator. The 1000-byte Eq/D typed comparator is a derived matched restriction of that control to the already existing Eq/D public grammar, and is labeled as such.

## Staged validator specialization: sound

Let J(q) assert that every node of the entire JSON input q is an exact Python integer or an exact Python list. Python booleans are deliberately excluded because type(True) is not int. The recursive predicate `type(a) is int or (type(a) is list and all(map(j,a)))` is exactly J on every finite JSON tree. Replacing a generator-based `all(j(b) for b in a)` by `all(map(j,a))` preserves the truth value and traversal order.

Once J(q) has succeeded, every extracted goal and every subtree passed to the public grammar validator is an exact integer or list. Therefore after the branch that handles integers, the remaining object is already known to be a list. Removing the repeated `type(a) is list` guard is sound. No intermediate mutation changes input node types: popping the outer list only removes a reference to an already checked subtree.

On this staged domain, `a * 0 == 0` is true precisely for integers and false for lists; `a * 0 != 0` selects precisely lists. Thus the changed discriminator in the opener and, if used, in the public validator has the same successful behavior as the old `a * 0 == []` list test. Kernel-generated negative labels, numeric zero and any Boolean zero aliases also have the same scalar behavior. The opener's default invalid replacement is a function object: multiplying it by zero raises TypeError under both discriminators, so it cannot cause a new acceptance. The input stage rejects all user supplied floats, booleans, strings, dictionaries and null before the kernel runs.

For exact integer a, `a==0` can be replaced by `not a`, and `3<=a<d` by `2<a<d`. These substitutions preserve the predicate, rather than merely its standard-model meaning.

## Shared arity tests: sound

The public validator uses odd depth for terms and even depth for formulas. Its depth changes by `5-len(a)` on descent. With only Eq/D public formulas:

- At even depth, `len(a) in (1,2+d%2)` means exactly arity 1 or 2.
- At odd depth it means exactly arity 1 or 3.

For full Eq/Q/D formulas, `len(a) in (1,3,2+d%2)` admits exactly the old arity sets. A separate diagonal-triple test is still necessary at even depth.

A shorter equivalent successful-recognition condition is `(len(a) in (1,2+d%2) or a == [a[0]]*3)`. At even depth its second disjunct admits exactly diagonal Q triples. At odd depth every diagonal triple already has the permitted ternary arity. On an empty list the second disjunct may raise IndexError; this is rejection under the explicit checker contract, matching the old validator's False result. If the validator itself is claimed to be a total Boolean predicate, retain an explicit nonempty guard instead. Do not claim total-predicate equality for the partial spelling.

## Single raw/goal validator: sound invariant

The code-sharing design, adopted in the final native checkers, uses one validator. The final actual-source review is in `evidence/mathematical_review.md`. Its mode/depth parameter d has this meaning:

1. d=0: check only raw exact integer/list syntax, recursively preserving d=0.
2. d>0: check canonical syntax at old opener depth d-2; the public formula call is therefore V(goal,2).

The descent `d and d+5-len(a)` keeps raw mode zero and advances canonical mode by exactly the old amount. The parity of d is the parity of d-2. The integer bound becomes `2<a<d-2`, exactly the old `3<=a<old_depth`; numerical zero is unchanged. In raw mode the first `not d` alternative accepts every exact integer and suppresses arity restrictions on lists. The list discriminator still rejects other JSON types. A structural induction establishes both invariants simultaneously.

If V uses `a*0==[]` in place of `type(a) is list`, non-list JSON values either give False or raise before acceptance. In particular bool and float multiply to numeric zero, strings to empty string, neither equal to [], while dictionaries/null raise. Such a version recognizes exactly the desired raw language but is a partial recognizer, not a total predicate on all JSON values.

It is also sound to pop the goal before the typing check and then check V(remaining_packets,0) and V(goal,2): successful canonical goal validation implies raw typing of that goal, so together these checks cover the entire original input, including unused prefix packets. Non-list top-level JSON values fail the argument-free pop. For a fair byte comparison, do not credit arbitrary shortening of error-message text as a mathematical simplification; document any merged diagnostics or keep matched messages.

## Tail-recursive continuation replaced by a loop: sound with immutable context

The original global-floor compact checker recursively calls itself on the continuation after each instruction. Replacing just this tail call by updating the local goal and context and repeating a while loop preserves every idealized finite successful trace. Recursive major-premise checks must remain recursive. Global freshness allocation must stay in the same order.

The retained context must be immutable or rebound. The selected `code/guarded_tokens.py` uses tuples: `g += (resource,)` creates a new tuple bound to the current invocation's local g. The tuple passed to a recursive major check cannot be changed in the caller. This is safe and was independently inspected.

The exploratory `global_loop.py` uses `g += [resource]`, which mutates a shared list and can leak assumptions from a major subproof. That prototype must not be delivered as an accepted checker. Rebinding with `g = g + [resource]` would also be safe. The implementer has confirmed the tuple profile is the selected one.

On finite hardware, loop conversion can avoid RecursionError on proofs for which the old tail-recursive program exhausted its stack. The exact equivalence claim is under the repository's ideal finite-certificate convention, not equality of every machine's resource-failure behavior.

## Neutral truth plus exact-root introduction: sound

The detailed proof is in `evidence/neutral_zero_exact_root.md`. Initial formula truth [] can be replaced by formula truth 0, while dummy computation/introduction majors are changed from [] to 0 in generated certificates. The negative-variable floor and initial context length do not change. Every ordinary packet case remains sound under the guarded auxiliary decoder.

One additional raw case deserves explicit mention: a nonzero scalar major may now normalize to retained truth 0. It cannot equal the list-valued elimination matcher; multiplying it by three exports only another scalar truth. It cannot create an equation or closure. Thus no new canonical public consequence appears. Canonical completeness follows by changing only neutral-major packet fields in the existing compiler. This transfers the existing guarded public bi-interpretation; it does not establish a new full-language auxiliary round trip.

## What may be claimed

These are smaller complete checker implementations of already described presentations. The parser and continuation transformations are proved program refactorings, and the neutral/exact-root composition preserves the inherited canonical guarded consequence relation. They do not supply a new arithmetic foundation, a new proof-assistant verification, a global lower bound, or an absolute simplestness theorem. Distinguish native full Eq/Q/D, native public Eq/D, and guarded compact contracts in every comparison. State that separate profiles attain separate coordinate minima.

The executable core's iPRA bi-interpretability follows from unchanged native consequence relation or from the established guarded public equivalence, as appropriate. Both ordinary numerical domains and equality are unchanged in these transformations. The inherited interpretation proofs are mathematical dependencies, not consequences of finite tests or byte counts.
