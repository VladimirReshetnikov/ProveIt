# Audit of reservation at call entry

This audits the evaluation order in `agent_kernel/entry_tokens.py` and `agent_kernel/entry_ast.py`, inspected on 2026-11-13. It is a mathematical audit, not a machine-checked proof. The originally inspected copies used a singleton set as successor image, which is incompatible with their multiplicative array test; the image must be the singleton list `[k]`.

## Required order

At every call `c(g, a)`, with current global floor `K`:

1. Read the next packet.
2. Evaluate the scan `i(a)` at floor `K` as the left operand of the membership comparison. The result need not be assigned back to `a`.
3. Reserve a fresh value as the first member of the comparison tuple, `(k := k - 1)`.
4. Perform the terminal comparison and, when necessary, the elimination pre-opening or the witness pre-opening.
5. Prove the major with `c(g, s)`.
6. Use the returned current floor as the new eigenparameter, construct the opened hypothesis and continuation, and recurse.

There is no decrement at return. Python evaluates the left operand before the right tuple, and tuple members left to right, so `if i(a) not in ((k := k - 1), *g, candidate): ...` has exactly this order. The opener uses `k == 0` as the strict public-goal phase, with the root call alone starting at zero. The initial context contains the neutral truth, so the former per-call `g.append(0)` is unnecessary.

The added tuple member cannot create a new terminal. If the old-floor scan returns a scalar, it is either zero or an admitted negative scalar at least `K`; the new marker is `K-1`. If the scan returns an array, it is not the scalar marker. Hence `i(a) == K-1` is impossible.

## Invariant

The context of a call and its exported goal have ordinary readings whose free numerical parameters belong to the scope already in force before step 2. Every meaningfully occurring parameter therefore has value at least the old floor. Auxiliary trees can contain irrelevant annotations, but the argument is about their established ordinary readings, not every raw integer in a tree.

The entry scan is made before reservation. Consequently a returning call cannot export a goal that mentions the value first reserved by that call, or any later value, unless that value had already been present before its entry (which strict decrease excludes). Lowering the floor afterward amounts to parameter weakening: it admits an unconstrained fresh numerical parameter. Such a parameter can occur in internal terms and internal derivations; the exported sequent remains the one fixed at entry.

## Freshness at introductions and openings

The source and target instances of an elimination are opened before its major is proved. For an introduction, the witness instance of the matrix is also opened before the neutral major is proved. Let the floor at those pre-openings be `L`. The major call first validates its exported major at `L`, and then reserves at least one lower value. Hence its return has floor `K' < L`.

The parameter `K'` is fresh for the major, the pre-opened witness instance, the previous context, and the previous goal. It therefore meets the eigenparameter conditions for the paired elimination and for both forms of introduction. The fact that other fresh parameters were made available during the major derivation does not weaken this conclusion: the exported major was fixed before those reservations.

The crucial inequality is strict. Omitting the reservation of a terminal major, or choosing an eigenparameter before the major's entry reservation, would invalidate this argument.

## Terminal equations

A computation candidate is compared with a goal that was validated before reservation. A new parameter admitted during candidate construction cannot appear meaningfully in the compared goal. A successful syntactic equality therefore has the same ordinary computation reading as the established direct-terminal rule. Computation leaves do not discharge assumptions.

The exact candidate is `[[s and [s] or 1, u, t], i(t, [s,u,t], 3) if s else u]`. Its outer scan is omitted. The repair `or 1` uses the strict codec's canonical dummy spelling of numerical zero. If `s` is false, a successful comparison has the shape `I(0,u;v.t)=u`; the same raw `u` is valid both below the iterator's dummy slot and as the right term, so dummy-slot erasure gives equal readings. If `s` is true, it has the shape `I(S(s),u;v.t)=t[I(s,u;v.t)/v]`. If the state occurs, the right opener validates the recursive image at the root term depth; if it does not, the right side is independent of that image. These are the existing direct-computation-leaf cases. Literal equality with the already scanned goal supplies the validation of the candidate's left side; a separate scan of the whole candidate is not needed. The reservation move changes only which additional free parameters would be admitted while constructing a candidate, and those cannot occur in a matching old-floor goal.

## Public-goal validation

The global floor is initially zero and is decreased exactly once at every entered call. It can never become zero again. Since the first `i(a)` is evaluated before the first decrease, `k == 0` selects strict validation exactly at the public root. All later opener calls have auxiliary mode. This reproduces the former phase transition from the empty context to a context containing the neutral truth.

The old `g.append(0)` added only duplicate copies of neutral truth after the first call. Removing those copies preserves context membership. Its `None` return was an additional irrelevant member of a membership tuple; the opener never returns `None` on a successful input.

## Keeping the raw local goal

The implementation retains raw `a`, as the previous checker did. The no-image scan preserves its ordinary reading and establishes closure at the old floor in all semantically active numerical positions. An ignored annotation or a scalar at a formula position need not satisfy a stronger claim about every raw integer; neither is a free numerical occurrence. Decreasing the floor preserves the sorted reading of the raw tree. The existing opening/exposure lemmas, formulated for those sorted readings, therefore still apply. It would be incorrect to claim that every raw scalar of `a` is in the old numerical scope.

Exact certificate-by-certificate equivalence with the old checker is not claimed. The allocation schedule changes and later references may need renaming.

## Completeness

Compile an abstract derivation using the new depth-first schedule, assigning each eigenparameter the fresh floor after its major call has returned. All free parameters in the continuation are mapped to already allocated values. The extra parameter reserved at entry need not be used. The same rule-by-rule compilation used for the original checker applies, because the mathematical rules require freshness, not contiguous names or reservation at return. Equivalently, carry an injective finite environment from abstract eigenparameters to allocated negative integers while compiling.

Do not claim that old JSON packets remain valid unchanged: the allocation schedule changes, so certificates mentioning eigenparameters generally need renaming or recompilation.

## Conclusion

Subject to the exact evaluation order above, the reservation move is sound and complete for the same ordinary calculus. The substantive invariant is exported-goal validation before scope extension, followed by one strict extension during every major call. This is a checker-protocol refinement of the inherited axiomatization, not a new arithmetic axiom or a proof of a global minimum.

## Concrete implementation correction found during audit

For the multiplicative array-test opener, `i(3, {-2}, 3)` at floor `-2` raises `TypeError: unsupported operand type(s) for *: 'set' and 'int'`, whereas `i(3, [-2], 3)` returns `[-2]`. Thus a singleton set cannot stand for the successor image in these candidates. That optimization belongs only to an opener that traverses arbitrary iterables inside a `try` block. Restoring `[k]` is necessary for completeness and should be covered by a positive test whose matrix genuinely uses the induction parameter.
