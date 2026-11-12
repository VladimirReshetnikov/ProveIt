# Independent review of the final checker transformations

This is a same-session assistant review, not a proof-assistant verification or external peer review. It audits the stated transformations relative to the supplied upstream checker semantics; it does not independently re-prove the inherited checker metatheory for every malformed JSON value.

## Files reviewed

The comparison sources are the corresponding `checker_tokens.py`, `checker_bytes.py`, and `checker_ast.py` under:

`incoming/ipra_guarded_source_2026-11-11/ipra_guarded_source_2026-11-11/code/`

The reviewed new files and SHA-256 hashes are:

| File | SHA-256 |
| --- | --- |
| `agent_checker/checker_tokens_256.py` | `27a6df3c4236c68a44a8f2b51043f4a9ebdfcd95ca9e57125ac6cc77e26d1e20` |
| `agent_checker/neutral_checker_bytes.py` | `895a8b4f2202dffdc5759249ecbc4f4058160c87d4ad87cd6df851c9694b97c6` |
| `agent_checker/neutral_checker_ast.py` | `1dcb980b0a84755fc44a26c0ae9ec5f631f4aea432cfba8bb8a5862162660f9a` |

## 1. Token profile: tail recursion becomes a loop

The token profile makes three coordinated changes:

1. A hypothesis match exits a `while` loop instead of triggering an explicit early `return`.
2. The final recursive continuation call becomes an update of the local goal and context followed by another loop iteration.
3. Contexts are tuples, beginning with `()`, and are extended by `g += (new_hypothesis,)`.

The primitive inference dispatcher, major-premise recursion, opening operation, introduction condition, and global freshness counter are unchanged.

### Simulation argument

Compare one old call `c(a, g_list)` with one new call `c(a, g_tuple)` when the list and tuple contain the same sequence of assumption values, the remaining instruction stream is the same, and the global integer `k` is the same.

The two calls first compute the same `i(a)` and compare it against the same sequence of values. If a hypothesis matches, the old explicit return and the new fall-through after the loop both return `None`. Otherwise, they pop the same instruction, perform the same elimination check and goal replacement, and compute the same generated hypothesis `h`.

Any major subproof is checked recursively before the continuation in both programs. Its context is a snapshot of the caller's assumptions. By the induction hypothesis, the major subproof consumes the same packets, returns `None` on success, and leaves the same global counter. Thus the dispatcher receives the same result and computes the same `h`.

Both programs then decrement the shared global counter once. Both continue with the goal `i(a, [k])` and the old assumption sequence followed by `i(h, (m or len(a) == 2) and k)`. The old program enters a fresh tail-call frame for this continuation; the new program performs that same transition in its existing frame. Induction on a finite successful execution gives success preservation in both directions, abstracting away finite implementation resource limits.

### Evaluation order

The old tail call evaluates the opened goal before evaluating the new hypothesis. The loop computes the new hypothesis before the opened goal. This swap is safe here: `i` does not pop proof instructions, mutate `k`, mutate its input trees, or mutate assumptions. On ordinary JSON values and the program's fixed sentinels it is a pure partial operation reading the current `k`. If both computations succeed, their values are independent of order. If either raises an uncaught exception, the run does not accept. No user-defined Python objects with effectful operators can arrive through `json.load`.

### Why global freshness is preserved

The token program intentionally uses a global `k`. Successful major subproofs decrement that shared counter, and the caller observes the resulting value before allocating its next parameter. The loop transformation does not reset, save, or restore it. The same depth-first sequence of instructions therefore receives the same sequence of fresh integer names. This differs from the local-counter byte and AST profiles; their certificate conventions must not be mixed.

### Why tuples matter

Tuple augmentation rebinds a local name to a new tuple. It does not mutate the tuple seen by a suspended caller. This exactly replaces the old list-concatenation operation `g + [new_hypothesis]`, which also created a new context. The proof does not apply if the loop keeps a shared list and uses in-place `g += [...]`.

### Resource qualification

The loop uses fewer Python frames for long continuations. It can consequently accept a large valid certificate that the original implementation rejects through a stack limit. The claim is equivalence of successful abstract finite checking traces and of the represented canonical theorem set, not identical acceptance under every fixed machine resource limit. The broad-exception opening routine is inherited; this review does not convert it into a total, separately verified parser for arbitrary malformed JSON.

## 2. Byte and AST profiles: the retained neutral truth changes spelling

The only program change in these two files is the initial context:

- Byte profile: `[[]]` becomes `[0]`.
- AST profile: `([],)` becomes `(0,)`.

The corresponding certificate convention changes the neutral major field of an instruction from `[]` to `0`. Numerical zero inside terms is not recoded. Ordinary formula matrices and nonneutral major premises are not recoded.

### Why both retained objects are true

In the inherited administrative syntax, both the empty formula array and the scalar formula padding are neutral truths. The numeral `0` in a numerical term position is a different syntactic use from scalar padding in a formula position. At the root of a formula, `i(0)` returns `0` for every reachable floor `k <= 0`, while `i([])` returns `[]`.

A canonical equation has a nonempty two-child list at its root, and a canonical paired formula has a nonempty one-child list. Successful opening preserves that outer list and its arity. Neither can compare equal to scalar zero. Thus adding scalar padding `0` as a hypothesis does not make an equation, a paired formula, or the designated contradiction a hypothesis.

For example, the false equation `0 = S(0)` is `[0, [0]]`; it is not the scalar padding value `0`.

### Per-instruction simulation on canonical certificates

For an old neutral major `m = []`, the recursive major check closes immediately from the old initial context. For the new neutral major `m = 0`, it closes immediately from the new initial context. Both calls return `None`.

The remaining dispatcher uses those values in the same way:

- Both are false in a Boolean test.
- Both `m * 3` values are false, so the same computation or introduction branch is selected.
- Neither equals a constructed two-child equation major or three-child closure major.
- The introduction expression `(m or len(a) == 2) and k` has the same value.

All nonneutral canonical goals, matrices, computed equations, and supplied closures are unchanged. Recoding neutral major fields therefore preserves the checking trace of a canonical serialization. The mathematical soundness argument is even simpler: the only changed initial assumption remains a theorem, and all inference steps remain identical. Completeness uses the recoded canonical proof serialization.

### What is not being claimed

These programs do not accept exactly the same unmodified raw JSON files. A certificate using the old neutral spelling needs the stated recoding. An old standalone padding goal `[]` and a new standalone padding goal `0` are also different administrative inputs, although both represent truth.

The compact programs inherit their canonical-goal contract. This review does not claim that the one-byte change supplies a strict validator for all possible goals or certificates, nor that a formula-padding alias is an additional arithmetic axiom. It does not assert a trace-by-trace bijection for all malformed old input strings.

### Default values of the opening functions

The byte profile retains its function-valued default `t=c`; the AST profile retains `t=None`; the token profile retains `t=0j`. None is supplied by an ordinary JSON certificate. The opening functions do not call the function-valued sentinel as a theorem prover. If an invalid numerical opening needs such a sentinel as an actual term, the relevant arithmetic/order operation rejects it. The sentinel does not emerge as a successfully opened canonical numerical term. Changing the initial context does not change these facts, and the token loop does not change its sentinel at all.

Although Python compares `0j` equal to numerical zero, this is not an additional proof route: the sentinel cannot pass the ordering check required to emerge from `i` as a successfully opened term. The neutral byte/AST changes do not introduce the token sentinel into either of those programs.

## 3. Concrete failure of a shared mutable list context

The following certificate has two instructions followed by the false public goal `[0, [0]]`:

```json
[[[],0,[],[0]],[[[0,[0]]],0,0,0],[0,[0]]]
```

It was run against the reviewed token checker and against the exact mutation that replaces its tuple initial context with `[]` and its tuple extension with list in-place extension.

| Program | Exit status | Exact `ACCEPT` verdict |
| --- | ---: | --- |
| Reviewed tuple checker | 1 | No |
| Shared-list `g += [...]` mutation | 0 | Yes |

The correct checker terminates with `IndexError: pop from empty list`; the deliberately defective mutation prints `ACCEPT`.

The major subproof establishes a vacuous administrative closure of the constant false equation. Within that subproof, progress introduces the false equation as a temporary assumption and closes the same equation by hypothesis. In the correct implementation this assumption belongs only to the subproof and is discharged. A list mutated in place leaks that temporary assumption into the caller. The caller can then accept `0 = S(0)` directly. The tuple conversion is therefore a soundness requirement of the loop transformation, not a cosmetic implementation choice.

## 4. Why the discarded compound-progress shortcut changes the theory

The final reviewed files retain the atomic introduction condition. A discarded idea replaced that condition by a test of the generated hypothesis length. With ordinary `Q` semantics, this also permits progress introduction when the matrix itself has root `Q`.

Here is the resulting general induction principle. Let `P(n)` be any native formula, including quantified formulas, and let `gate(z,P)` be the inherited formula gate that is true at zero and equivalent to `P` at successors. Define:

`G(n) := Q_z gate(z, P(n))`.

The inherited numerical cases and logical reconstruction prove `G(n) <-> P(n)`. The forward direction specializes at successor zero and uses the gate equation. For the reverse direction, `P(n)` proves all successor gate instances, while the zero gate instance is a theorem; closure introduction supplies `G(n)`.

Suppose a retained context proves `P(0)` and proves `P(Sn)` from the local assumption `P(n)`. Transporting these derivations through the displayed equivalence gives `G(0)` and a derivation of `G(Sn)` from `G(n)`. Progress introduction at a `Q`-rooted matrix now produces the dummy-witness paired closure of `G`. `DE` supplies `Q_n G(n)`, and `QE`, applied to `G(0)`, yields `G(t)` for every term `t`. Eliminating the gate gives `P(t)`.

Thus the proposed unrestricted `Q`-matrix progress rule makes induction admissible for every formula represented by the inherited logical macros. This is a substantive strengthening to full formula induction, not a harmless removal of a parser branch. Restricting only final public goals to canonical `Eq/D` formulas does not solve it: the conclusion `P(t)` can itself be canonical. The final checkers avoid this change by retaining the atomic test.

## Review conclusion

The three final implementation changes have the stated sound success-preservation arguments, subject to the inherited canonical representation and resource qualifications. The token optimization needs immutable context extension; the neutral-truth optimization needs the corresponding neutral-major recoding. The review supports presenting these as modest checker reductions implementing the inherited presentation. It does not support claiming a new mathematical axiomatization, a new bi-interpretation proof, or a global minimum.
