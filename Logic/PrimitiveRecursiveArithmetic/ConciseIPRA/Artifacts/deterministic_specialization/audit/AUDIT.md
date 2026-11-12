# Deterministic clause use: independent operational audit

The checker is the zero-normal, uniform-successor-Step clause presentation
with contexts stored newest first. `['u', index, premise]` specializes the
selected clause at `S(0)` when `index == 0`, and at the newest free level
`-scope` when `index > 0`. The index must be an exact integer in range.
Every legal positive index implies that at least two clauses and hence
at least two fresh levels have already been allocated.

## Eliminating redundant scope state

The standalone public interface checks a closed formula from the empty
context. Every reachable call `derive(proof, context, scope)` satisfies

    scope == len(context).

Proof is induction on the dynamic call tree. The initial call has scope
zero and empty context. Use, Step, and the major premise of elimination
recur with unchanged context and scope. Introduction and elimination each
add exactly one clause and increment scope exactly once for their branch.
There is no certificate instruction that inserts a context entry without
allocating a fresh level, or allocates a fresh level without an entry.
No rule mutates an existing context list.

Consequently `derive` can omit the scope argument and compute
`scope = len(context)` once on entry. In particular, the newest parameter
is `-len(context)` and the next fresh parameter is `-len(context)-1`.
All scope tests, all opening operations, and the deterministic target
selection therefore receive exactly their previous values.

This statement is about the complete public checker rooted at empty
context. The three-argument helper can also be called directly by Python
code with an arbitrary open context and an independent scope. Equivalence
for that non-public API requires `scope == len(context)` as a precondition;
it is not claimed for arbitrary external helper calls.

## Controlled measurements

The unrestricted comparison is the pinned incoming `uniform_step`
checker, with only context order changed to newest first. Reversing its
clause indices at each proof depth is an exact certificate translation.
The source count is unchanged by the context-order switch; gzip changes
by one byte. Module docstrings are omitted, and the entire remaining
module is normalized by `ast.unparse` plus one LF under CPython 3.12.14.

| Program | Bytes | Tokens | AST nodes | gzip9 |
| --- | ---: | ---: | ---: | ---: |
| Unrestricted Use, explicit scope | 2950 | 829 | 902 | 1004 |
| Deterministic Use, explicit scope | 2938 | 829 | 903 | 999 |
| Unrestricted Use, scope from context | 2926 | 819 | 895 | 1000 |
| Deterministic Use, scope from context | 2914 | 819 | 896 | 997 |

The mathematical target restriction contributes 12 bytes, leaves the
token count unchanged, and adds one AST node. The independent operational
invariant contributes 24 bytes, 10 tokens and 7 AST nodes to either
calculus. The combined program improves on the explicit unrestricted
control by 36 bytes, 10 tokens and 6 AST nodes. These are matched local
measurements, not a repository-wide minimum claim. Gzip is informational.

## Independent finite validation

Run `python3 verify.py` in this directory. The audit uses only its frozen
JSON fixture directory and the four standalone checker files. The frozen
corpus comes from the pinned upstream test builders and independent
higher-rank generators; regeneration is not needed to run the audit.

Executed results:

- 209 fixed certificates: 92 unrestricted positive proofs, 93
  deterministic positive proofs, and 24 negative deterministic proofs.
- 956 complete command-line runs across explicit and implicit scope and
  ordinary and optimized Python, including malformed JSON.
- 25047 observed calls of an explicit-scope `derive`, all satisfying the
  invariant.
- 1200 proof-tree mutations with no explicit/implicit acceptance mismatch.
  Fourteen mutations still expressed valid proofs and were accepted by both.
- 93 changed conclusions `0 = S(0)`, all rejected.
- 157 accepted closed equations independently evaluated in the natural
  numbers, with equal values on both sides.

The dispatch-sensitive positive proof `older_clause_uses_latest_parameter`
uses clause index 1 at free level -2 after two branch extensions. Its
arithmetic continuation requires that exact parameter. Changing the Use
index to 0 makes the proof fail. The `nested_binder_capture_avoiding`
example substitutes beneath two nested iterator binders; changing a bound
index so that the substitution is captured makes it fail. Other negatives
cover invalid proof shapes, incorrect Step predecessors, raw zero-counter
iterators, variable escapes, malformed indices including Boolean aliases,
incorrect clause antecedents, and malformed public goals.

These checks supplement the operational invariant and the separate
mathematical completeness proof. They do not constitute a proof-assistant
formalization or a semantic decision procedure for all D formulas.
