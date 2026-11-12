# Implementation routes investigated

This is a search note, not a claim of a simpler complete axiomatization.

## Local fresh-coordinate supply

Move the common opener inside `c`, capture a local `k=-len(g)`, and retain
`k-=1` only after validating the incoming goal and witness. Every continuation
adds exactly one context item, so that scope size is a natural local supply.
This removes the module-level mutable supply and avoids leakage of supply
state from a checked major proof. A formal equivalence requires alpha-renaming
certificates: existing certificates name globally numbered eigenparameters,
whereas the new experiment reuses names in disjoint scopes.

The executable transformation is `local_scope_checker.py`. No claim of full
malformed-input equivalence or independent soundness certification is made.
It was rejected as the main candidate because it increases all three primary
metrics (684 to 685 normalized bytes, 277 to 279 tokens, 317 to 322 AST nodes).
Its maximum-compression gzip decreases from 403 to 400 bytes; that is only the
requested informational metric and is not a reason to choose it.

Setting the floor to `~len(g)` *before* checking the incoming witness would be
unsafe: it would make the newly reserved eigenparameter available to that
witness. The experimental version retains the two-phase validate/allocate
order.

## Removing literal-equation case introduction

Replacing the tail mode selector by `k if len(h)<3 else 0` looks attractive.
It removes the case mode for literal-equation matrices, keeping only progress.
This is not justified: the native closure has meaning
`B(0) -> forall y B(y)`, which can hold vacuously when `B(0)` is false even if
`B(k) -> B(S(k))` fails. A language-restriction and full logical round-trip
proof would be necessary; no such proof was obtained. This is not an accepted
size improvement.

## Other routes rejected before coding

- Complete normalization in the common opening traversal removes computation
  leaves, but adds a recursive reducer, constructor discrimination, and a
  strong-normalization argument. It is not a measured improvement.
- Full conclusion synthesis can remove endpoint comparisons but introduces a
  no-eigenparameter-escape check at existential elimination. It was not shown
  to reduce the kernel.
- Eager decomposition of paired assumptions removes some explicit DE packets,
  but progress-introduction/DE pairs implement induction and cannot simply be
  normalized away. A direct atomic-induction rule must be restored.

No novel breakthrough or kernel below the corpus frontier was established by
these experiments.
