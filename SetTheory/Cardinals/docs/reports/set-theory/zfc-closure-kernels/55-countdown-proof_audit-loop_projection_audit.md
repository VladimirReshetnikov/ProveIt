# Audit of source-loop matrix projection

Reviewed implementation: `loop_experiments/affine_reference_loops.py`.
The executable audit is `check_loop_projection.py`; its recorded hashes and
results are in `loop_projection_audit.json`.

## Findings

The logical-to-physical mapping and difference-bound signs are correct.
The matrix rows use physical primary-register order. The source DBM uses
variable zero followed by logical registers R0 through R8. For each logical
register r, the implementation reads its physical entry bounds at
`PHYS[r]` and intersects them as `D[0,r+1]<=-lower` and
`D[r+1,0]<=upper`, followed by Floyd closure. The selected initial CD guard
has already been included in those entry bounds.

For finite bounds with `D[i,j]+D[j,i]=0`, the invariant proves
`x_i-x_j=D[i,j]`. Closure makes these equalities an equivalence relation.
Choosing the smallest member as each class representative ensures that
the class containing the distinguished zero variable is represented by
zero itself. The stored potential `D[i,representative]` therefore has the
right sign in `x_i=x_representative+potential_i`.

For physical output row t, the code subtracts identity using the coefficient
`A[t,PHYS[r]] - (PHYS[r]==t)`, groups coefficients by their logical equality
classes, and adds coefficient times potential to b_t. It rejects unless
each nonzero representative has total coefficient zero. The remaining
constant is exactly the required delta_t. The distinguished zero
representative contributes no variable term. This is direct substitution,
not a sampled or approximate identity test.

The binary oracle retains its coarser independent entry bounds. That is
safe: its binary run is proved for a superset of inputs, and the source
comparison uses the narrower intersection with the inductive DBM invariant.
Both source invariants include the initial state and are preserved under
actual source transitions. No raw equality is inferred from a mere bounded
difference.

The source loop update reads the old counter row before clearing it, uses
that same old row in every recipient update, and adds
`cycle_length*old_counter+1` to the source clock. Physical permutation,
zero-exit PC normalization, gap update, and the terminal CH event convention
are consistent with the independent source theorem.

## Independent controls

The audit compares all **1,433** driver loop records against the separate
direct-parser catalogue in `countdown_loops.py`. It checks the head, counter,
body, increment vector, positive-cycle length, cycle/exit gap contributions,
normalized exit PC, and exit source site.

It then constructs **48 deliberately nonidentity copy matrices** from exact
equalities in the independently checked original DBM certificate. For an
original fact `Ra-Rb=d`, the control replaces output Ra by initial Rb+7,
leaving every other physical row unchanged. The correct offset is exactly
`7-d` at the physical position of Ra. All controls return that vector.
They include 36 fixed-class equalities, six free-class equalities with
difference zero, and three each with differences +1 and -1. The latter
cases exercise the potential sign as well as the physical permutation.

These controls are not a rerun of a fold journal, a proof of concrete source
reachability, a binary-machine acceleration certificate, or a smaller-state
machine claim. The unbounded justification is the equality-substitution
argument above, together with the independently verified source invariant
and countdown induction.

## Positive-head overflow check

The initial reviewed loop enumerator counted body overflow and omitted an
explicit contribution from the head's positive CD. The independent direct
parser includes that contribution and proves it is zero in every one of
the 1,433 accepted pinned loops. Thus the reviewed results were sound for
this source. The final driver now includes that head contribution
explicitly, so the implemented cycle premise matches the general theorem.
The recorded executable audit was rerun after this hardening and checks
the complete cycle count.
