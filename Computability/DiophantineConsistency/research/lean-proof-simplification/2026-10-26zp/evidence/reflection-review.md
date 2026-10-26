# Reflection source formula: independent mathematical review

Source pin: `e1c8914bc7064d9a8e7c06171a18069a949badd0`.

Final novelty cutoff: `ae736b383e59c32c3c3f81910ef1c1197cbfbd44`.
The late 36-packet comparison is in `late-refresh.md`. Packet zh already
consolidates the terminal band; none of its endpoint savings is claimed here.

## Exact improvement

`CurrentReflectedGeometry2011.reflected_source` assumes an output offset
`h <= 1004` and coefficient position `p <= 985`. Its source equation is

```
c (b + h - (1005-p)) =
  if 1005 <= h+p then c (b + (h+p-1005)) else 0.
```

All index arithmetic on the left and inside `c` is in `ZMod (N*2011)`;
the two displayed subtractions inside casts are natural subtraction.
The assumptions on `c` imply it vanishes whenever its field residue is
greater than 1004; `b` is aligned modulo 2011.

The output bound can be removed entirely. It need not merely be weakened
to `h < 2011`. The coefficient-position bound can weaken to `p <= 1005`.

If `1005 <= h+p`, natural subtraction is exact at both occurrences and
the index identity is ordinary additive-group algebra. No upper bound on
`h` is used, even if it crosses many complete periods.

If `h+p < 1005`, this branch itself implies `h < 1005` and `p < 1005`.
Writing `d=1005-p`, one has `h<d<=1005`. The residue `r` of the source
satisfies `r+d = h (mod 2011)`. It must therefore be
`r=2011+h-d=1006+h+p`, which lies in 1006 through 2010. The support
hypothesis makes that source zero. Thus the old separate hypothesis
`h<=1004` is unnecessary in the only branch that uses support.

## What does not generalize

This is a source-identity improvement, not a stronger coefficient budget.
Keep the low-field premises of `source_le`,
`source_nonselector_coefficient`, `source_nonselector_coefficient_strict`,
`control_reflection_le`, `reflected_lt`, and carry-reset bounds. For
example, `source h e <= 984` is false for arbitrary large `h`.

Keep `p<=1005`: at `p=1006`, `h=0`, natural subtraction gives the old
left index `b`, whereas the proposed unguarded right index is `b+1`.
An origin-indicator word supplies a counterexample.

## Useful integration choices

1. Strengthen the existing source formula and finite-sum formula, updating
   their finitely many explicit callers to stop passing the unnecessary
   output-bound argument. This yields the smallest source.
2. Alternatively introduce `reflected_source_all` and `reflected_cell_all`,
   retaining the old declarations as wrappers. Charge the wrappers in any
   source-count comparison; their benefit is compatibility and a new
   high-field interface, not an automatic line reduction.

The complete reflected finite sum then has one normal form for low,
clause, high and multi-period output offsets. The new top-field clients
can specialize it instead of constructing a second reflected-source
calculus. Existing pure index equalities, such as `top_reflected_source`,
have fewer assumptions than an evaluation theorem and should not silently
be replaced by a support-dependent theorem with a narrower contract.

The old origin-zero proof can already specialize the original low-field
source formula at zero. That deletion is not incremental credit for the
new unbounded-offset theorem.

## Novelty boundary

The initial targeted searches across 28 proposal packets for `reflected_source`,
`reflected_cell`, generalizing the low band, and same-cell reflected
sources found no proposal for this stronger formula. One prior progress
note says the low-field theorem exists; it does not propose deleting its
offset bound. Previous field-residue interfaces and the aligned-cell
equivalence remain assumed available.

## Validation boundary

`lean/ReflectionAllFields.lean` is a standalone proof kernel using
the real numerical constants, the original modular-residue argument and
a weaker interval support premise. It includes low-interface wrappers,
a high-field corollary, finite-sum lifting, guard-boundary and one-cell
examples, and a counterexample to removing the coefficient-position
bound. Its compiler receipt, rather than this note, determines validation
status. Complete production-module rebuilding and all affected clients
are a separate integration task.

## Excluded adjacent direction

The earlier coordinate/control-update exploration has been dropped from the
final recommendations. Packet w provides the general band/time equivalence
and packet zd gives the actual numeric control-slot overwrite view and its
invariants. Related source-packing or point-update adapters are not counted
as additional methods. See `late-refresh.md` for the exact comparison.
