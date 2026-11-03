# Trace75 main ordinate exceeds the index-three ordinate

`Trace75MainSize.graph_main_size` is Lean checked in every `IΣ₁` model. For
arbitrary natural ports with `2≤beta` in the model and ten positive witnesses
at which the Lean trace75 ring value is zero, it returns the same r,j,I
witnesses from `graph_main_index_ge_five` with r≥5, r odd, r<j, the main
ordinate and strong coordinate equations, c²∣I, and

```
4*Delta + 3 < c.
```

Here the local `A=X*Y+Y`, and `4*Delta+3` is proved equal to
`ycoord 3 (A-1)` by the exact third-ordinate formula; monotonicity and r≥5
give the strict inequality. The theorem is a necessary consequence of a zero;
it is not an auxiliary-index bound, a halt/iPRA theorem, a trace74 guard, or
a Lean binding of external coefficient/JSON bytes. Its beta assumption is
explicit rather than fixed-symbolic-port discharge.

Accepted source `Trace75MainSize.lean` SHA-256
`a6e4d0eb9cec01195d2f9184388a47fc2d15894e13fcd25aa00e5901bb3c1167`;
`run-mainsize-v2.py` accepted `observations/mainsize-attempt02/`, object
`/tmp/trace75-mainsize-a06e2di1/Trace75MainSize.olean` SHA-256
`617754ec439b63ae5ab242ce2c161d0b500b3925220b1a790ac6f6c151d6555f`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The prior failed namespace-resolution attempt and source are retained.
Selected direct providers are pinned; project/package transitive, historical
source/object and dynamic ancestry remain inherited.
