# Independent review of the conditional direct-main lemmas

The two accepted Lean modules prove five **conditional model lemmas** for an
arbitrary `IΣ₁` model. They do not define or prove equivalence of a
90-operation graph.

In `DirectMainProjection`:

- `direct_parts_positive` defines `a=X*Y+Y`, `c=eta+Y*k` and `H=3+4*a`.
  From `U>0`, `Y≥8` and `k>0`, it proves
  `H*k < U*(X+a*c)+H*(U*G+R+1)`. It does not assume a decomposition of `G`.
- `cancel_direct_root` assumes `U>0` and the exact root balance
  `U*(X+a*c)+H*(U*G+R+1) = H*(R+1+U*W)+U*main`, and derives
  `X+a*c+H*G = main+H*W`.
- `direct_projection` additionally assumes `H>0`, `X<H`, `P<H`, and the
  exact Pell projection `main=P+a*c+H*t`; it concludes `X=P`.

The bound `X<H` cannot simply be dropped from the abstract projection
statement. For example, the natural values
`(U,X,a,c,H,G,R,W,main,P,t)=(1,3,0,0,2,1,0,1,3,1,1)` satisfy its other
listed hypotheses and both assumed equations, but have `X≠P` and `X≥H`.
This finite counterexample concerns the abstract lemma; it is not asserted
to arise from a candidate graph.

In `DirectMainNorm`, `oriented_scaled_norm` assumes `U>0`, `N<P`, and the
explicit equation `magnitude(P,N)²=U²*(1+C)`. It yields a positive `m` with
`P=N+U*m` and `m²=1+C`. `direct_main_orientation` specializes that result to
the displayed direct-main positive and negative parts, assuming `U>0`,
`Y≥8`, `k>0`, and its own explicit magnitude-squared norm equation. The
projection module supplies its strict orientation inequality. None of these
lemmas derives the norm, root balance, projection equation, bounds or a
positive inverse witness from a modified graph zero.

Both recorded author runs exited zero with empty stderr, no warnings and no
`sorryAx`. The three projection and two norm axiom reports contain only the
Lean metatheory axioms `[propext, Classical.choice, Quot.sound]`. Their source
snapshots, runner snapshots by hash, logs and objects match the receipts. The
norm run's first selected import is the exact object produced by the
projection run. The independent checker rehashed all 1,291 selected 92-halt
union files and symlink targets before and after, and reran the existing
read-only 92 halt review. The two sampled runs each saw at most one Lean
process, with minima of 18,508,148 KiB and 18,527,976 KiB available memory;
sampling is not continuous.

Run `python3 -I -S -B check.py` from this directory, or give its path from
another directory. Its captured execution exited zero with empty stderr; see
`observations/stdout`. The check needs the retained absolute `/tmp` providers
and objects, and did not start Lean.

This is an independent inspection of recorded single-author runs, not an
independent kernel replay. Complete historical source-to-object,
package-transitive and dynamic ancestry remain inherited. A proposed further
reduction still needs a concrete graph, graph-derived hypotheses, both
positive-witness directions and the remaining model/iPRA bindings.
