# Main-anchor multiplication and whole-graph sharing

This is a bounded search for a saving after a nonlocal, zero-preserving
transformation. It found **no reduction** in the family checked; it does not
prove the 65-operation equation optimal.

The independently reviewed main-norm argument says that every positive zero
has `N1=1`, and this follows solely from the unchanged `N1` and the
factorization `scaled_Ns=Δ*Ns` with positive `Δ`. For an intermediate `t`
that does not influence `N1` or `Δ`, replacing all its uses by `t*N1`
therefore preserves the zero set provided `scaled_Ns` remains divisible by
`Δ`. The checker builds such substitutions in the pinned graph, after
excluding the `N1` ancestors and the final product/aggregation gates. In
particular, the only affected strong-factor intermediates are `f2`,
`normalized_S`, `normalized_S2`, `scaled_f2` and `scaled_Ns`: scaling each
by an integer still leaves the scaled strong factor divisible by `Δ`.
`N1` itself remains an explicit final product factor. The other factor signs
are immaterial to this argument.

For each of the 37 eligible nodes, the checker inserts one `t*N1` gate and
reorders the DAG by dependency, giving 66 live gates. It then merges equal
fingerprints globally, including free leaves, using four samples over each
of three fixed prime fields at the four pinned port values. Even this
optimistic merging finds **no graph below 66**. Fingerprint collisions could
create false candidate savings, not conceal an actual identity; any survivor
would still require an exact proof. A positive control inserts `N0+0` and
confirms that the screen removes its redundant gate.

This is limited to the listed one-node multiplications and equality-based
common-subexpression merging on those circuits. It does not include affine
or algebraic rewrites beyond equality, other coefficients, transport
anchors, simultaneous changes, arbitrary circuits, or Lean/PDF semantics.
The search supplies no global lower bound.

Run without Lean:

```
python3 -I -S -B research/current14-carrier65-anchor-cse/check.py > /tmp/anchor-cse-result.json
cmp /tmp/anchor-cse-result.json research/current14-carrier65-anchor-cse/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier65-anchor-cse-independent/`.
