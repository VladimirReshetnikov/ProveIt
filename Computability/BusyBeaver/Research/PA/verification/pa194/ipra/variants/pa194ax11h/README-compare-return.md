# AX11H comparison and return

`PA194AX11HSourceAt` gives the revised source's increment, decrement and
jump steps at arbitrary valid sites. `PA194AX11HCompareRows` kernel-checks
the delivered candidate instructions at sites 3642–3659, and
`PA194AX11HCandidateDrain` proves model-length drains of candidate registers.

`PA194AX11HCompare.compare` starts at site 3642 with an arbitrary file. It
reaches site 3652 when H=X and site 3659 otherwise, clearing H and X and
preserving all other coordinates. `PA194AX11HCompareReturn.compareAndReturn`
continues to dispatch site 25 with that exact cleared file when the input
satisfies `H = X → D = 0`. This premise is unnecessary in the unequal branch;
it allows the equal branch's success-copy to take its two zero tests directly.
Both results hold in every arithmetic `IΣ₁` model, including for nonstandard
register values and execution times. The caller must supply the premise; the
result does not claim the behavior of equal inputs with nonzero D.

For a source replay, pass a colon-separated LEAN_PATH file from checked
provider stages containing `PA194AX11HSource`, the generic paused reachability
and the primary source arithmetic/model lemmas:

```sh
bash check-compare-return.sh "$checked_provider_leanpath" "$new_output"
```

The output directory must be new. The script rebuilds the five modules in
dependency order and checks their axiom audits. Its checked provider stages
are inputs, not a rebuild of their complete transitive source closures.
