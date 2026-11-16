# First actual primary push for AX11H

This stage proves the exact result at the **first** exit of the primary
MP push. All results hold in PRA models whose arithmetic reduct satisfies
`IΣ₁`, with arbitrary model-valued register contents and clocks.

- `PA194PausedReach` supplies reachability and model-length concatenation
  for any unary primitive-recursive transition code. `PA194PausedSites`
  relates the primary push and field transition codes frozen at their
  respective exits to ordinary source steps at each earlier site.
- `PA194PausedDrain` proves the full arithmetic result of a model-length
  register drain under any code agreeing with the primary source below the
  specified boundary. The finite `SafeIncrements` premise certifies every
  visited loop instruction stays below that boundary. `PA194PausedTransfer`
  supplies the corresponding three-row transfer.
- `PA194PausedPair` proves the ten-row Cantor-pairing result under the same
  boundary discipline. `PA194PausedPush.push` composes these operations to
  reach the exact pushed file under the primary code frozen at site 3587.
- `PA194PausedFirstHit.first_actual_exit` transfers a reached frozen exit
  state to the least actual exit. `PA194FirstActualPush.first_actual_push`
  gives the full primary source state at the first exit and excludes all
  earlier exits. The [revised push proof](README-candidate.md) uses the
  first-hit result to identify the revised source output.

For a source replay, pass a colon-separated LEAN_PATH file from checked
provider stages containing the primary MP macro definitions and both
`PA194AX11HPushPaused` and `PA194AX11HFieldPaused`, including their verified
source/advance dependencies:

```sh
bash check-paused-primary.sh "$checked_provider_leanpath" "$new_output"
```

The output directory must be new. The script deduplicates the provider list,
puts its fresh output first, rebuilds all eight modules in dependency order,
and audits their reported axioms. The supplied checked providers furnish
the transitive dependencies.
