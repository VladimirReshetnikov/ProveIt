# Spatial cell cycle: author receipt

The complete new main source and focused checks were read before their
respective fresh builds. This is an author receipt, not an independent peer
review. No frozen source, existing documentation, or umbrella file was
edited, and no git mutation command was run.

## Frozen source

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentCellCycle2011.lean` | 171 | `874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d` |
| `Lean/DiophantineConsistency/CurrentCellCycle2011Checks.lean` | 73 | `57f9344d572c115acdf5006d57c6d8874ed66c0b874c12bfe34966192585f6cb` |

The main source imports only `CurrentCellTranslation2011`, SHA-256
`c3e9811e9b5c60c8ed740b58277ed40569108f888347ffcbb84169ba31b5685d`.
The checks import only the new main module. Both disable asynchronous
elaboration and use a maximum recursion depth of10000.

## Mathematical scope

The only ambient hypothesis is `[NeZero (N*2011)]`. In particular,
`cellCount_pos` derives `0<N`, and no hypothesis requires `N≥2`.
There are no native-word, mask, tile, occupation, or target-equivalence
premises.

The existing aligned subtype is
`Cell N = {b : ZMod (N*2011) // b.val%2011=0}`. The new `next` and
`previous` are inverse equivalences of this exact type, with underlying
values `b+2011` and `b-2011`. They reuse the already proved whole-cell
translation equivalence at shift2011, without changing its coordinate.

The canonical index is the least nonnegative field base divided by2011.
`index_lt` proves this index is less thanN, and `index_mul` reconstructs
the original least representative exactly. `coe_iterate_next` gives the
full cyclic group value `b+j*2011` for every naturalj, without limitingj
to the first period. Hence:

- `iterate_index_zero` and `reachable_from_zero` reach every cell from zero.
- `iterate_period` returns every base to itself afterN successor steps.
- `reachable_from` reaches any target from any source in fewer thanN steps,
  using the aligned cyclic difference cell.
- `propagate P hzero hnext` proves `∀b,P b` for any predicateP true at zero
  and preserved by successor. `propagate_from` permits any initial base.

`coordinateFin : Cell N ≃ Fin N` uses that same canonical index, with
inverse given by successor iteration from zero. Composing it with the
standard finite-ring equivalence yields `coordinate : Cell N ≃ ZMod N`.
`coordinate_val` explicitly identifies its least representative with the
physical quotient index; this is not merely an arbitrary finite bijection.

The single-cell successor and predecessor are both the identity. Focused
checks cover this case, exact cyclic addition/subtraction, both inverse
identities, bounded reachability, periodN, propagation from zero and an
arbitrary base, and both coordinate directions.

This is the generic spatial-cycle step needed for future occupation
propagation. It does not assert occupation or any tiling conclusion itself.

## Builds and axiom audit

From the repository root, these final commands exited0 sequentially:

```sh
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellCycle2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellCycle2011.lean > /tmp/current-cell-cycle-stage2.log 2>&1
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellCycle2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellCycle2011Checks.lean > /tmp/current-cell-cycle-checks-stage1.log 2>&1
```

The main log is empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The check log has SHA-256
`6f24034dcfb6d5bdd5ab61356a0cac5565f498e768dc148e008b44a6b1e978d4`.
Its16 axiom reports contain only subsets of `propext`, `Classical.choice`,
and `Quot.sound`.

The first main run checked the general cycle, propagation and coordinate
proofs, but reached the default elaborator recursion limit while resolving
`NeZero (1*2011)` for the two concrete singleton endpoints. The final source
raises that limit and removes an unused section hypothesis from `index_mul`;
it does not weaken any mathematical statement. Both final source files
were built under the6000MB memory cap with one Lean worker. These runs
rebuilt the new modules against the existing dependency objects; they were
not fresh rebuilds of the entire import closure.

Neither new source introduces `sorry`, `admit`, an axiom, `native_decide`,
or an executable finite certificate.
