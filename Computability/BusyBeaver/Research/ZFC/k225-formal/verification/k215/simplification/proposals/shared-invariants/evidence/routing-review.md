# Independent static review of the residual-port adapter

## Scope

This note reviews `src/BusyBeaver/ZFC/KResidualRouting215.lean` and the exact
definitions it uses in `KDecoderSuffix215`, `KSimPrefix`, `KDecoderPrefix215`,
`DecoderPaths`, `DecoderCertificate`, and `SiteCoverage`. The companion
`routing-review.json` records their source hashes at review time.

This is a source-level mathematical review. It performs no new compilation
and does not assert that the finite all-sites check has completed. The build
ledger is the authority for completed compiler and finite-check results.

**Finding:** no soundness gap or loss of continuation bits was found in the
reviewed adapter and its prefix/suffix attachment.

## Why the selected port is the certified port

`followRoles` consumes every bit of the prefix preceding the final leaf bit.
It follows internal role edges, rejecting a missing role or a premature
primitive edge. `followRoles_of_path` proves agreement with `RolePath` by
induction on that exact relation. An empty path returns its initial role;
the subsequent `portState` lookup still checks that the final role exists.

`portState_of_path` identifies the machine state of the final certified role.
The ignored block index on an internal edge is harmless at this stage: the
statement compares route selection, while the existing decoder prefix theorem
already supplies execution soundness of the certified blocks.

`checkLeafSuffix_of_routed` uses both complete-word equations
`word = pre ++ [bit]` and `word = pre' ++ [bit]`. Reversing and cancelling the
same final bit proves `pre = pre'`. Thus the computable selector and
`RoutedEntry` identify the same entire prefix and the same state. The proof
does not infer equality from a physical state or a short recent history.

## The full continuation remains present

The selected entry is exactly `leafPort pre bit q`, whose left segment is

```lean
pre.reverse.map .bit ++ [.bit true]
```

Its right side begins with the final `bit`, followed by the original gap
expression, header marker, and register box. Therefore every previously
consumed bit remains on the tape. The trailing true marker also prevents
zipper normalization from discarding the prefix as trailing blanks.

The suffix checker receives the original full `word` as its path argument.
`checkEdgeFrom` uses that word in `incPath`, `breakPath`, `continuePath`,
`stripPath`, the overflow conditions, and path-length bounds. The two
decrement branches retain their respective zero and nonzero register guards.
Neither equal selected states nor equal role suffixes merge these obligations.

## Coverage and composition remain explicit

`checkedLeafSuffixes_of_allSites` applies `allSites_sound` to the exact
`LeafAt KSource215.t215 word e` occurrence. With an empty reverse prefix,
the checked input is precisely `word`, with precisely the leaf's edge `e`.
The routed-port equality then converts that check into the required residual
contract. The unused `he : e = primitive op arg` parameter is harmless: the
all-sites premise already concerns that exact `e`, and the port-equality
proof only needs the routed state and complete prefix.

This theorem does not establish source/role correspondence by itself.
`KDecoderSuffix215.leaf_spec` obtains that correspondence and the actual
prefix execution from the existing `leaf_prefix` theorem. It then composes
the prefix and checked suffix. The source shape/totality premise and the
binding between the symbolic source tree and `p215` remain explicit in
`semantic_covered`.

For nonhalting source edges, `runToFrom` initializes the executor's progress
flag to false and its soundness conclusion is `Reach1`. Prefix composition
therefore preserves positive physical progress even when a particular
prefix is empty. Halt handling retains the separate terminal-state condition:
the residual establishes reachability of state 230, and the simulation uses
the no-transition hypothesis for that state.

## Limits of this review

The result is conditional on the stated finite all-sites equation and the
existing certified prefix, source binding, register-box contracts, and
terminal-row premise. No universal premise was discharged by this static
review. No new full machine-to-ZFC endpoint build or timing improvement is
claimed here.
