# Internal universal-premise choice as a Σ₁ graph

`choiceGraph` is a fixed parameter-free Σ₁ arithmetic formula. On inputs
`(derivationNode, target)` it composes the graph of the fixed candidate-PRA
body decoder, Foundation's actual `freeGraph L`, and the graph of the fixed
candidate-PRA universal-premise selector. `choice_defined` proves it represents
the resulting total operation throughout every candidate-PRA model with an IΣ₁
arithmetic reduct, including nonstandard inputs; `choice_graph_total` gives
existence of a graph output in each such model.

For an actual `allIntro s p dp` node, a Foundation Δ₁ theory `T`, an internal
`DerivationOf T dp (insert (free L p) (setShift L s))`, and a member `q` of that
premise, `all_choice_graph` proves that any graph output is `0` when `q` is the
distinguished free formula, or is a successor `u+1` where `u ∈ s` and
`shift L u = q`. The previously proved selector returns zero in an overlap.
No assumption that an external standard list represents a nonstandard sequent
is used.

This is a Σ₁ graph, **not** a fixed finite candidate-PRA code for the entire
operation: such a code would require a separately proved finite code for
Foundation's free substitution. Complete coded derivation traversal, proof
compiler correctness, PA/source-calculus calibration, and a machine halting
reduction also remain open.

The final module passed a fresh Lean 4.32 suffix rebuild against freshly
rebuilt field, choice, preimage, set-search and source-shift suffixes plus the
audited project and Foundation objects. Its printed theorem axioms are
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The full nested
replay below is pending; the source-shift dependency has passed its own full
replay.

From the repository root, using matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-all-choice-graph/check.sh
```

The script rebuilds its prerequisite chain under `/dev/shm` by default; set
`TMPDIR` to use another suitable temporary directory.

An independent suffix replay recompiled the choice-graph module against
separately checked node-field and sequent-search objects, reusing the other
prerequisite overlays. Its reported axioms did not include `sorryAx`.
