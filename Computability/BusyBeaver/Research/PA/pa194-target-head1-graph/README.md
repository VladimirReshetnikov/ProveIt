# Uniform Σ₁ graph for a target h1 leaf certificate

`certificateGraph` is an explicit, fixed, parameter-free Σ₁ arithmetic formula
with inputs `(certificate, theorem)`. `certificate_graph_correct` proves that,
in every candidate-PRA model whose arithmetic reduct satisfies IΣ₁, it holds
exactly for the `Head1Certificate` relation from `pa194-target-head1`. The
certificate is the independently chosen Foundation pair `pair 2 (pair a b)`;
the theorem number is the machine's h1 formula constructed using triangular
Cantor pairing. Inputs may be nonstandard.

The graph is obtained from the fixed finite h1 checker by substituting the
successor of the theorem into its output position. The standard binding of the
formula generator to PA194's actual h1 axiom is separately proved in
`pa194-target-head1-standard`.

Only the h1 leaf schema is covered. This is not the upstream multi-rule checker
or a complete target proof relation; modus ponens, generalization, other leaves,
source proof compilation and the PA/machine reduction remain open.

The final module passed a fresh Lean 4.32 suffix rebuild against the retained
h1 checker and its earlier suffix dependencies plus the audited project and
Foundation overlays. Its printed theorem axioms are `[propext,
Classical.choice, Quot.sound]`, without `sorryAx`. The full nested replay below
is pending.

From the repository root, using matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-target-head1-graph/check.sh
```

The script rebuilds its prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

An independent suffix replay recompiled this graph module against the
separately checked h1 checker and its existing prerequisite overlays. The
reported theorem axioms did not include `sorryAx`.
