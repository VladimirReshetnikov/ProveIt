# Invert an internal Foundation universal-rule derivation

`all_inversion` starts with an arbitrary internal Foundation `Derivation T d`
whose fixed candidate-PRA tag decoder returns `4`. It analyzes all ten
Foundation derivation forms and proves that `d` is an `allIntro s p dp` node,
that `s` is an `IsFormulaSet`, and that the universal principal formula and
exact internal premise `DerivationOf` have the required properties. It applies
to every candidate-PRA model with an IΣ₁ arithmetic reduct and a Foundation
Δ₁ theory `T`, including nonstandard proof and formula codes.

`all_graph_from_derivation` composes this inversion with the previous
parameter-free Σ₁ choice graph. For any member `q` of the decoded child
sequent and any output `y` of that graph, it proves the zero distinguished
formula case or the successor-coded shifted-preimage case, using the decoded
parent fields. No external standard list of the internal sequent is assumed.

This is specific to the universal-introduction rule and does not provide a
complete recursive traversal of internal Foundation derivations, a finite
candidate-PRA code for free substitution, full compiler correctness,
PA/source-calculus calibration, or a machine halting reduction.

The final module passed a fresh Lean 4.32 ordered-suffix rebuild against the
fresh universal-choice graph and earlier checked suffixes plus audited project
and Foundation objects. The printed theorem axiom dependencies are
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. Its full nested
replay below is pending; the source-shift dependency has passed its own full
replay.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-all-inversion/check.sh
```

The script rebuilds its prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

An independent suffix replay recompiled this inversion and graph composition
against separately checked universal-choice and sequent-search objects, reusing
the remaining prerequisite overlays. Its reported axioms did not include `sorryAx`.
