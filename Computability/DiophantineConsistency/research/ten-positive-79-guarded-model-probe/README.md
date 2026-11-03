# Guarded 79-to-80 model zero

`TenPositive79Guarded.guarded_to_old` is checked in Lean for every supported
IΣ₁ model and arbitrary natural ports. For a positive 79-row zero satisfying
the explicit guard `F+C<q`, the coordinate map replaces `C` with the positive
old coordinate `alpha=q−F−C` and yields a positive 80-row zero. It uses the
checked ring-level coordinate identity and proves the natural-subtraction to
difference-ring cast under that guard.

The accepted guarded run is `observations/guarded-attempt03/`, producing
`/tmp/mask79-guarded-qk46k3xo/Mask79Guarded.olean`, SHA-256
`3bba5208ea586c4451aaeb3b4e4056bd81db5489ca9d3ac32ac100c8b03358c0`.
The printed Lean axioms are `propext`, `Classical.choice`, and `Quot.sound`,
without `sorryAx`. Attempts 01 and 02 retain failed elaboration/linter
diagnostics. Source SHA-256 is
`0ac5e1fa65c72b9f66cdb5fbaa8488e2f9ea1fcefb303fa90ac619a596d002dd`;
runner SHA-256 is
`19163d69ee605a28255b86c32f48e7215851246de22c66fb84ce15d12015374c`.
The runner records and pins selected direct imports, with project-transitive,
historical source/object, package and dynamic limits inherited.

The guard is an explicit hypothesis, not a consequence of the 79 zero proved
here. This direction alone does not establish an unrestricted positive-zero
equivalence or a 79-operation iPRA endpoint. The candidate JSON-to-Lean
comparison is external, as recorded in the ring probe.
