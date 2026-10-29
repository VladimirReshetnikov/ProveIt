# Exact PA-minus axiom shape for the marked invariant

`ParsonsBasePositive.paminus_prefix_sentence` proves that every actual
PA-minus axiom, including all equality axiom families, is a universal prefix
ending in a positive Boolean/existential formula over Σ₀ parts. The
`addEqOfLt` axiom requires an unbounded existential and is explicitly covered;
a stronger claim that every terminal part is Σ₀ would be false.

`negative_tree` shows that negating a terminal positive formula, after any
rewriting to an arithmetic proposition, gives the Tree descriptor used by the
counterexample recursion. Prefix certificates survive rewriting, opening a
negative universal base state at any witness, and eigenvariable shifting.
`terminal_tree` supplies the side certificate for same-height terminal base
reclassification.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. The six
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-base-positive-replay/FILES.json) has SHA-256
`d6a31567ef1cc0a7733a74337fd5aa9f77f105620ae07c1b5d9fada287c416fa`.
The direct StrictInvariant source hash
`e8f9c582dea832533e80f5a29d067f0cc507931a4f0347ec68c3c06719ad8f3d` and object
hash `6f3fb81ee258ac58d80ad88200fff07844174bf230a92964aeae73668d7672e2`
match its frozen provider. Earlier providers and Foundation/Mathlib are an
inherited boundary, not a fresh transitive source audit.

This certificate concerns actual PA-minus axioms and their opened instances;
it does not establish the global recursion or extend strict induction to all
Σ₁ predicates.

A third independent replay at `/tmp/parsons-base-positive-build-vq3n02ct`
passed with matching source, object and complete log hashes under the same
inherited-provider boundary.
