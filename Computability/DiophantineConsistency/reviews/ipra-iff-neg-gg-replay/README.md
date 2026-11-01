# Unpacking GG-translated equivalence and negation

`IPRAIffGG` proves the Gödel–Gentzen image of an iff is intuitionistically
equivalent to an iff of images, both for propositions and within arbitrary
intuitionistic theories. It supplies an endpoint-shaped consequence: from a
proof of `(φ ↔ ∼ψ)ᴺ`, the theory proves `φᴺ ↔ ∼ψᴺ`.

The result retains `∼ψᴺ`, so relating it to an ordinary intuitionistic
consistency statement requires a separate theorem. No equation equivalence
or classical-to-native axiom transfer is asserted here. The independent
native-induction parent was source-rebuilt coherently; its external transitive
ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-iff-neg-gg-replay/replay.py`.

Author PASS; all six axiom reports were separately parsed and contained
only `propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; source/object/full-log rows match author, and all six
axiom reports contain only the standard Lean trio.
