# Native binary relation transport

For any binary relation symbol in the expanded PR language,
`relation_native` proves in the existing native iPRA theory the curried
intuitionistic sentence `∀x y u v, x=u → y=v → R(x,y) → R(u,v)`. It uses
two actual native Leibniz equality instances and no equality decidability.
Both PR-language relation symbols are binary. The actual Foundation relation
congruence axiom has a conjunction-shaped antecedent; deriving its GG image
requires a separate checked logical adapter. Function congruence and the
consistency bridge likewise remain open. External transitive ancestry is
inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-binary-relation-native-replay/replay.py`.

Author PASS; all five axiom reports were separately parsed and contained
only `propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; source/object/full-log rows match author and all
five axiom reports contain only the standard Lean trio.
