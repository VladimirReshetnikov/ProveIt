# Negative atoms and the restricted Lukasiewicz row: a limited obstruction

This note does **not** establish or refute equiconsistency of a proposed
native set theory. It records a core counterexample to one intermediate
shortcut, and identifies what remains possible.

Suppose the full Lukasiewicz row

```
((c -> u) -> a) -> ((a -> c) -> (b -> c))
```

is restricted to `u=F`. Replacing both named atomic predicates by relative
negations can eliminate the non-Boolean atomic colors of the previously
published HC countermodel. It does not automatically make all formulas
built from those atoms classical.

Take values `0,1,2,3`, bottom `F=0`, designated value `3`, and implication

| -> | 0 | 1 | 2 | 3 |
| --- | --- | --- | --- | --- |
| 0 | 3 | 3 | 3 | 3 |
| 1 | 3 | 3 | 0 | 3 |
| 2 | 3 | 3 | 3 | 3 |
| 3 | 0 | 0 | 1 | 3 |

For a nonempty set S of values in a quantifier fiber, define `Q(S)=3` if
`S={3}`, `Q(S)=2` if `0` belongs to S, and `Q(S)=0` otherwise. In particular
the unary operation on constant fibers is `(2,0,0,3)`.

This matrix validates MP, theorem generalization, identity, explosion,
the restricted Lukasiewicz row, normal quantifier distribution, commuting
coordinate quantifiers, and the original rho6. The accompanying checker
verifies all 65,535 nonempty sets of value pairs for distribution and all
15 nonempty value sets for rho6. These powerset checks cover fibers of
arbitrary cardinality because the value set is finite. For commutation,
either order of the two coordinate quantifiers is designated exactly when
every entry is designated. Both orders have values in `{0,2,3}`, and on
that set equality of designatedness implies a designated implication.

Every relative negation has value 0 or 3. Nevertheless, `Q({0})=2` and
`3 -> 2 = 1`, so the implication/quantifier closure of negative atoms can
contain all four values. The unrestricted Lukasiewicz row has value 0
at `(a,b,c,u)=(0,3,1,2)`. Thus unrestricted classical closure cannot follow
merely from the observation that all starting atoms are negative.

This example leaves a stronger translation open. Double negation maps a
value to 3 exactly when it was designated, and to 0 otherwise. Implication
on the values 0 and 3 is ordinary Boolean implication; double negation
after quantification implements ordinary universal truth. A translation
that stabilizes every connective or quantifier can therefore escape the
example. Furthermore, with such Boolean matrix codes, the full native
seed-K scheme still expresses the ordinary set-theoretic closure principle.
No model of every native K instance is supplied here. In particular, the
example is not a substitute for a calibration or a full-theory countermodel.

The separate bounded condensed-detachment searches are exploratory only.
Their failure to find a proof is not an impossibility result, and they
have not been used as premises in any positive theorem in this packet.
