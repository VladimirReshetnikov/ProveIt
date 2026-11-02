# Independent review of the bounded local rewrite screen

The independent review actually exited 0 in session 24987; its receipt SHA-256
is `657a42c82964c7297f3a14926892047455a63d099332a67ee55848ccda6905cf`.
The original screen also actually exited 0 in session 4009, and an isolated
copy of its process wrapper exited 0 in session 35760, reproduced the exact
recorded receipt and refused a second overwrite. The independent reviewer
and wrapper reject optimized Python.

The checked family selects a single target row; permits earlier inputs,
literals 0–4 and earlier rows; replaces the target by an alias, one binary
`+`, `−` or `×` gate, or two such gates with the first temporary used by the
second; and leaves all other rows and the output fixed. The second gate may
use the temporary with an earlier node in either subtraction order, or use
the temporary twice. A candidate is relevant only if dead-row deletion then
strictly reduces the live gate count and the **target polynomial** is
identical over the integers with every input and all four ports symbolic.

For each sampled tuple, reduction modulo the chosen modulus is a ring
homomorphism. Thus any genuine integer-polynomial identity must produce the
same signature at all three tuples; this direction does not depend on random
samples being representative. The test never promotes a signature match into
an identity. It enumerates every first gate with unordered operands for the
commutative operations and both subtraction orders. A one-gate match is checked
directly. For a two-gate final addition or subtraction, the required temporary
signature is uniquely determined. For multiplication, componentwise inverses
recover it only when every component of the earlier operand is a unit. The
implementation fails closed on a zero component or a noninvertible nonzero
component, as independently tested using a composite modulus. Literal-zero
multiplication and `temp−temp` cannot match a target whose **whole signature**
is nonzero; the code checks precisely that the three-component signature is
not the all-zero tuple, not that every target component is nonzero. Reusing the
temporary twice for addition and multiplication is separately enumerated.

The independent reviewer exhaustively enumerated the concrete operations on
both toy controls without the implementation's inverse lookup, compared all
match and live-count totals, and verified the repeated-temporary positive
control. It also verified that an all-zero target signature, a nonunit divisor,
and an earlier signature with one zero component stop the scan instead of
being silently skipped. For the real pinned graphs there are zero sampled
aliases and zero strict candidates in every one-gate, two-gate and repeated-
temporary category. The reproduced non-strict match counts are respectively
87/1326/81 for the 87-gate graph and 86/1505/57 for the 86-gate graph.

This result excludes only the explicitly bounded, universal-port,
same-target-polynomial family. It does not exclude identities that hold only
after fixing the ports, graph-wide or downstream compensating substitutions,
three-or-more-gate changes, different constants or encodings, or equations
with merely equivalent zero sets. It is not a global minimality lower bound,
a Lean theorem, or a proof about actual ZFC consistency.
