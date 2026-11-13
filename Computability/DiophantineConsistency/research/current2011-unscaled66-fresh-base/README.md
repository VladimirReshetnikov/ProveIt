# Fresh current14-base model and iPRA client for the integer 66/138 graph

The [Lean client](Current2011Unscaled66Fresh.lean) checks the 66-row
integer-leaf expression at the current2011 ports. It proves its ring
evaluation, the exact identity `Carrier65 = Delta * unscaled`, and, in every
model of IΣ₁, the equivalence of its positive-shifted zero condition with that
of the maintained current14 expression at the same valuation. It uses the
fresh-base `FreshModel106` proof of beta positivity, shifted-coordinate
positivity and the 65-row evaluation, then inlines the generic no-zero bridge
and applies the existing iPRA transfer. Its no-premise
`standard_equivalence138` states that standard iPRA derives the equivalence
with intuitionistic negation of the mapped native ZFC-refutation predicate.
It proves neither side separately.

The [row audit](audit-rows.py) compares the complete `expressionAt` definition
byte-for-byte with the independently audited historical 66-row client; its
recorded output is [row-audit.txt](row-audit.txt). The [original graph and
degree audit](../current2011-unscaled66/README.md) remains an external finite
certificate: this Lean client does not prove a `totalDegree` theorem, parse
the graph/TeX/PDF, or identify coefficient bytes with Lean ports.

[Attempt 01](attempt01/) passed. Both the dependency query and Lean compile
exited 0; outer session 37489 also exited 0. The compile took 3.253 seconds,
produced no warnings or errors, and its five reports contain only `propext`,
`Classical.choice`, and `Quot.sound`; none contain `sorryAx`. It used one
thread, `-M2800`, nice 19, idle I/O and a 180-second foreground timeout; there
was no automatic group-RSS or host-memory stop. The runner checks the original
fresh-base client, the sixteen extension outputs and their direct guards, the
source/base preflight before and after, and 80 direct dependency
companion/shadow slots before and after. Both preflights match the pinned
result. The client imports the successful `FreshModel106` object, not the
historical `ModelCarrierCurrent` or `HAExpressionSameZero` modules.

The source SHA-256 is
`9b323e56feabc402d02c49af27192013d0b9faf74631ead83f3cf7a0b51b0f7a`, the
captured state SHA-256 is
`900a60a742590560b4d95cbba945d22028e508c02964abde9f55a0b1a68b58a2`, and the
temporary object `/tmp/current2011-unscaled66-fresh-base-20261105/Current2011Unscaled66Fresh.olean`
has SHA-256 `43de05d18c2854a224ebcd01c560cb5327752118ee08164277f38e7611a01b00`.
This is a client check on the same base, not a new independent base rebuild;
the base and package-transitive, dynamic, toolchain and between-observation
ancestry limitations remain as stated in the
[fresh-base model packet](../normalized106-fresh-base-model-build/README.md).
