# Exploratory trace75 syntax and iPRA client

`Trace75BFSIPRA.lean` turns the two-way model result in
`Trace75BFSModelIff` into a `PositiveModelBridge` for
`TenPositiveTrace75.expression`, using the checked `Trace75BFSSyntax`
binding. It applies the native, standard and equality-only reference
adapters, with the mapped refutation negation and, for the latter two, the
selected translated consistency sentence. The four symbolic port equalities
remain explicit assumptions.

`Trace75BFSFixedIPRA.lean` specializes those equalities to the symbolic
direct-BFS ports, with native, standard and equality-only forms. Fixed
attempt01 was rejected: Lean exhausted its kernel
memory while proving three port projections directly at the large concrete
constants. Its failed log and receipt are preserved. The revised attempt02
uses generic port-projection lemmas.

The predecessor model iff joins graph-to-halt and halt-to-graph directions
obtained on different selected provider sets: the reverse join used an
old-first overlay with five known object differences from the fresh forward
union. The mixed-provider client below inherits these differences and the
eight BFS baseline overrides; a source-coherent join remains separate.

The exploratory author check `attempt01`, tool session 38768, exited 0 and
is reaped. Its six theorem reports all list `[propext, Classical.choice,
Quot.sound]`. The generated
`/tmp/trace75-bfs-ipra-tpj8nxvp/Trace75BFSIPRA.olean` has SHA-256
`75d2988695d143e0e26035d0d977197c4aa1c43d29b671f525c823ec323b6212`.
Source SHA-256 is `8f80194ef34f3031bb60b603cc8cd18c8e487083df85957fe846cc2b72a75f89`,
runner SHA-256 is `45c1e512f3307ebaabdf0ca0b86fd0213cb8b463a425f1d1c027dc1dbce84c7e`,
and terminal record SHA-256 is `ebdbbfa570fd7f15ddbfb8dd29c64fbe5600c357ea359c7789da17b72b2ccc73`.
The runner inventories its selected old-first namespace overlay, pins the
direct imported objects and records the inherited model-iff search path. It
does not authenticate the full transitive closure, resolve the known
producer-time differences, or constitute an independent Lean replay.
The [independent result audit](../../reviews/trace75-bfs-ipra-draft-result-independent/README.md)
checked the six reports, selected pins and stated boundary; it did not replay
Lean or resolve the inherited mixed-provider provenance.

Fixed author `fixed-attempt02`, tool session 46004, exited 0 and is reaped.
All five theorem reports list `[propext, Classical.choice, Quot.sound]`.
The object `/tmp/trace75-bfs-iprafixed-f0tc2i67/Trace75BFSFixedIPRA.olean`
has SHA-256 `a824917dde516e283a8046dd36e7e77df599cb997849e5c0ffb4eb88beccf909`.
Fixed source SHA-256 is `4a9f03a96a10bd2b52cb828506c4d89d97524e06e6180476547554a72262fa8d`,
runner SHA-256 is `6aec6a4c13a94ae410209ddbcf379627bab736598921a97219923879279ca622`,
and terminal record SHA-256 is `30ee9ad59a2ee1289d8bfe35cc5d5fb352ed86e886577d3c393e115435e457d9`.
This check inherits exactly the same mixed-provider and file-binding limits.
The [fixed-port independent result audit](../../reviews/trace75-bfs-fixed-ipra-result-independent/README.md)
checked the five reports and fixed symbolic tuple without replaying Lean or
resolving the inherited provider history.

`TenPositiveTrace75.expression` is a Lean expression; neither this client nor
the existing syntax evaluation theorem formally interprets an external JSON
file, displayed TeX or PDF. This is a separate graph from the maintained
14-variable equation.
