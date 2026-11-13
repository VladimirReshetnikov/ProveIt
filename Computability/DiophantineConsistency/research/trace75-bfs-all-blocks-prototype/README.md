# Trace75 direct-BFS all-blocks client

`Trace75BFSAllBlocks.graph_all_blocks` adapts the 80-row cyclic orbit induction
to trace75. Under exact symbolic direct-BFS ports and a positive trace75 zero
it proves one common positive N with the radix identity and every block selected.
The author check passed with tool-observed outer exit 0 and child, Lean and
header exits 0. Independent post-audit passed in
`reviews/trace75-bfs-all-blocks-result-independent/`.

The runner checks twelve accepted regular client roots, the 1,977-object
fresh union, 80 outside providers and the captured BFS `InternalOrbit` subtree
(299 project objects), including companions. Read-only preflight and 18
controls passed. `observations/attempt01/result.json` has SHA-256
`9f4f627f52e667075b6b025b2b99b6e24920f72b74169e54b3f2e2a2dee4a6b2`;
`observations/outer-attempt01/terminal.json` has SHA-256
`9fac2b6f25ded83af8d23bf78b85634670d41a636d21c31c568235b0a036ac3f`.
The object `/tmp/trace75-bfs-allblocks-9b9tohp3/Trace75BFSAllBlocks.olean`
has SHA-256 `4e8944a240915156fafabb828f2fcdca76393bf3a895532e19f36b90a02a1a5f`.
Historical
unrebuilt-source, package/dynamic ancestry and external coefficient-file
binding remain outside this check; this is not a machine-halt or iPRA theorem.
