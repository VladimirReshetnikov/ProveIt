# Trace75 direct-BFS local-word client

`Trace75BFSLocalWord.graph_local_word` adapts the 80-row local-word construction
to trace75. Under exact symbolic direct-BFS ports and a positive trace75 zero it proves
one common N, W and s, a represented row and a local word satisfying the
bound, forbidden tile, origin and horizontal/vertical matching conditions.
The independently selected lengths are identified through the common radix.
Its `Trace75BFSLocalWord.Word` is a new structure declaration; later clients
must explicitly bind it to any previously named word type. The author check
passed with tool-observed outer exit 0 and child, Lean and header exits 0.
Independent post-audit passed in `reviews/trace75-bfs-local-word-result-independent/`.

The runner checks seventeen accepted regular client roots, the 1,977-object
fresh union, 80 outside providers and the captured BFS `CompactLocalWord`
subtree (334 project objects), including companions. Exact log policy requires
both named axiom reports; read-only preflight and 20 controls passed, including
rejection of either missing report. `observations/attempt01/result.json` has
SHA-256 `08fe37cf70ecbcbd6ec88d565322be49a7be4f10c41dad0fb2df5614a171c4b3`;
`observations/outer-attempt01/terminal.json` has SHA-256
`f4e93b1bbe068139c7f60a53e67f2a3308a27e3bc5b25952ce499ee6a1203d88`.
The object `/tmp/trace75-bfs-localword-akvztvhn/Trace75BFSLocalWord.olean`
has SHA-256 `71466a6f5a3a7e9fcbf7963b2d9430952e7f81cfd65b023f17fc09bfb78ecbda`.
Historical unrebuilt-source, package/dynamic ancestry and external coefficient
file binding remain outside this check; it is not a halt or iPRA theorem.
