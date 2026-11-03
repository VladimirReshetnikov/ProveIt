# Trace75 direct-to-original word transfer

This client adapts the generic direct-BFS word transfer to the new
`Trace75BFSLocalWord.Word` declaration. It proves that any such word maps
through the model backward index map to an original-table `CompactLocalWord.Word`,
preserving N and s. The transfer explicitly assumes the input word; it does not
itself assume a graph zero. The author check passed with tool-observed outer
exit 0 and child, Lean and header exits 0. Independent post-audit passed in
`reviews/trace75-bfs-model-word-transfer-result-independent/`.

The runner checks eighteen accepted regular client roots, the 1,977-object
fresh union, 80 outside providers and three captured BFS subtrees with 209,
79 and 4 project objects, including companions. Exact log policy requires four
named axiom reports; read-only preflight and 22 controls passed, including
rejection of each missing report. `observations/attempt01/result.json` has
SHA-256 `b87fe4e0896496d9e38a45325fbb3df732f0afda93793e47125e6a259cedf81a`;
`observations/outer-attempt01/terminal.json` has SHA-256
`5935aa3cdc7ff7d31f237a612d8b93651f351de2bd4cfe171c225925bef147bc`.
The object `/tmp/trace75-bfs-wordtransfer-dageoevm/Trace75BFSModelWordTransfer.olean`
has SHA-256 `083ef679ae47d02e61a292d127e1f76b1a2b6670e190b0371a8381e123c0992a`.
Historical unrebuilt-source, package/dynamic ancestry and external coefficient
file binding remain outside this check; it is not a halt or iPRA theorem.
