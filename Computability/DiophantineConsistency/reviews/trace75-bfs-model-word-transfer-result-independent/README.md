# Independent result review: trace75 BFS model-word transfer

**PASS.** The captured author result for `Trace75BFSModelWordTransfer` has
child, Lean and serialized-header exits 0, four exact named axiom reports,
and matching source, output, logs, pins and four direct imports. The author
reports actual outer tool exit 0; the wrapper records child exit 0 and stable
hashes. This review did not replay Lean.

`transfer` explicitly takes the distinct `Trace75BFSLocalWord.Word b N s`
and returns `CompactLocalWord.Word (fun j => back (b j)) N s`. The proof
preserves the same N and s and uses the inverse row map and horizontal and
vertical edge reflection; bounded entries, the forbidden tile and origin
are checked. The theorem assumes the input word and does not assert a graph
zero or a represented output word. It is not a halt or iPRA theorem and does
not bind external coefficient files.

The accepted result SHA-256 is
`b87fe4e0896496d9e38a45325fbb3df732f0afda93793e47125e6a259cedf81a`,
and its outer receipt SHA-256 is
`5935aa3cdc7ff7d31f237a612d8b93651f351de2bd4cfe171c225925bef147bc`.
The regular output
`/tmp/trace75-bfs-wordtransfer-dageoevm/Trace75BFSModelWordTransfer.olean`
has SHA-256 `083ef679ae47d02e61a292d127e1f76b1a2b6670e190b0371a8381e123c0992a`.

The actual recorded Lean search order selects output, 18 guarded client roots,
the fresh union and package. The check rehashes those roots, 1,977 project and
80 outside bundles, targets and first resolutions, and the captured BFS
subtrees (209/9, 79/3 and 4/3 project/outside). Historical source/object,
unrebuilt, package/dynamic and external-file limits remain; these checks do
not establish full ancestry.

`check.py` SHA-256 `57de9e0083826e1c4efea28b6c27e97741867c0134312d27da9da34c1cb2a368`;
`result.txt` SHA-256 `2fd4987a3ba4e9f5ac4e4bad00dc38e9004e0240cdf1a66cce332cbf07b236d2`.
