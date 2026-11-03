# Independent result review: trace75 BFS original word

**PASS.** The captured author result for `Trace75BFSOriginalWord` has child,
Lean and serialized-header exits 0, the expected axiom report, and matching
source, output, logs, pins and two direct imports. The author reports actual
outer tool exit 0; the wrapper records child exit 0 and stable hashes. This
review did not replay Lean.

Under exact symbolic direct-BFS ports and a positive trace75 zero,
`graph_original_word` yields one N,W,s with the stated radix and shift bounds.
For the direct row b, W represents its model backward-map image and
`CompactLocalWord.Word` holds for that same image at N,s. The predecessor's
direct-row representation is discarded and not exported as W. This is not a
halting or iPRA theorem and does not bind external coefficient files.

The accepted result SHA-256 is
`746ed1e8d13ee775b65ecc524e3f345a4bfef59e307afe2e42e16b1fd4868aec`,
and its outer receipt SHA-256 is
`3549393cbe3d97bcca1df55ebfa9aba2bce3cd2dd923f447033c97a09e991bc4`.
The regular output
`/tmp/trace75-bfs-originalword-761j1h5p/Trace75BFSOriginalWord.olean`
has SHA-256 `7993899f413a29c339018d2aa71879f7c04968c080b431a5d1407b49d5670066`.

The actual recorded Lean search order selects output, 19 guarded client roots,
the fresh union and package. The check rehashes those roots, 1,977 project and
80 outside bundles, their targets and first resolutions. Historical
source/object, unrebuilt, package/dynamic and external-file limits remain;
these checks do not establish full ancestry.

`check.py` SHA-256 `0e6f28a57eff9122d7b41f9148f57d3b284efee6d471bc81c3d1b30fd4bcf9d9`;
`result.txt` SHA-256 `0d97c0daf066d191e22d0f58b97731fe59b17b5fadfe554830afaa4f9ca9ec20`.
