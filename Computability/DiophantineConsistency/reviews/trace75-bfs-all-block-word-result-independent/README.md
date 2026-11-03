# Independent result review: trace75 BFS all-block word

**PASS.** The captured author result for
`Trace75BFSAllBlockWord.graph_all_block_word` has child, Lean and serialized
header exits 0, the exact expected axiom report, and matching source, output,
logs, pins and direct imports. The author reports the actual outer tool exit 0;
the outer wrapper independently records its child exit 0 and stable hashes.
No Lean replay was performed in this review.

The checked source uses the exact symbolic direct-BFS port assumptions and a
positive trace75 zero. It identifies the two lengths using the common radix,
then yields one positive model length N, a represented base-1024 block word,
and a selected tile with the corresponding copy word for every h<N. This is
not a halting or iPRA theorem and does not bind external coefficient files.

The reviewed receipt is
`research/trace75-bfs-all-block-word-prototype/observations/attempt01/result.json`,
SHA-256 `46d8ffd2a89c1e7a955e54f763668bf0d03b2bb24aeea495b3a9bc6094756932`.
Its outer receipt SHA-256 is
`638abb41f85ec52f6cca75cf37d3988c761b5b024ecb11e85043a5d01ac47611`.
The regular output object is
`/tmp/trace75-bfs-allblockword-_c_e6kmb/Trace75BFSAllBlockWord.olean`,
SHA-256 `ad6eda0a5c1a390493a943e97d08e84dc0eed993918d16122d0c0b3bebbfa23a`.

The actual recorded Lean search order selects the output, the 13 guarded
client roots, the fresh union and the package in that order. The review
rehashes those client roots and all 1,977 project and 80 outside provider
bundles, compares targets and first resolutions, and rechecks the captured
BFS subtrees (330/29 and 7/4 project/outside modules). Retained historical
source-to-object, unrebuilt, package/dynamic ancestry, and external-file
limitations remain; these checks do not establish full ancestry.

`check.py` SHA-256 `49c869fdc2e79e51c590b4c0c6eaa61235f468d999d1dc20a9ce98d371bd209a`;
`result.txt` SHA-256 `519aaf9f22128a98d8bd2aedad1ff1913d4a93d1a1a460ccf340de3dce751631`.
