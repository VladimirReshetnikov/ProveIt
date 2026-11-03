# Independent review: 19 upstream producer receipts

PASS for the bounded captured evidence in `research/trace75-upstream-19-provenance/`. We independently derived the 19-member selection from the preceding 141-input records and matched each captured candidate receipt and successful exit, unchanged recorded pins and import lists, actual selected output realpath/hash, source snapshot and producer source-copy hashes, and both retained logs. Source-declared imports agree with the captured serialized headers after removing implicit `Init`.

We independently compared all 56 explicit producer-recorded direct `.olean` input hashes with the final selected objects: 52 project edges and four Mathlib edges. The producer and selected realpaths are retained separately; the comparison of direct inputs is by `.olean` hash, not a claim that their paths or provenance are identical. The receipt output realpath itself is required to be the selected output realpath.

This does not authenticate the other 122 inputs, implicit `Init`, direct input companion bundles, producer-time package-transitive or dynamically loaded dependencies, the complete source-current closure, external file binding, or an independent Lean replay.

Author checker SHA `2195352d4a31e84e49e74b37f2cf322e3dedf30b989b4dc158525ceba3ad809b`, terminal SHA `9f5bc341d45234f151319ea2a113f181184debc7a89bca201491bd7151b56ba7`, stdout SHA `d9e3020b3a928aefdbc7c4601a023c6f1b40d0930d4ad4f5229d4eac36555eb3`. Our independent checker and output are alongside this review; no Lean was run.
