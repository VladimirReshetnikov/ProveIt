# Decoder-bundle follow-up fixed source graph

The current workspace and this fixed source tree both passed graph-only audits and match all 847 project source paths, import edges, source hashes, build order, 101 direct external object anchors and companions, and Lean/Lake anchors. The frozen tree is `/tmp/pra14-bundle-followup-frozen-ijrbirl6/tree`. Exactly one source delta, `ZFCinPA.ModelCodedDecoderBundle222`, is stored in `source-deltas/` relative to the previous fixed 847-source packet `reviews/pra14-post-merge-source-snapshot/`. A separate audit of the 847 parent and 73 suffix sources found no other drift (`reviews/pra14-bundle-followup-source-audit/`).

This is input evidence, not a proof result. After the previous isolated rebase `/tmp/pra14-full-transitive-bbfwtdv_` has finalized PASS, the prepared incremental source rebase is:

```sh
python3 /tmp/pra14-bundle-followup-frozen-ijrbirl6/driver.py --rebase /tmp/pra14-full-transitive-bbfwtdv_
```

The static source-declared reverse cone has eight parent modules. Reused-object original compile ancestry is reconstructed from surviving objects; external package transitive ancestry and dynamic imports remain inherited. A source-current suffix rebuild and independent checks remain separate.
