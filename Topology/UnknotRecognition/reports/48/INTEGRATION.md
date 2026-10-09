# Integration plan

Suggested additive location:
`Topology/UnknotRecognition/research/compressed-braid-certificates/`.
No numbered report slot is assumed and no remote repository was changed.

Keep the existing explicit-word gateway as the default. The new backend accepts a native, validated binary braid SLP; it does not accept an arbitrary group-presentation SLP or silently bind itself to a planar diagram.

`compressed_b3.engine.recognize` and `compressed_b3.verify.verify` accept `arena_factory`. The intended upstream factory is `fastunknot.compressed_words.WordArena`; the new modules use only its exact string methods and implement the C2*C3 anti-morphism themselves. Do not use the free-group inverse/reduction methods for these syllables.

Run the supplied check in an actual checkout:

```sh
python integration/upstream_check.py \
  --fast /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --output results/upstream-local.json
```

This check is **not recorded as passed** in the delivered package. It validates actual imported module paths and compares the actual explicit braid gateway. It is not the full production regression suite. Run that suite separately and preserve legacy certificate compatibility.

Use `compressed_b3.forest.recognize_forest` and `verify_forest` for arbitrary-strand raw SLPs. The forest is complete when all leaves have at most three strands. Wider unsupported leaves remain INCONCLUSIVE; integrate a complete exact fallback on the individually verified projected words only after checking its input and certificate contracts. A closure-equivalent substring replacement inside an arbitrary tangle is not valid.

The local CLI catches local `Limit` exceptions. An injected upstream WordArena raises its own `CompressedLimit`; a host adapter must handle the actual resource type. Never broadly convert arbitrary implementation errors into mathematical decisions. Provide a shared global resource callback across leaves and replay, because per-arena allowances reset and metadata/JSON work is outside the kernel operation counter.

Production promotion checklist: actual factory check; full current regression suite; deterministic source binding; global input/certificate byte limits; independent fallback replay; no-progress timing controls; compressed versus explicit crossover measurements on genuine workflow inputs. No claim about an uninspected future API is made.
