# PA195 source ordinals and resolved instructions

`PA195SourceClaims.lean` gives a Lean-checkable ordinal, source-site, and
resolved-instruction claim. Its `accepted_sound` theorem connects each
accepted claim to the actual flattened formal source tree and the upstream
`resolveAt` source control-flow semantics, using the upstream verified trie
lookup and fast resolver. The tree is generated from the hash-pinned upstream
program and PA195 grammar as described in `../pa195-source-entry`.

The batch generator reads the pinned 3,700-entry archive `source.json` and
emits explicit Lean claims. Lean computes each claim against the generated
formal source tree, independently of the Python resolver used by the packet.
From the repository root, check all claims sequentially with:

```sh
Computability/BusyBeaver/Research/PA/pa195-source-claims/check.sh
```

Pass `--start-site 0 --stop-site 100` for a smaller, independently
reproducible check. The generated count describes intended coverage; it is
not a record that a full run has completed. The grammar-to-Lean generator
remains an explicit source-generation boundary. This checker does not prove
that all source steps are physically simulated, a PRA/iPRA theorem, or an
arithmetic consistency equivalence.
