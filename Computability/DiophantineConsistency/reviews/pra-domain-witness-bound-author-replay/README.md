# Explicit positive domainDef polynomial

The full exact Foundation `domainDef u s` now has a candidate-PRA witness bound at the explicit polynomial `s + bitMajorant(u) + negBitMajorant(u) + bitMajorant(s) + negBitMajorant(s)`. The proof binds both positive and negative existential branches and both bit-membership polarities; its only graph hypothesis is the actual positive domain graph. The bit majorants are themselves explicit quartic and quadratic polynomials in the source.

The positive and negative domain-existential parents each have independent root and private replays. Foundation and package transitives are inherited with listed boundary anchors checked. The result does not bound `isMappingDef`, construct a recursive history, or establish rho/HA equivalence. Replay: `python3 Computability/DiophantineConsistency/reviews/pra-domain-witness-bound-author-replay/replay.py --parent /tmp/pra-domain-full-overlay-wr1mr3p2/lib`.
