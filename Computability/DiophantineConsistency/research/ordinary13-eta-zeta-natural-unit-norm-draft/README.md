# Proposed unit factors for the eta/zeta-natural probe

This is an unelaborated, source-only adaptation of the existing eta-natural
unit/norm proposal to the exact eta/zeta-natural boundary probe. It is not a
Lean theorem, provider or axiom replay, compact zero-exclusion, zero-map,
equation reduction, or endpoint. In particular, the two signed-port full
zeros in the boundary audit are consistent with the source's unit conclusion:
those examples have all four factors +1.

The generated `EtaZetaNaturalUnitGraph` transcribes all 85 probe rows and
exports the exact original factor and norm fields. Its k field is `kbase`
(the new eta+zeta), and its main root uses the probe's adjusted r0 so that
`r0=k−1−R`. `EtaZetaNaturalUnitBridge` is a mechanical namespace adaptation
of the previously independently reviewed eta-natural bridge: it proposes the
first-factor mod-four negative-unit exclusion, applies the existing generic
main/auxiliary/strong pattern exclusions, and derives four signed norm
identities from an actual probe output zero. Whether its expression-pattern
`rfl`, finite-residue proof, source imports and all model casts elaborate for
the new literal remains unchecked.

The checker verifies exact namespace transcription, generated graph bytes,
all 1,024 first-pattern mod-four combinations and 300 probe evaluations at
zeta=0 with arbitrary signed ports. These finite/source checks cannot replace
a Lean proof for arbitrary models and do not justify a positive beta or
compact port assumption. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta-natural-unit-norm-draft/check.py | cmp - research/ordinary13-eta-zeta-natural-unit-norm-draft/receipt.json
```
