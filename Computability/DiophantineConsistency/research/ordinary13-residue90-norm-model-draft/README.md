# Residue-90 model norm and compact-bound source drafts

This packet proposes a graph-to-fact client for the 13/90 compact-port gamma
argument. **All Lean sources here are unelaborated**. The finite checks do not
validate their tactics, theorem statements against compiled providers, model
equivalence, or an iPRA endpoint.

The generated literal and its four residuals reproduce the pinned 90-row
graph. `Residue90GraphNorms.lean.src` proposes that a graph zero makes all
four residuals zero, then extracts the first signed norm and, assuming
`F≤q` and gamma zero, the actual main signed norm. Its explicit natural rank
representation reconciles the truncated subtractions with the signed graph;
the main pair uses the required `R+X*Y*q` adjustment. The exact residual
simplification and difference-ring calculations remain proof attempts.

`Residue90SignedNorms.lean.src` isolates the model-level quotient steps. From
a signed square norm and positive natural scale it proposes using
`ReducedNormSigned.natural_magnitude_square` and
`ArithmeticAdaptiveQuotients2011.scaled_quotient` to obtain a natural norm
witness in the same IΣ₁ model. For the main root it uses
`P72Root.ι_magnitude_sq` to recover the signed-pair magnitude norm consumed
by the gamma client, then obtains its natural quotient norm. No root sign is
assumed.

`Residue90CompactPortBounds.lean.src` proposes applying the existing
`CompactFixedBeta.bounds` and `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`
with the explicitly represented compact mask tuple. Its rank theorem retains
`F+alpha<q` and `J>0` as hypotheses. The source tuple still needs to be
identified with the authenticated compact graph bytes and compatible provider
closure; an arbitrary natural `K` in this packet is not an authenticated
fixed kernel.

`Residue90GraphGamma.lean.src` composes the proposed graph norm extractions
with the earlier fact-level gamma client. It **still assumes** positive first
scale and U, `q≥2`, `X≥1`, `Y≥q³`, `F≤q`, and the model rank bound. It does
not prove the graph's positive-C argument or derive those facts from a zero.
`Residue90CompactGraphGamma.lean.src` further proposes deriving the scale,
`q` and `Y` bounds and the rank inequality for the symbolic mask tuple from
`J>0`, `X≥1` and `F+alpha<q`; those three graph facts stay explicit, and K
remains an arbitrary standard natural. No connection to the 90/91 zero maps, physical displayed equation, compact
fixed-kernel endpoint or current-2011 ports is claimed.

Run the bounded checks from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-norm-model-draft/check.py | cmp - research/ordinary13-residue90-norm-model-draft/receipt.json
```

The checker pins source and graph bytes, verifies the four-residual DAG sum,
replays the external graph checker and tests finite graph/ring identities.
These checks never run Lean, stage artifacts or authenticate providers.
