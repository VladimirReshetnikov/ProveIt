# AQ20/104 conditional model-transfer draft

This packet transcribes the positive 20-variable, 104-operation, degree-14
candidate to an inert Lean literal and its 11 residuals, and proposes a model
transfer to the positive AQ22/110 literal. **No source here has been
elaborated by Lean**, and the two graph maps and the AQ22/110 graph maps remain
explicit assumptions in the conditional native and standard endpoints. The
124-operation natural JSON has no Lean proof of equality to `positiveShift`
of this literal.

Projection removes parent scale slots 13 and 14. Extension restores
`M=q*(q*q)*(J*beta)` and `U=Y*(q*q)`, where `q=1+J*beta`. The proposed
`extend_pos` uses `J,Y,beta > 0`; the beta hypothesis is **strict**. The graph
obligations require in addition that the cast into the model difference ring
of the fixed signed first port is exactly `ι beta`. Merely asserting that an
unrelated model beta is positive would not establish the port identity.

For current fixed ports the draft applies `ModelThirteenCarrier.port0` for
the exact representation and `ModelCarrierCurrent.beta_pos` for positivity
in the difference ring, then reflects the latter through `ι_lt_ι`. These are
source-level uses and neither the applications nor imported provider ancestry
have been checked for this new client. The output is conditional on the
unproved graph-map obligations for both AQ20/104 and AQ22/110. The latter has a
separate [residual-map source draft](../adaptive-aq22-quotient110-residual-maps-draft/),
also unelaborated.

The graph author's external polynomial checker confirms two deleted binding
residuals vanish after extension and the other 11 residuals agree. The missing
Lean argument must use these to construct both model zero maps, including
recovering the two scale equalities from a parent zero. The beta and maps
then need model-level elaboration, coherent provider replay, and axiom audits.
The parent AQ22/114 historical paired endpoint does not by itself certify either
new transfer or equivalence with an untranslated classical sentence.

From the `Computability/DiophantineConsistency` directory, run:

```
python3 -I -S -B research/adaptive-aq20-substituted104-model-draft/check.py | cmp - research/adaptive-aq20-substituted104-model-draft/receipt.json
```

The deterministic read-only check reconstructs the source literal and sum,
rechecks the graph author's receipt and pins the relevant sources. It does not
invoke Lean, stage artifacts, authenticate compiled providers, or prove the
candidate endpoint.
