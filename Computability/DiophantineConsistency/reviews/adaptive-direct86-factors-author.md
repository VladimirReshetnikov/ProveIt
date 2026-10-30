# Direct-ordinate 86 literal factors: scoped author replay

The 86-operation literal is factored exactly into four signed factors whose product is one. `AdaptiveDirectOrdinate86Factors.expressionAt_factor_magnitudes86` proves, in every model of IΣ₁, that a literal zero makes all four factor magnitudes one. It binds the changed first factor through the already checked 87-root one-hole context, and identifies the unchanged second and strong factors exactly. `AdaptiveDirectOrdinate86Units.expressionAt_factor_units86` proves all four factors represent **positive** one, from that zero, by modulo-four exclusion of negative one. No factor-unit hypotheses are assumed, and arbitrary internal values, including zero, are covered.

Author run: `/tmp/adaptive-direct86-factors-k9qsu5hx`, final `state.json` SHA-256 `3adca22ce4b2dc2e4af1d8b10391b6fd856c15b5b2291da2c30c45922a1fc2a3`. Reproduce with `python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_direct_ordinate_factors.py`. It snapshots both sources, verifies the deterministic factor generator against candidate JSON, authenticates selected inherited provider state/source/object/log records before and after, and stores commands and all build logs in the private directory. Both Lean logs were empty.

| Module | Source SHA-256 | Object SHA-256 |
|---|---|---|
| `AdaptiveDirectOrdinate86Factors` | `1d812e085ca074eb66bda9b4a7aa01ee5118af7e0f2d303320a524d854084967` | `5909ba000051d1ac7c22b0256ad78325d2e93331355dc45ed09dc370c5620362` |
| `AdaptiveDirectOrdinate86Units` | `8afcece32c0f40a321f7fd0957450f1d0516ff38be37fd75de264d52f9144d02` | `67bf513ddd54c19199c18d60fe4d66deae83acbcefeee15a4a31f07e5a35f330` |

The fixed 41-node source graph excludes the recently changed FirstDivisibility and TransportQuotient modules, and excludes Population, whose inherited canonical source guard has drifted. This is a **scoped** check: inherited Foundation/Mathlib and other recorded provider boundaries remain historical, and this run does not authenticate the entire source closure of the canonical overlay. The result does not yet derive the norm or residue needed for positive offset recovery; it does not establish 86/87 zero-set equivalence or an HA proof-existence theorem.

The frozen evidence directory `adaptive-direct86-factors-author-evidence` contains state, driver, generated source, source snapshots and complete logs/timing output. Its `FILES.json` SHA-256 is `58e27281e6104dbc4ce704c34767db770e2b55bcafae5adfccc70cebd3359c08`.
