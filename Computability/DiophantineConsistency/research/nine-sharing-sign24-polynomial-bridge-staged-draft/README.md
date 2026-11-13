# Sign24 polynomial bridge via conditional specialization: source-only draft

The first proposed stage specializes generic transport to the sign24/sign25
zero equivalence while leaving the sign25 `PolynomialBridge` as a hypothesis;
it therefore does not import the sign25 concrete bridge. The second stage
imports that bridge and discharges the hypothesis by a direct theorem
application. This avoids repeating generic elaboration while both large
provider cones are simultaneously imported; it does not guarantee a smaller
Lean memory footprint, since the second stage still imports both cones.

Matching source copies were tried under `-M2800`: the conditional first stage
compiled, but the second stage still hit an interpreter memory exception.
The [independent terminal audit](../../reviews/nine-sharing-sign24-polynomial-bridge-staged-terminal-independent/README.md)
records the partial result. An unconditional bridge, iPRA proof-existence
endpoint, exact Lean degree and external-byte binding remain separate.
