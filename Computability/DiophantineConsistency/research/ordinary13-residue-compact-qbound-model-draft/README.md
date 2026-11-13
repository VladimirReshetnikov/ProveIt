# Compact first-port bound for the 13/90 graph-power draft

This is a **source-only, unelaborated** client of the proposed
`ResiduePellCoordinatesDraft.graph_power`. It specializes the graph's natural
port tuple to `Residue90CompactPortBoundsDraft.ports K`, where `K` remains an
arbitrary standard natural. Its first port is exactly
`CompactFixedBeta.betaNat = 2^(67*8807)-1 = 2^590069-1`; the input is the
natural port tuple cast into the arbitrary IΣ₁ model, not an external byte
file or an assumed model numeral decoded from a PDF.

The proposed `beta_at_least_46` uses the existing
`CompactFixedBeta.beta_identity`, which states inside the model that the
cast beta plus one is the internal exponential at `67*8807`. The proof copies
the finite-six cast and exponential monotonicity pattern from
`CompactGraphDerivedRadix.graph_digits`: `64 = exp 6 ≤ beta+1`, and hence
`46 ≤ beta`. The large beta numeral is not evaluated in the model proof.
The proposed `compact_q_at_least_47` uses `0 < v 0` to get `1 ≤ v 0` and the
definitional identity `q=1+v 0*beta`; its multiplication step follows the
existing `FreeJPowerGrowth` source. These are source proof proposals and
imports, not independently authenticated compiled providers.

The final `compact_graph_power` passes the derived `46≤q` and `0<beta` into
the earlier witness-preserving power source. Its assumptions still include
the actual residue-90 graph zero, `0<v 0`, `0<v 6`, positive-C gap, and rank
window. The latter might be discharged separately using the compact rank
bound under its own hypotheses; this client does not do so. It also does not
establish the previous q-balance, exact-index, first-ordinate, oriented-root,
main-Pell coordinate, or other imported graph lemmas by compilation. The
witness-Pell draft and all provider/toolchain/axiom boundaries are inherited.

Specializing arbitrary `K` to the retained 87-operation endpoint's symbolic
kernel needs the separate tuple client and a graph/endpoint transfer. The
current Lean source's compact beta is distinct from the previously displayed
2011 tuple. This packet does not connect its natural/integers casts to the
external P72/P115 payload or physical equation PDF, prove the positive-82
bridge, or provide an internal-iPRA end-to-end proof. `#print axioms` commands
are included in the inert source for a future coherent build; they were not
executed.

The check is deterministic and read-only. It pins this draft, the selected
source providers, and both witness/graph interfaces, checks the exact symbolic
first-port and q definitions and finite exponent arithmetic, and performs
1,100 bounded natural-integer controls. These controls are not a substitute
for model proof or Lean elaboration:

```
python3 -I -S -B research/ordinary13-residue-compact-qbound-model-draft/check.py | cmp - research/ordinary13-residue-compact-qbound-model-draft/receipt.json
```

Run from `Computability/DiophantineConsistency` or use absolute paths.
