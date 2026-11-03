# Matched cyclic source digits at compact field phases

`CompactWordFieldCyclic.lean` connects the packed edge-bit equalities to the
actual full-word cyclic offsets in every IΣ₁ model. For each valid row `j`:

* at phase `1013+u`, `u<9`, the bare shift 30 and whole-cell shift `8807*s`
  read equal source digits;
* at phase `1065+u`, `u<8`, the bare shifts 62 and 8849 read equal source
  digits.

The proof uses the `CompactWord` neighbor matches, the concrete packed
field-digit equalities and the existing model-level block-index wrap lemmas.
It requires Σ₁-definable row and dummy functions, a marked word, and `s<N`
for the vertical identity. These are source-column equalities; physical
output parity, marker phases, full high-mask safety, graph zero and iPRA
proof remain separate.

The guarded single-author compile (session `38859`) exited 0 without warnings
or `sorryAx`, with unchanged sampled direct dependencies and companions. Both
named axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The command, source/object hashes, dependency scan, log and
terminal receipt are retained; `/tmp` providers are ephemeral. Package,
transitive, dynamic and between-observation ancestry is inherited, and this
is not an independent paired replay or full dependency-closure audit.
