# Noncircular odd-ordinate recovery

`PellRecovery.recover_odd_ordinate` proves in every IΣ₁ model: if `n>0`, `s` is odd, `0<c<ycoord n`, `2*ycoord n<xcoord n`, and `c` is signed-congruent to `ycoord s` modulo `xcoord n`, then `c=ycoord p` for a positive odd `p<n`. It first folds `s` and then uses the explicit size bounds to exclude a negative residue. It never assumes the main norm for `c` and does not invoke `half_index`.

The guarded author check `observations/attempt01/` passed without diagnostics, yielding `/tmp/pell-all-index-recovery-oi9pydkd/PellRecovery.olean`, SHA-256 `0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a`. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Its runner pins selected prototype objects and one inherited provider, not the complete project/package/dynamic or historical source-object ancestry. Resource monitoring is sampled; no paired replay is claimed.

Actual graph-specific size bounds must still be proved before applying this theorem to the 80-operation graph; it does not itself prove a machine or iPRA endpoint.
