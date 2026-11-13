# 90-to-89 graph transport

`Absorb89Forward.zero_iff` checks that updating the 90-row valuation by `r := r+s` yields an 89-row zero exactly when the original valuation is a 90-row zero. `transform_pos` and `exists_absorb_of_direct` establish the corresponding forward existence implication for positive valuations in every indicated IΣ₁ model. These statements use arbitrary natural ports; the bounded-port hypothesis arises in the other direction.

The guarded author run `run-forward.py` passed in session 62909 with exit 0, using the recorded selected provider; source, command, samples and output hashes are in `observations/forward-attempt01/`. No independent Lean replay was performed, and inherited package-transitive, dynamic and historical source/object ancestry remain outside this check. The later [existence-equivalence join](EQUIVALENCE.md) supplies the reverse implication at bounded ports; fixed-port and iPRA equivalences require further composition.
