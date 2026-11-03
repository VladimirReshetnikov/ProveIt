# Packed-cell pulse preservation

`CompactPackedPulsePreservation.packing_of_packed_pulse` combines the
represented compact cell with the earlier conditional single-pulse packing
client. Its base word is `j ↦ packedCell (row j) 0` and its low mask is the
symbolic finite-list compact mask. In every model of IΣ₁, the base
`PackingInput.low` field and the proved empty dummy bit now provide the
single-pulse low-mask condition, so that condition is no longer a separate
hypothesis in this client.

The theorem **still assumes a valid base packing**, a Boolean dummy pulse
function with positive support, and all five product, cell-sum, positive
block and high-mask conditions for the perturbed word. It does not construct
any of those objects, supply a graph zero, or establish an internal iPRA
proof. It does not require the row or pulse functions to be definable because
this is a pointwise packing-preservation theorem, not the outer represented
word or rank-calibration construction.

The first bounded attempt, session 89024's predecessor, exited 1 before proof
elaboration: Lean's namespace search selected a provider missing a transitive
word-client module. The corrected run (session 89024) used a new mixed
overlay, exited 0 without warnings or `sorryAx`, and printed only `propext`,
`Classical.choice`, and `Quot.sound` for the named theorem. Its runner hashed
all regular files in the two candidate `DiophantineConsistency` provider
directories. It found 524 distinct names, including 338 shared names whose
bytes matched across both providers; the per-file inventory and before/after
hash checks are retained. Direct import and companion checks were also
unchanged. The overlay makes the sampled union available to this incremental
author-side run; it does **not** independently authenticate the full source
closure, package or dynamic-loading ancestry, nor establish an independent
paired replay. Its `/tmp` paths are ephemeral.
