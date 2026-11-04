# Beta-only cover: opaque elaboration draft

The first beta-bind attempt had Lean exit 0 but the strict runner rejected a warning that exponent 8807 was not evaluated; the attempt is excluded. This unchecked v2 retains the exact theorem and proof and locally marks `Nat.pow` and `CompactFixedBeta.betaNat` irreducible for elaboration. Its intent is to prevent unnecessary giant-power reduction while applying already checked theorems. It does not increase the exponentiation threshold or assert that the warning will disappear.

Independent source/prelaunch reviews and a guarded Lean check are required. The low, defect and high values and hypotheses remain symbolic. No concrete cover or graph guard is claimed.

The [independent source review](../../reviews/trace74-cover-bind-beta-v2-draft-independent/README.md) confirms the local-only change and unchanged theorem; no Lean run was performed by that review.
