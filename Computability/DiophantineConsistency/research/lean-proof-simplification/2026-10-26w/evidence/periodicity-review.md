# Periodicity after the earlier proposal baseline

Pinned repository: 553a5f7a463cbaab8800ff8148fef0bc5a9e1b22.

## Proposal: use the actual additive period vector

`WangTiles942HelicalQuotient.row_zero_of_helix` proves an equality for every integer time by separately inducting in the positive and negative directions. Interpret the plane as `F : ℤ × ℤ → α`; the hypothesis is exactly `Function.Periodic F (w,-1)`. Closure of periods under integer scalar multiplication says

`F ((x,t) + t • (w,-1)) = F (x,t)`.

The point on the left is `(x+w*t,0)`. This proves precisely the original statement without any finite-type, positivity, coprimality, vertical-period, or tile-semantic hypothesis. The complete declaration drops from 19 to 7 physical lines, and the full file from 147 to 135. These are source measurements, not timing measurements. A sheared one-dimensional alternative is also checked in the prototype: for fixed y, `u ↦ T(y-w*u,u)` has period one.

This use of the free additive lattice is distinct from earlier finite-set inverse invariance: the domain is infinite, and no recurrence argument or finite orbit is used. It is also separate from merely centralizing quotient/remainder transport; quotient formation occurs only downstream of this theorem.

## Adjacent client: seams are unit-periodic predicates

`WangTiles942SeamColumns.seam_iff_zero` has a second positive/negative time induction. Its already-proved `seam_successor_iff` makes the Prop-valued function `t ↦ SeamAt T x t` one-periodic, using `propext`. Apply `Periodic.int_mul_eq t`, then turn the equality of propositions back into an iff. The declaration drops from 8 to 5 lines, file 106 to 103. No extra period hypothesis is introduced: the period is a consequence of the local seam matching theorem.

## Validation and limits

`arithmetic_prototype.lean` successfully elaborated with Lean 4.32.0 and the cached Mathlib v4.32.0 environment. The exact generic helical statement, both proposed helical proofs, the original helical proof, and the original and proposed generic seam interfaces are in that file. No `sorry`, new axiom, or unsafe declaration is used.

The original and both new helical proofs each have `[propext, Quot.sound]`. The standalone original proposition-invariance proof has `[propext]`; the periodic replacement has `[propext, Quot.sound]`. The Bool-valued alternative also has `[propext, Quot.sound]`, so merely switching to Bool does not remove this dependency. The actual production seam theorem's existing imported dependency closure has not been freshly checked here. If preserving that exact closure is required, keep the original seam proof until a full-module comparison approves it.

`periodicity-refactor.patch` is a reviewable source patch; it was not applied to the repository and the full modified production modules were not built. The standalone checked theorem retains the full helical statement; the seam generic theorem receives exactly the already-available local iff. Thus the remaining integration work is import/interface and client verification, not a missing mathematical argument. `periodicity-metrics.json` records declaration counts, full-file counts and source hashes.
