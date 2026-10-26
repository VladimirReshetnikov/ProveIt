# Future Lean validation (not executed)

The snapshot is not a complete Lake checkout. Obtain a full checkout at e1c8914bc7064d9a8e7c06171a18069a949badd0 with the pinned Lean/mathlib dependencies and already built imports. No installation or compilation was performed for this review.

Use a disposable checkout/worktree, not the only production copy. Check source hashes first. Apply only the selected patches listed in candidate_status.json. PhysicalOrder is excluded prior work and is not a selected patch.

For each selected full replacement module, from Computability/DiophantineConsistency/Lean:

    lake env lean DiophantineConsistency/SidonPositions.lean
    lake env lean DiophantineConsistency/IterationSize.lean
    lake env lean DiophantineConsistency/CurrentPowerCoordinates2011.lean

Before running existing checks, compile the edited modules into the disposable checkout's normal Lake build artifacts. A direct `lean file.lean` check alone does not replace the old imported `.olean` used by a checks file. Use the repository's normal Lake target for each edited module, or an explicit isolated overlay with the edited `.olean` files first on LEAN_PATH. Do not read a successful checks build that imports old `.olean` files as validation of the patch.

Run the existing matching checks/SidonPositions.lean, checks/IterationSize.lean, and checks/CurrentPowerCoordinates2011.lean against those exact edited artifacts. Then build all reverse dependencies or the complete project using its documented build command.

Capture `#print axioms` for these five selected endpoints before and after under exactly the same environment:

- DiophantineConsistency.SidonPositions.weight_injective
- DiophantineConsistency.SidonPositions.pairWeight_injective
- DiophantineConsistency.IterationSize.iterate_depth
- DiophantineConsistency.CurrentPowerCoordinates2011.generator_cast_auxiliary
- DiophantineConsistency.CurrentPowerCoordinates2011.generator_cast_C0

The excluded PhysicalOrder endpoint is a sixth endpoint checked in the original static shortlist, but is not part of this selected replay.

The controller patch deliberately routes through stronger exact-order results. An unchanged source type or import list is not evidence of an unchanged proof dependency/axiom footprint. Reject sorryAx, preserve required regression checks, and report any changed axioms or runtime honestly.

For Sidon, test both the raw frozen source patch and its composition after the prior moment-polarization patch. Both orders should reproduce the same composite source bytes, as recorded by independent_review/composition_check.json. The full conceptual assumed-applied baseline is not a mechanically composed checkout; only this concrete overlap was replayed.
