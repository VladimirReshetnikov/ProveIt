# Lean artifact status

## Checked directly

- `pell/ThirteenFreshSeedAudit.lean`: entire modified module plus endpoint axiom queries. `pell/ThirteenFreshSeed.lean` is the same module without those trailing queries.
- `pell/SignedPellResidueAudit.lean`: entire modified module plus endpoint axiom queries. `pell/SignedPellResidue.lean` is the same module without those trailing queries.
- `canonical/CanonicalResidue.lean`: standalone arithmetic iff.
- `canonical/CanonicalDecoder.lean`: full focused forward decoder, with the existing encoded-product identity supplied as a hypothesis.

## Integration candidates, not full-module validated

- `canonical/Diophantine/Common/MRDPCore.lean`.
- `canonical/DiophantineConsistency/BoundedForallCertificate.lean`.

The complete lower module could not load `Mathlib.NumberTheory.Dioph.olean` from the partial dependency cache. Apply the combined patch and compile the real pair in a complete checkout before integration.

`canonical/mathlib_source/Mathlib/Data/Nat/Prime/Factorial.lean` is unchanged dependency source, not a proposed edit. Its separate receipt records the narrow dependency rebuild used for the focused check.

Final compiler output and exact source hashes are under `../validation/`. The withdrawn aggregate prototype is outside this folder in `../screened_out/` and is not a recommendation.
