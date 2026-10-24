# Sources and exact scope

The new equations and signed-base proof are stated fully in PROOF.md.
The only non-elementary imported arithmetic ingredient is the standard
Pell-index criterion, with the exact positive-domain and congruence
hypotheses shown in the copied source files.

1. Mathlib, Mathlib/NumberTheory/PellMatiyasevic.lean. The pinned reference
   and its commit are in prior/PELL_SOURCE_PIN.json; the actual source is
   prior/PellMatiyasevic_reference.lean, with prior/LICENSE.Mathlib.
   Relevant statements are Pell.matiyasevic, Pell.eq_pell and the standard
   Pell recurrence. Current official documentation was also checked:
   https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PellMatiyasevic.html

2. ProveIt, commit 84e16e43092614bae262ca59651cb9d77e31a255,
   Computability/DiophantineConsistency/Lean/DiophantineConsistency/PellRepresentation.lean.
   The copied prior/PellRepresentation.lean gives the exact norm-to-natural
   criterion used here. Repository:
   https://github.com/VladimirReshetnikov/ProveIt

3. The same repository's immutable incoming archive
   ConZFC_Synchronized_Certificates_2026-10-24.zip, SHA256
   ea82e23aa5956262c823368e947e31ad113201c22654c214b9c6f7427d63e0bf.
   The inherited finite-ring common-index and common-scale arguments are
   copied as prior/shared_indices.md, prior/shared_powers.md and
   prior/independent_mathematical_review.md. Those arguments are not
   presented as new in this packet. The new compiler does not import
   their implementation.

4. The preceding ZFC_Diophantine_Budget_Interpolation archive's alternative/
   component supplies the strict-boundary packed tiling circuit and its
   two-power fusion theorem. Exact copied source hashes are in
   SOURCE_PINS.json. Its source PROOF.md and independent ordinary review
   are preserved as prior/tiling_PROOF.md and
   prior/tiling_INDEPENDENT_PROOF_REVIEW.md. The original core.py and
   build_dag.py are retained verbatim for the optional tiling composition.

The prior source files are immutable copies. SOURCE_PINS.json authenticates
every one, and the final manifest authenticates this complete packet.
The auxiliary counts and new signed-frame proof do not rely on a source
claim that the raw 943-tile list has the necessary initialization property.
