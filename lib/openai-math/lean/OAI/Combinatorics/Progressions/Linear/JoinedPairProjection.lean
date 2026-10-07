import Mathlib.Algebra.Lie.Prod
import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop

namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M W : Type u} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [LieRing W] [LieAlgebra ℚ W]

def joinedPairProjection (ρ : W →ₗ⁅ℚ⁆ M) : (L × W) →ₗ⁅ℚ⁆ PairAlgebra L M :=
  liePiMap (fun i => by
    cases i
    · exact ρ.comp (LieHom.snd ℚ L W)
    · exact LieHom.fst ℚ L W)

@[simp] theorem joinedPairProjection_true (ρ : W →ₗ⁅ℚ⁆ M) (x : L × W) :
    joinedPairProjection ρ x true = x.1 := rfl

@[simp] theorem joinedPairProjection_false (ρ : W →ₗ⁅ℚ⁆ M) (x : L × W) :
    joinedPairProjection ρ x false = ρ x.2 := rfl

@[simp] theorem pairFrequency_joinedPairProjection (ρ : W →ₗ⁅ℚ⁆ M)
    (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ) (x : L × W) :
    pairFrequency η θ (joinedPairProjection ρ x) = η x.1 + θ (ρ x.2) := by
  rw [pairFrequency_apply, joinedPairProjection_true, joinedPairProjection_false]

theorem joinedPairProjection_mem_layer {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (H : NilpotentLieFiltration (L × W) s) (ρ : W →ₗ⁅ℚ⁆ M)
    (hfirst : ∀ j, ∀ x ∈ H.layer j, x.1 ∈ D.filtration.layer j)
    (hpartner : ∀ j, ∀ x ∈ H.layer j, ρ x.2 ∈ E.filtration.layer j)
    (j : ℕ) (x : L × W) (hx : x ∈ H.layer j) :
    joinedPairProjection ρ x ∈ (pi (pairModels D E)).filtration.layer j := by
  change joinedPairProjection ρ x ∈
    (NilpotentLieFiltration.pi (fun i => (pairModels D E i).filtration)).layer j
  rw [NilpotentLieFiltration.mem_pi_layer]
  intro i
  cases i
  · exact hpartner j x hx
  · exact hfirst j x hx

end Erdos3.RationalFilteredNilmanifold

end

end OAI
