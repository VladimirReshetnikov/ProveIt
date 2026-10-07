import OAI.Combinatorics.Progressions.Estimates.WeightedCubePlateau
import OAI.Combinatorics.Progressions.Lattices.AffineBlockScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def affineTorusRadius (q g b : ℕ) (C V : ℝ) : ℕ :=
  ⌈affineBlockScaleBound q g b C V⌉₊

noncomputable def affineTorusFactor (q g b : ℕ) (C V : ℝ) : ℕ :=
  2 * affineTorusRadius q g b C V + 1

theorem affineTorusFactor_pos (q g b : ℕ) (C V : ℝ) : 0 < affineTorusFactor q g b C V := by
  unfold affineTorusFactor
  omega

instance affineTorusFactor_neZero (q g b : ℕ) (C V : ℝ) : NeZero (affineTorusFactor q g b C V) :=
  ⟨(affineTorusFactor_pos q g b C V).ne'⟩

theorem affineTorusFactor_le (q g b : ℕ) {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) :
    (affineTorusFactor q g b C V : ℝ) ≤ 2 * affineBlockScaleBound q g b C V + 3 := by
  exact integerSupportTorusFactor_upper (affineBlockScaleBound_nonneg q g b hC hV)

theorem affineWeightedCube_bound_le_torus {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n K : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    {C V : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ b j i, |(u b j i : ℝ)| + (v b j i : ℝ) * (s b j).length ≤ C * (s b j).length)
    (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (S : Finset I) (hS : S.card ≤ n + 1) :
    affineWeightedCubeJetBound s u v S ≤
      (affineTorusRadius (Fintype.card I) (n + 1) (Fintype.card B) C V : ℤ) * K := by
  have h := (affineWeightedCubeJetBound_le_scale s u v hC hcoord hvol S hS).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))
  exact_mod_cast h

theorem affineWeightedModerate_bound_le_torus {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n K : ℕ} (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (stride : B → ℕ) (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    {C V : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ b j i, |(u b j i : ℝ)| + (v b j i : ℝ) * (s b j).length ≤ C * (s b j).length)
    (hvol : ∀ b, (|(offset b : ℝ)| + (stride b : ℝ) * (c b).length) *
      (∏ j, ((s b j).length : ℝ)) ≤ V * K)
    (S : Finset I) (hS : S.card ≤ n) :
    affineWeightedModerateJetBound c s offset stride u v S ≤
      (affineTorusRadius (Fintype.card I) n (Fintype.card B) C V : ℤ) * K := by
  have h := (affineWeightedModerateJetBound_le_scale c s offset stride u v hC
    hcoord hvol S hS).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))
  exact_mod_cast h

theorem affineModerate_physical_volume_lower {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    {t : ℕ} (ht : 0 < t) {K D : ℝ} (hD : 0 ≤ D)
    (hlower : K ≤ D * ((c.length : ℝ) * ∏ j, ((s j).length : ℝ))) :
    K ≤ D * ((((t * c.modulus none : ℕ) : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) := by
  have hm : (1 : ℝ) ≤ (t * c.modulus none : ℕ) := by exact_mod_cast Nat.mul_pos ht (c.modulus_pos none)
  apply hlower.trans
  apply mul_le_mul_of_nonneg_left _ hD
  have hp : 0 ≤ (c.length : ℝ) * ∏ j, ((s j).length : ℝ) := by positivity
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hm hp

end Erdos3

end

end OAI
