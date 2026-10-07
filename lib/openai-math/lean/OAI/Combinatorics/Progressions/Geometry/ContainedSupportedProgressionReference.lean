import OAI.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

private theorem fiberLaw_weight_pos_of_pos {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (f : X → Y) (x : X) (hx : 0 < p.weight x) :
    0 < (p.fiberLaw f).weight (f x) := by
  change 0 < ∑ y, p.weight y * (if f y = f x then (1 : ℝ) else 0)
  apply Finset.sum_pos'
  · intro y _
    exact mul_nonneg (p.nonneg y) (by split_ifs <;> norm_num)
  · exact ⟨x, Finset.mem_univ _, by simpa using hx⟩

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_restrict_weight_pos
    (y : PrincipalIntegerTuples B h α L) (hy : 0 < (law).weight y) (P : D → Prop) :
    0 < (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight
      (principalAxisRestrict P y) := by
  rw [← containedSupportedProgressionAxisLaw_fiberLaw B h L H step c hL hH hsubset q r hcell P]
  exact fiberLaw_weight_pos_of_pos (law) (principalAxisRestrict P) y hy

theorem containedSupportedProgressionLaw_cube_support
    (y : PrincipalIntegerTuples B h α L) (hy : (law).weight y ≠ 0)
    (j : PrincipalTupleIndex B h) : IntegerScalarCube (L j) (fun a => (y j a : ℤ)) := by
  apply FiniteProbabilityWeights.fiberLaw_support _
    (containedProgressionTupleMap B h L H step c hL hsubset)
    (fun y => IntegerScalarCube (L j) (fun a => (y j a : ℤ))) _ y hy
  intro z _
  exact containedProgressionCubeMap_cube α _ _ _ _ _ _ (z j)

theorem exists_containedSupportedProgressionReference :
    ∃ y₀ : PrincipalIntegerTuples B h α L,
      0 < (law).weight y₀ ∧
      (∀ j, IntegerScalarCube (L j) (fun a => (y₀ j a : ℤ))) ∧
      (∀ P : D → Prop,
        0 < (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight
          (principalAxisRestrict P y₀)) ∧
      (∀ y, (law).weight y ≠ 0 → principalResidueLabel q y = principalResidueLabel q y₀) := by
  obtain ⟨y₀, hy₀⟩ := (law).exists_weight_pos
  refine ⟨y₀, hy₀, ?_, ?_, ?_⟩
  · exact containedSupportedProgressionLaw_cube_support B h L H step c hL hH hsubset q r hcell y₀ hy₀.ne'
  · exact containedSupportedProgressionLaw_restrict_weight_pos B h L H step c hL hH hsubset q r hcell y₀ hy₀
  · intro y hy
    exact containedSupportedProgressionLaw_residue_eq B h L H step c hL hH hsubset q r hcell y y₀ hy hy₀.ne'

end Erdos3

end

end OAI
