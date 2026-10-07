import OAI.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

def progressionPrincipalResidue (q : ℕ)
    (r : PrincipalTupleIndex B h → Option α → ZMod q) :
    PrincipalTupleIndex B h → Option α → ZMod q :=
  fun j a => (if a = none then (c j : ZMod q) else 0) + (step j : ZMod q) * r j a

include hH hsubset in
 theorem containedProgressionTupleMap_residue_of_weight_ne_zero
    (q : ℕ) (y : PrincipalIntegerTuples B h α H)
    (hy : (principalTupleWeights B h H hH).weight y ≠ 0) :
    principalResidueLabel q (containedProgressionTupleMap B h L H step c hL hsubset y) =
      progressionPrincipalResidue B h step c q (principalResidueLabel q y) := by
  have hpos := lt_of_le_of_ne ((principalTupleWeights B h H hH).nonneg y) hy.symm
  funext j a
  have hj := FiniteProbabilityWeights.pi_weight_pos_component
    (fun j => integerScalarCubeWeights α (H j) (hH j)) y hpos j
  have hcube := (mem_integerScalarCubeSet (H j) (y j)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y j)).mp hj).1
  change ((containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j)
    (hsubset j) (y j) a : ℤ) : ZMod q) = _
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ hcube]
  simp only [progressionPrincipalResidue, principalResidueLabel, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero]

theorem containedProgressionForecast_indicator_disintegration
    {Z : Type*} [DecidableEq Z] (q : ℕ) [NeZero q]
    (F : PrincipalIntegerTuples B h α L → Z) (z : Z)
    (coefficient : (PrincipalTupleIndex B h → Option α → ZMod q) → ℂ) :
    let p := principalTupleWeights (α := α) B h H hH
    let map := containedProgressionTupleMap B h L H step c hL hsubset
    (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
      (if F y = z then 1 else 0)) =
      ∑ r : {r : PrincipalTupleIndex B h → Option α → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient (progressionPrincipalResidue B h step c q r.val) *
          (((containedSupportedProgressionLaw B h L H step c hL hH hsubset q r.val r.property).toPMF.map
            F z).toReal : ℂ) := by
  intro p map
  rw [p.fiberLaw_complexMean]
  have hcongr : p.complexMean (fun y => coefficient (principalResidueLabel q (map y)) *
      (if F (map y) = z then 1 else 0)) =
      p.complexMean (fun y => coefficient (progressionPrincipalResidue B h step c q
        (principalResidueLabel q y)) * (if F (map y) = z then 1 else 0)) := by
    unfold FiniteProbabilityWeights.complexMean
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : p.weight y = 0
    · simp only [hy, Complex.ofReal_zero, zero_mul]
    · dsimp only [map]
      rw [containedProgressionTupleMap_residue_of_weight_ne_zero B h L H step c hL hH hsubset q y hy]
  have hd := forecastInactive_indicator_disintegration p (principalResidueLabel q)
    (fun y => F (map y)) z (fun r => coefficient (progressionPrincipalResidue B h step c q r))
  refine hcongr.trans (hd.trans ?_)
  apply Finset.sum_congr rfl
  intro r _
  have hm :
      (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r.val r.property).toPMF.map F =
      (p.condition (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) r.property).toPMF.map
        (fun y => F (map y)) := by
    rw [containedSupportedProgressionLaw, FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
    rfl
  rw [hm]

end Erdos3

end

end OAI
