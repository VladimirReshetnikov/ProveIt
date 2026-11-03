import DiophantineConsistency.ArithmeticConstructionVariationCompact44
import DiophantineConsistency.ArithmeticConstructionUnitCompact44

/-! Bounded attempt: turn an explicitly supplied pair of valid packings and
the exact dummy perturbation into the compact Gamma rank identity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactRankVariation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticPacking
open DiophantineConsistency.ArithmeticConstructionVariationCompact44
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def windowRank (K N s c : V) (X : V → V) : V :=
  ((Exp.exp (590069*N) - 1) * (Exp.exp (590069*N) - Fw 590069 K N s X) +
    alpha 590069 K N s X) * (Exp.exp (590069*N)^2 - 1) + c

theorem rank_variation {K MC HP N s c : V} {X0 X1 δ : V → V}
    [𝚺₁-Function₁ X0] [𝚺₁-Function₁ X1] [𝚺₁-Function₁ δ]
    (h0 : PackingInput 590069 K MC HP N s X0)
    (h1 : PackingInput 590069 K MC HP N s X1)
    (hX : ∀ j < N, X1 j = X0 j + Exp.exp (67*1063) * δ j)
    (hδ : ∀ j, δ j ≤ 1)
    (hsafe : ∀ j, δ j ≠ 0 → j+1 < N ∧ j+s < N) :
    windowRank K N s c X1 + Gamma K N s * bsum 590069 δ N =
      windowRank K N s c X0 := by
  obtain ⟨hC, hF⟩ := variation (d := (590069 : V)) (ρ := Exp.exp (67*1063))
    (by norm_num) h0 h1 (exp_monotone.mpr (by norm_num)) hX hδ hsafe
  have hrs := rank_shift (q := Exp.exp (590069*N)) (c := c)
    (one_le_exp _) (packing_alpha h0).2 (packing_alpha h1).2 hC hF
  unfold windowRank Gamma
  rw [← hrs]
  ring

theorem calibrated_rank {K MC HP N s c : V} {X0 X1 δ : V → V}
    [𝚺₁-Function₁ X0] [𝚺₁-Function₁ X1] [𝚺₁-Function₁ δ]
    (h0 : PackingInput 590069 K MC HP N s X0)
    (h1 : PackingInput 590069 K MC HP N s X1)
    (hX : ∀ j < N, X1 j = X0 j + Exp.exp (67*1063) * δ j)
    (hδ : ∀ j, δ j ≤ 1)
    (hsafe : ∀ j, δ j ≠ 0 → j+1 < N ∧ j+s < N)
    (hcal : (Gamma K N s * bsum 590069 δ N + 590069*s) % (590069*N) =
      windowRank K N s c X0 % (590069*N)) :
    windowRank K N s c X1 % (590069*N) = (590069*s) % (590069*N) := by
  exact calibrated (mul_pos (by norm_num) (lt_trans _root_.zero_lt_one h0.N_gt))
    (rank_variation h0 h1 hX hδ hsafe) hcal

#print axioms rank_variation
#print axioms calibrated_rank
end CompactRankVariation
