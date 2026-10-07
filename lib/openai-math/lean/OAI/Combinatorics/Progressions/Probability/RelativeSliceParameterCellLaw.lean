import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistCellSelection

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem complexMean_finitePushforward_relativeSlice {U T : Type*} [Fintype U] [Fintype T]
    (p : FiniteProbabilityWeights U) (f : U → T) (g : T → ℂ) :
    (p.finitePushforward f).complexMean g = p.complexMean (fun u => g (f u)) := by
  simp only [complexMean, finitePushforward, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [apply_ite, ite_mul]

theorem uniform_finitePushforward_complexMean {U T : Type*}
    [Fintype U] [Nonempty U] [Fintype T] (f : U → T) (g : T → ℂ) :
    ((uniform U).finitePushforward f).complexMean g = 𝔼 u, g (f u) := by
  rw [complexMean_finitePushforward_relativeSlice, uniform_complexMean]

theorem uniform_condition_complexMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (f : Ω → ℂ) :
    ((uniform Ω).condition G hG).complexMean f = 𝔼 x ∈ G, f x := by
  have hc : (Fintype.card Ω : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : (G.card : ℂ) ≠ 0 := by
    have hgNat : G.card ≠ 0 := by
      intro hz
      rw [uniform_mass, hz, Nat.cast_zero, zero_div] at hG
      exact (lt_irrefl _ hG)
    exact_mod_cast hgNat
  have hm : (((uniform Ω).mass G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  apply (mul_left_cancel₀ hm)
  rw [mass_mul_condition_complexMean, uniform_complexMean, uniform_mass,
    Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  have hsum : (∑ x, if x ∈ G then f x else 0) = ∑ x ∈ G, f x := by simp
  rw [hsum, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  field_simp

end FiniteProbabilityWeights

namespace BoxProgressionPartition

variable {I : Type*} [Fintype I] [DecidableEq I] {L : I → ℕ}
  [Nonempty (∀ i, Fin (L i))] (Q : ∀ i, FiniteProgressionPartition (L i))

theorem uniform_cell_mass_pos (c : ∀ i, (Q i).Label)
    (hlen : ∀ i, 0 < (Q i).length (c i)) :
    0 < (FiniteProbabilityWeights.uniform (∀ i, Fin (L i))).mass (partitionCell (cell Q) c) := by
  rw [FiniteProbabilityWeights.uniform_mass, card_cell]
  apply div_pos
  · exact_mod_cast Finset.prod_pos (fun i _ => hlen i)
  · exact Nat.cast_pos.mpr Fintype.card_pos

theorem uniform_condition_complexMean (c : ∀ i, (Q i).Label)
    (hc : 0 < (FiniteProbabilityWeights.uniform (∀ i, Fin (L i))).mass
      (partitionCell (cell Q) c)) (f : (∀ i, Fin (L i)) → ℂ) :
    ((FiniteProbabilityWeights.uniform (∀ i, Fin (L i))).condition
      (partitionCell (cell Q) c) hc).complexMean f =
      𝔼 u : (∀ i, Fin ((Q i).length (c i))), f (point Q c u) := by
  rw [FiniteProbabilityWeights.uniform_condition_complexMean, expect_cell_complex]

end BoxProgressionPartition

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceLaw_complexMean (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℂ) :
    (S.fullSliceLaw hlen).complexMean f = 𝔼 u, f (S.fullSlicePointInIntegerBox u) := by
  let : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0, hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

theorem fullSliceParameterCell_complexMean (S : ResidueBoxSlice N q)
    [Nonempty (∀ i, Fin (S.length i))]
    (Q : ∀ i, FiniteProgressionPartition (S.length i)) (c : ∀ i, (Q i).Label)
    (hc : 0 < (FiniteProbabilityWeights.uniform (∀ i, Fin (S.length i))).mass
      (partitionCell (BoxProgressionPartition.cell Q) c)) (f : integerBox N → ℂ) :
    ((FiniteProbabilityWeights.uniform (∀ i, Fin (S.length i))).condition
      (partitionCell (BoxProgressionPartition.cell Q) c) hc).complexMean
        (fun t => f (S.fullSlicePointInIntegerBox t)) =
      𝔼 u : (∀ i, Fin ((Q i).length (c i))),
        f (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) :=
  BoxProgressionPartition.uniform_condition_complexMean Q c hc _

end ResidueBoxSlice
end Erdos3

end

end OAI
