import GowersSzemeredi.Proofs14Product

/-! The Fourier-frequency graph used at the start of Corollary 16.11,
including its exact density and product-property parameter. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Failure of degree-k+1 uniformity yields a dense graph of large Fourier
frequencies with the product property, without a modulus-size threshold. -/
theorem section16_large_frequency_graph {N k : Nat} [NeZero N]
    (alpha : Real) (ha : 0 < alpha) (haone : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (hnot : ¬ UniformOfDegree f alpha (k + 1)) :
    ∃ B : Finset (Point N k), ∃ phi : Point N k → ZMod N,
      alpha / 2 * (N : Real) ^ k ≤ B.card ∧
      HasProductProperty B phi (alpha / 2) ∧
      ∀ y ∈ B, alpha / 2 * N ≤ ‖fourier (cubeDifference f y) (phi y)‖ := by
  classical
  have hahalf : 0 < alpha / 2 := by positivity
  have hahalfOne : alpha / 2 ≤ 1 := by linarith
  obtain ⟨hi_ii, hii_iii, _, _, _, hvi_iii, _, hvii_vi⟩ :=
    lemma_3_1_holds N (k + 1) f (by omega) hf alpha (alpha / 2) (alpha / 2)
      ha.le haone hahalf.le hahalfOne hahalf.le hahalfOne
  have hnotvii : ¬ higherUniformConditionvii f (alpha / 2) (k + 1) := by
    intro hvii
    have hvi := hvii_vi le_rfl hvii
    have hiii := hvi_iii (by linarith) hvi
    exact hnot (hi_ii.mpr (hii_iii.mpr hiii))
  let Good : Point N k → Prop := fun y ↦
    ∃ r : ZMod N, alpha / 2 * N ≤ ‖fourier (cubeDifference f y) r‖
  have hcount : alpha / 2 * (N : Real) ^ k < (countWhere Good : Real) := by
    unfold higherUniformConditionvii at hnotvii
    simp only [Nat.add_sub_cancel] at hnotvii
    exact lt_of_not_ge hnotvii
  let B : Finset (Point N k) := Finset.univ.filter Good
  let phi : Point N k → ZMod N := fun y ↦ if h : Good y then h.choose else 0
  have hfreq : ∀ y ∈ B, alpha / 2 * N ≤ ‖fourier (cubeDifference f y) (phi y)‖ := by
    intro y hy
    have h : Good y := (Finset.mem_filter.mp hy).2
    dsimp only [phi]
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨B, phi, ?_, ?_, hfreq⟩
  · have hcountEq : countWhere Good = B.card := by
      unfold countWhere B
      apply congrArg Finset.card
      ext y
      simp
    rw [hcountEq] at hcount
    exact hcount.le
  · exact lemma_14_2_holds N k (alpha / 2) f B phi hahalf hf hfreq

end LeanProofs.GowersSzemeredi
