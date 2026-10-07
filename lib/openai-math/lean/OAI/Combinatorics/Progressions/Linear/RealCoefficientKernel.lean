import OAI.Combinatorics.Progressions.Estimates.FreeCorrelationRelationRefinement

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficientFourSpace_eq_sup (d : Fin (s + 1)) :
    D.coefficientFourSpace d = D.spaces d ⊔
      Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2) := by
  let F := W.rank.filtration
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change F.fourHorizontalMap d.val w ∈ F.horizontalImageOfSubmodule (D.spaces d) d.val at hw
    obtain ⟨z, hz, he⟩ := hw
    apply Submodule.mem_sup.mpr
    refine ⟨z.val, hz, w.val - z.val, ?_, by abel⟩
    apply Submodule.mem_pi.mpr
    intro k _
    exact (F.higherHorizontalMk_eq d.val _ _).mp (congrFun he.symm k)
  · intro hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hx' := D.spaces_le_fourHorizontalLayer d hx
    have hy' : y ∈ F.fourHorizontalLayer d.val := by
      apply (F.mem_fourHorizontalLayer d.val y).mpr
      intro k
      exact F.lex_antitone (Or.inr ⟨rfl, by omega⟩) ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))
    let z : F.fourHorizontalLayer d.val := ⟨x, hx'⟩
    let w : F.fourHorizontalLayer d.val := ⟨x + y, (F.fourHorizontalLayer d.val).add_mem hx' hy'⟩
    apply (D.mem_coefficientFourSpace d w).mpr
    change F.fourHorizontalMap d.val w ∈ F.horizontalImageOfSubmodule (D.spaces d) d.val
    refine ⟨z, hx, ?_⟩
    funext k
    apply (F.higherHorizontalMk_eq d.val _ _).mpr
    change x k - (x k + y k) ∈ F.layer d.val 2
    simpa only [sub_add_cancel_left] using
      (F.layer d.val 2).neg_mem ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))

theorem spaces_le_coefficientFourSpace (d : Fin (s + 1)) :
    D.spaces d ≤ D.coefficientFourSpace d := by
  rw [D.coefficientFourSpace_eq_sup]
  exact le_sup_left

theorem fourKernel_le_coefficientFourSpace (d : Fin (s + 1)) :
    Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2) ≤
      D.coefficientFourSpace d := by
  rw [D.coefficientFourSpace_eq_sup]
  exact le_sup_right

theorem coefficientFourSpace_add_kernel_iff (d : Fin (s + 1))
    (v z : Fin 4 → W.L) (hz : ∀ k, z k ∈ W.rank.filtration.layer d.val 2) :
    v + z ∈ D.coefficientFourSpace d ↔ v ∈ D.coefficientFourSpace d := by
  have hz' := D.fourKernel_le_coefficientFourSpace d
    (Submodule.mem_pi.mpr (fun k _ => hz k))
  exact Submodule.add_mem_iff_left _ hz'

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem real_fourKernel_le_coefficientFourSpace (d : Fin (s + 1))
    (v : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hv : ∀ k, v k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v ∈ D.realCoefficientFourSpace d := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  have hbase : e.symm v ∈
      (Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2)).baseChange ℝ := by
    apply (mem_realified_four_product_iff _ _).mpr
    intro k
    change e (e.symm v) k ∈ _
    rw [e.apply_symm_apply]
    exact hv k
  exact ⟨e.symm v, Submodule.baseChange_mono ℝ (D.fourKernel_le_coefficientFourSpace d) hbase,
    e.apply_symm_apply v⟩

theorem realCoefficientFourSpace_add_kernel_iff (d : Fin (s + 1))
    (v z : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hz : ∀ k, z k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v + z ∈ D.realCoefficientFourSpace d ↔ v ∈ D.realCoefficientFourSpace d :=
  Submodule.add_mem_iff_left _ (D.real_fourKernel_le_coefficientFourSpace d z hz)

theorem realCoefficientFourSpace_congr_mod_kernel (d : Fin (s + 1))
    (v z : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hz : ∀ k, v k - z k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v ∈ D.realCoefficientFourSpace d ↔ z ∈ D.realCoefficientFourSpace d := by
  have h := D.real_fourKernel_le_coefficientFourSpace d (v - z) hz
  constructor
  · intro hv
    simpa only [sub_sub_cancel] using (D.realCoefficientFourSpace d).sub_mem hv h
  · intro hz
    simpa only [sub_add_cancel] using (D.realCoefficientFourSpace d).add_mem h hz

theorem realCoefficientFourSpace_log_product_correction_iff
    {κ : Type*} (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (d : Fin (s + 1)) (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α = d.val)
    (g h : Fin 4 → W.rank.filtration.associatedDegree.realification.PolynomialOrbit
      (fun _ : Unit => 1)) (E Q : Fin 4 → ℝ ⊗[ℚ] W.L) :
    (fun k => coefficients ((g k) * (h k)).log α) - E - Q ∈ D.realCoefficientFourSpace d ↔
      (fun k => coefficients (g k).log α + coefficients (h k).log α) - E - Q ∈
        D.realCoefficientFourSpace d := by
  apply D.realCoefficientFourSpace_congr_mod_kernel d
  intro k
  change (coefficients ((g k) * (h k)).log α - E k - Q k) -
    (coefficients (g k).log α + coefficients (h k).log α - E k - Q k) ∈ _
  have heq : (coefficients ((g k) * (h k)).log α - E k - Q k) -
      (coefficients (g k).log α + coefficients (h k).log α - E k - Q k) =
      coefficients ((g k) * (h k)).log α -
        (coefficients (g k).log α + coefficients (h k).log α) := by abel
  rw [heq]
  simpa only [hα] using W.rank.filtration.polynomialOrbit_log_mul_mod_rank_two hs c τ hG
    (fun _ : Unit => 1) α (g k) (h k)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
