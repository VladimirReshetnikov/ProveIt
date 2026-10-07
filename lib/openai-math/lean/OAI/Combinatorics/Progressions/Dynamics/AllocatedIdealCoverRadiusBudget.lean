import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverSupport_le_exp {P : ℝ} (hP : 0 ≤ P) (j : Fin m)
    (hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ Real.exp P)
    (hI : partitionedIdealRadius α m + 1 ≤ Real.exp P)
    (hn : (n j : ℝ) ≤ Real.exp P)
    (hW : ∀ i : Fin (n j), allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ Real.exp P) :
    allocatedIdealCoverSupport (G := G) B rowSets j ≤ Real.exp (2 * P + 2) := by
  have hs : (∑ i : Fin (n j), (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1)) ≤
      Real.exp (2 * P) := by
    calc
      _ ≤ ∑ _i : Fin (n j), Real.exp P := Finset.sum_le_sum (fun i _ => hW i)
      _ = (n j : ℝ) * Real.exp P := by simp
      _ ≤ Real.exp P * Real.exp P := mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : Real.exp P ≤ Real.exp (2 * P) := Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold allocatedIdealCoverSupport
  calc
    _ ≤ Real.exp P + Real.exp P + Real.exp (2 * P) := add_le_add (add_le_add hA hI) hs
    _ ≤ 3 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 2 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem allocatedIdealCoverRadius_inv_le_exp {P : ℝ} (hP : 0 ≤ P)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m)
    (hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ Real.exp P)
    (hI : partitionedIdealRadius α m + 1 ≤ Real.exp P)
    (hn : (n j : ℝ) ≤ Real.exp P)
    (hW : ∀ i : Fin (n j), allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ Real.exp P)
    (hr : ((rowSets j).card : ℝ) ≤ Real.exp P)
    (hd : (Fintype.card (I j) : ℝ) ≤ Real.exp P) (hCP : C j ≤ Real.exp P) :
    (allocatedIdealCoverRadius (G := G) B rowSets C j)⁻¹ ≤ Real.exp (8 * P + 14) := by
  have hp : Real.exp P ≤ Real.exp (2 * P + 2) := Real.exp_le_exp.mpr (by linarith)
  have h := finiteRowChartRadius_inv_le_exp (rowSets j).card (Fintype.card (I j))
    (hC j) (allocatedIdealCoverSupport_nonneg B rowSets j) (by positivity : 0 ≤ 2 * P + 2)
    (hr.trans hp) (hd.trans hp) (hCP.trans hp)
    (allocatedIdealCoverSupport_le_exp B rowSets hP j hA hI hn hW)
  have he : 4 * (2 * P + 2) + 6 = 8 * P + 14 := by ring
  simpa only [allocatedIdealCoverRadius, he] using h

theorem allocatedIdealCoverRadius_le_one (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedIdealCoverRadius (G := G) B rowSets C j ≤ 1 := by
  have ht := allocatedIdealCoverSupport_nonneg (G := G) B rowSets j
  have hc := hC j
  unfold allocatedIdealCoverRadius finiteRowChartRadius
  apply (div_le_one (by positivity)).mpr
  calc
    (1 : ℝ) ≤ 4 * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr <;> linarith [hC j]

end Erdos3.VectorPolynomial

end

end OAI
