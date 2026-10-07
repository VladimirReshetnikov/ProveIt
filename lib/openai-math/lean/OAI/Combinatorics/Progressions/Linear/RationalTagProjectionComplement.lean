import OAI.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction
import OAI.Combinatorics.Progressions.Sampling.RealMatrixSpecifiedGrid

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {T : Type*} [Fintype T]

noncomputable def rationalTagProjectionComplement (P : Matrix T T ℚ) :
    (T → ℝ) →ₗ[ℝ] (T → ℝ) :=
  LinearMap.id - Matrix.mulVecLin (fun i j => (P i j : ℝ))

@[simp] theorem rationalTagProjectionComplement_apply (P : Matrix T T ℚ) (x : T → ℝ) :
    rationalTagProjectionComplement P x = x - (fun i j => (P i j : ℝ)) *ᵥ x := rfl

theorem rationalTagProjectionComplement_eq_zero_of_mem
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x)
    (U : Submodule ℝ (T → ℝ)) (hU : U ≤ realRationalCoordinateSpan V)
    {x : T → ℝ} (hx : x ∈ U) : rationalTagProjectionComplement P x = 0 := by
  change x - Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = 0
  rw [hfix x (hU hx), sub_self]

theorem rationalTagProjectionComplement_ker
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x) :
    LinearMap.ker (rationalTagProjectionComplement P) = realRationalCoordinateSpan V := by
  ext x
  change x - Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = 0 ↔
    x ∈ realRationalCoordinateSpan V
  constructor
  · intro hx
    rw [sub_eq_zero] at hx
    rw [hx, ← hrange]
    exact ⟨x, rfl⟩
  · intro hx
    rw [hfix x hx, sub_self]

theorem rationalTagProjectionComplement_idempotent
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x)
    (x : T → ℝ) :
    rationalTagProjectionComplement P (rationalTagProjectionComplement P x) =
      rationalTagProjectionComplement P x := by
  let L := Matrix.mulVecLin (fun i j => (P i j : ℝ))
  have hmem : L x ∈ realRationalCoordinateSpan V := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hLL : L (L x) = L x := hfix _ hmem
  change x - L x - L (x - L x) = x - L x
  rw [map_sub, hLL, sub_self, sub_zero]

theorem rationalTagProjectionComplement_entry_bound
    (P : Matrix T T ℚ) {H : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) (a i : T) :
    |rationalTagProjectionComplement P (Pi.single a 1) i| ≤ 1 + H := by
  classical
  have he : ((fun i j => (P i j : ℝ)) *ᵥ Pi.single a 1) i = (P i a : ℝ) :=
    congrFun (Matrix.mulVec_single_one (Matrix.of fun i j => (P i j : ℝ)) a) i
  rw [rationalTagProjectionComplement_apply, Pi.sub_apply, he]
  have hsingle : |(Pi.single a (1 : ℝ) : T → ℝ) i| ≤ (1 : ℝ) := by
    by_cases hai : a = i
    · subst i; simp
    · simp [hai]
  calc
    _ ≤ |(Pi.single a (1 : ℝ) : T → ℝ) i| + |(P i a : ℝ)| := abs_sub _ _
    _ ≤ 1 + |H| := add_le_add hsingle ((hP i a).trans (le_abs_self H))
    _ = 1 + H := by rw [abs_of_nonneg hH]

theorem rationalTagProjectionComplement_coordinate_bound
    (P : Matrix T T ℚ) {H : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) (x : T → ℝ) (i : T) :
    |rationalTagProjectionComplement P x i| ≤
      (1 + (Fintype.card T : ℝ) * H) * ‖x‖ := by
  classical
  have hx (j : T) : |x j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hrow : |((fun i j => (P i j : ℝ)) *ᵥ x) i| ≤
      (Fintype.card T : ℝ) * H * ‖x‖ := by
    calc
      _ ≤ ∑ j, |(P i j : ℝ) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : T, H * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hP i j) (hx j) (abs_nonneg _) hH
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [rationalTagProjectionComplement_apply, Pi.sub_apply]
  calc
    _ ≤ |x i| + |((fun i j => (P i j : ℝ)) *ᵥ x) i| := abs_sub _ _
    _ ≤ ‖x‖ + (Fintype.card T : ℝ) * H * ‖x‖ := add_le_add (hx i) hrow
    _ = _ := by ring

theorem rationalTagProjectionComplement_coordinate_exp_bound
    (P : Matrix T T ℚ) {p h : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h)
    (hdim : (Fintype.card T : ℝ) ≤ p)
    (hP : ∀ i j, rationalLogHeight (P i j) ≤ h) (x : T → ℝ) (i : T) :
    |rationalTagProjectionComplement P x i| ≤ Real.exp (p + h + 1) * ‖x‖ := by
  have hentry : ∀ i j, |(P i j : ℝ)| ≤ Real.exp h := fun i j =>
    (rational_abs_real_le_numerator (P i j)).trans
      ((rationalLogHeight_le_iff _ _).mp (hP i j)).1
  apply (rationalTagProjectionComplement_coordinate_bound P (Real.exp_nonneg _) hentry x i).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hdimexp : (Fintype.card T : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have h1 : 1 ≤ Real.exp (p + h) := Real.one_le_exp_iff.mpr (add_nonneg hp hh)
  calc
    1 + (Fintype.card T : ℝ) * Real.exp h ≤ 1 + Real.exp p * Real.exp h := by gcongr
    _ = 1 + Real.exp (p + h) := by rw [Real.exp_add]
    _ ≤ 2 * Real.exp (p + h) := by linarith
    _ ≤ Real.exp 1 * Real.exp (p + h) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p + h + 1) := by rw [← Real.exp_add]; congr 1; ring

theorem rationalTagProjectionComplement_eq_iff_sub_mem
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x) (x y : T → ℝ) :
    rationalTagProjectionComplement P x = rationalTagProjectionComplement P y ↔
      x - y ∈ realRationalCoordinateSpan V := by
  rw [← rationalTagProjectionComplement_ker P V hrange hfix,
    LinearMap.mem_ker, map_sub, sub_eq_zero]

theorem rationalTagProjectionComplement_denominator_grid
    (P : Matrix T T ℚ) (D l : ℕ)
    (hP : ∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = z)
    (x : T → ℝ) (hx : x ∈ realDenominatorGrid l) :
    rationalTagProjectionComplement P x ∈ realDenominatorGrid (D * l) :=
  real_matrix_complement_linearMap_specified_denominator_grid
    (fun i j => (P i j : ℝ)) D l hP x hx

theorem rationalTagProjectionComplement_integer_grid
    (P : Matrix T T ℚ) (D : ℕ)
    (hP : ∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = z)
    (x : T → ℤ) :
    ∃ z : T → ℤ, ∀ i,
      (D : ℝ) * rationalTagProjectionComplement P (fun j => (x j : ℝ)) i = (z i : ℝ) := by
  have hx : (fun j => (x j : ℝ)) ∈ realDenominatorGrid 1 :=
    ⟨x, by ext j; simp⟩
  obtain ⟨z, hz⟩ := rationalTagProjectionComplement_denominator_grid P D 1 hP _ hx
  refine ⟨z, fun i => ?_⟩
  have hi := congrFun hz i
  simpa only [mul_one, Pi.smul_apply, smul_eq_mul] using hi.symm

namespace VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedRealMatrixProjection_complement
    (P : ∀ j, Matrix (J j) (J j) ℚ) (j : Fin m) :
    LinearMap.id - fullTaggedRealMatrixProjection J P j =
      rationalTagProjectionComplement (P j) := rfl

end VectorPolynomial
end Erdos3

end

end OAI
