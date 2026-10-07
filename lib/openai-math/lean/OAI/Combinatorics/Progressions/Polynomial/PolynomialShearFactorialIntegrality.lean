import OAI.Combinatorics.Progressions.Estimates.WeightedLoweringAction
import OAI.Combinatorics.Progressions.Lattices.FactorialIntegerScalars
import OAI.Combinatorics.Progressions.Lattices.IntegerWeightedLoweringGroup
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

theorem WeightedLoweringAut.difference_pow_degree (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ k) P ∈ weightedSupportLE w n := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact weightedSupportLT_le (e.difference_lower ih)

theorem WeightedLoweringAut.difference_pow_lower (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ (k + 1)) P ∈ weightedSupportLT w n := by
  rw [pow_succ', Module.End.mul_apply]
  exact e.difference_lower (e.difference_pow_degree hP k)

variable [Algebra ℚ R]

noncomputable def polynomialShearLogOn (e : WeightedLoweringAut w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) :=
  nilpotentLog ((e.degreeAction n).toLinearMap - 1)

theorem polynomialShearLogOn_sum (e : WeightedLoweringAut w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearLogOn e n P : MvPolynomial σ R) =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℚ) ^ (k + 1) / k) •
        (polynomialHomDifference e.val.toAlgHom ^ k) (P : MvPolynomial σ R) := by
  simp [polynomialShearLogOn,
    nilpotentLog_eq_sum (a := (e.degreeAction n).toLinearMap - 1)
      (e.degreeAction_difference_pow_zero n), e.degreeAction_difference_pow_coe]

theorem polynomialShearLogOn_mono (e : WeightedLoweringAut w R)
    {m n : ℕ} (hmn : m ≤ n) (P : weightedSupportLE (R := R) w m) :
    (polynomialShearLogOn e n ⟨P.val, weightedSupportLE_mono hmn P.property⟩ :
      MvPolynomial σ R) = (polynomialShearLogOn e m P : MvPolynomial σ R) := by
  let inc : weightedSupportLE (R := R) w m →ₗ[R] weightedSupportLE (R := R) w n :=
    Submodule.inclusion (fun _ h => weightedSupportLE_mono hmn h)
  have hc : ((e.degreeAction n).toLinearMap - 1) ∘ₗ inc =
      inc ∘ₗ ((e.degreeAction m).toLinearMap - 1) := by
    apply LinearMap.ext
    intro Q
    rfl
  have h := nilpotentLog_intertwine (e.degreeAction_difference_nilpotent m)
    (e.degreeAction_difference_nilpotent n) hc
  exact congrArg Subtype.val (LinearMap.congr_fun h P)

theorem polynomialShearLogOn_leibniz (e : WeightedLoweringAut w R) (m n : ℕ)
    (P : weightedSupportLE (R := R) w m) (Q : weightedSupportLE (R := R) w n) :
    (polynomialShearLogOn e (m + n) (weightedPolynomialMul w m n P Q) : MvPolynomial σ R) =
      (polynomialShearLogOn e m P : MvPolynomial σ R) * Q.val +
        P.val * (polynomialShearLogOn e n Q : MvPolynomial σ R) := by
  have h := nilpotentLog_bilinear (weightedPolynomialMul (R := R) w m n)
    (e.degreeAction m).toLinearMap (e.degreeAction n).toLinearMap
    (e.degreeAction (m + n)).toLinearMap
    (e.degreeAction_difference_nilpotent m) (e.degreeAction_difference_nilpotent n)
    (e.degreeAction_difference_nilpotent (m + n))
    (fun x y => Subtype.ext (map_mul e.val x.val y.val)) P Q
  exact congrArg Subtype.val h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearLogValue (e : WeightedLoweringAut w R)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  polynomialShearLogOn e (P.weightedTotalDegree w)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩

theorem polynomialShearLogValue_eq_on (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P = (polynomialShearLogOn e n ⟨P, hP⟩ : MvPolynomial σ R) :=
  (polynomialShearLogOn_mono e ((mem_weightedSupportLE_iff w n P).mp hP)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩).symm

theorem polynomialShearLogValue_eq_sum (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P = ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℚ) ^ (k + 1) / k) • (polynomialHomDifference e.val.toAlgHom ^ k) P := by
  rw [polynomialShearLogValue_eq_on e hP]
  exact polynomialShearLogOn_sum e n ⟨P, hP⟩

theorem polynomialShearLogValue_add (e : WeightedLoweringAut w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearLogValue e (P + Q) = polynomialShearLogValue e P + polynomialShearLogValue e Q := by
  let n := P.weightedTotalDegree w + Q.weightedTotalDegree w
  have hp : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (Nat.le_add_right _ _)
  have hq : Q ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n Q).mpr (Nat.le_add_left _ _)
  rw [polynomialShearLogValue_eq_on e ((weightedSupportLE w n).add_mem hp hq),
    polynomialShearLogValue_eq_on e hp, polynomialShearLogValue_eq_on e hq]
  exact congrArg Subtype.val ((polynomialShearLogOn e n).map_add ⟨P, hp⟩ ⟨Q, hq⟩)

theorem polynomialShearLogValue_smul (e : WeightedLoweringAut w R)
    (c : R) (P : MvPolynomial σ R) :
    polynomialShearLogValue e (c • P) = c • polynomialShearLogValue e P := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearLogValue_eq_on e ((weightedSupportLE w _).smul_mem c hp),
    polynomialShearLogValue_eq_on e hp]
  exact congrArg Subtype.val ((polynomialShearLogOn e _).map_smul c ⟨P, hp⟩)

theorem polynomialShearLogValue_mul (e : WeightedLoweringAut w R)
    (P Q : MvPolynomial σ R) :
    polynomialShearLogValue e (P * Q) =
      polynomialShearLogValue e P * Q + P * polynomialShearLogValue e Q := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  have hq : Q ∈ weightedSupportLE w (Q.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ Q).mpr le_rfl
  rw [polynomialShearLogValue_eq_on e (weightedSupportLE_mul hp hq),
    polynomialShearLogValue_eq_on e hp, polynomialShearLogValue_eq_on e hq]
  exact polynomialShearLogOn_leibniz e _ _ ⟨P, hp⟩ ⟨Q, hq⟩

theorem polynomialShearLogValue_C (e : WeightedLoweringAut w R) (c : R) :
    polynomialShearLogValue e (C c) = 0 := by
  rw [polynomialShearLogValue_eq_sum e (weightedSupportLE_C w 0 c)]
  simp

noncomputable def polynomialShearLogDerivation (e : WeightedLoweringAut w R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) where
  toFun := polynomialShearLogValue e
  map_add' := polynomialShearLogValue_add e
  map_smul' := polynomialShearLogValue_smul e
  map_one_eq_zero' := by simpa using polynomialShearLogValue_C e 1
  leibniz' P Q := by
    change polynomialShearLogValue e (P * Q) =
      P • polynomialShearLogValue e Q + Q • polynomialShearLogValue e P
    rw [polynomialShearLogValue_mul]
    simp only [smul_eq_mul]
    ring

theorem polynomialShearLogValue_lower (e : WeightedLoweringAut w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearLogValue e P ∈ weightedSupportLT w n := by
  rw [polynomialShearLogValue_eq_sum e hP, Finset.sum_range_succ']
  simp only [Nat.cast_zero, div_zero, zero_smul, add_zero]
  apply (weightedSupportLT w n).sum_mem
  intro k hk
  exact (weightedSupportLT (R := R) w n).restrictScalars ℚ |>.smul_mem _
    (e.difference_pow_lower hP k)

noncomputable def polynomialShearLog (e : WeightedLoweringAut w R) :
    PolynomialShearLieAlgebra w R :=
  ⟨polynomialShearLogDerivation e, fun i => by
    change polynomialShearLogValue e (X i) ∈ weightedSupportDrop w (w i) 1
    rw [weightedSupportDrop_one]
    exact polynomialShearLogValue_lower e (weightedSupportLE_X w i)⟩

theorem polynomialShearLog_apply (e : WeightedLoweringAut w R) (P : MvPolynomial σ R) :
    (polynomialShearLog e).val P = polynomialShearLogValue e P := rfl

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearLog_end (e : WeightedLoweringAut w R) (n : ℕ) :
    polynomialShearEnd (polynomialShearLog e) n = polynomialShearLogOn e n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact polynomialShearLogValue_eq_on e P.property

theorem polynomialShearExp_degreeAction (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    ((polynomialShearExpAut D).degreeAction n).toLinearMap = polynomialShearExpOn D n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact polynomialShearExp_eq_on D P.property

theorem polynomialShearExp_log (e : WeightedLoweringAut w R) :
    polynomialShearExpAut (polynomialShearLog e) = e := by
  apply Subtype.ext
  apply DFunLike.ext
  intro P
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExpAut_apply, polynomialShearExp_eq_on _ hp]
  unfold polynomialShearExpOn
  rw [polynomialShearLog_end, polynomialShearLogOn,
    exp_nilpotentLog (e.degreeAction_difference_nilpotent _)]
  simp [WeightedLoweringAut.degreeAction_apply_coe]

theorem polynomialShearLog_exp (D : PolynomialShearLieAlgebra w R) :
    polynomialShearLog (polynomialShearExpAut D) = D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  change polynomialShearLogValue (polynomialShearExpAut D) (X i) = D.val (X i)
  rw [polynomialShearLogValue_eq_on _ (weightedSupportLE_X w i)]
  unfold polynomialShearLogOn
  rw [polynomialShearExp_degreeAction, polynomialShearExpOn,
    nilpotentLog_exp_sub_one (polynomialShearEnd_isNilpotent D (w i))]
  rfl

noncomputable def polynomialShearExpLogEquiv (w : σ → ℕ) :
    PolynomialShearLieAlgebra w R ≃ WeightedLoweringAut w R where
  toFun := polynomialShearExpAut
  invFun := polynomialShearLog
  left_inv := polynomialShearLog_exp
  right_inv := polynomialShearExp_log

theorem polynomialShearExpAut_injective :
    Function.Injective (polynomialShearExpAut (w := w) (R := R)) :=
  (polynomialShearExpLogEquiv w).injective

theorem polynomialShearExpAut_surjective :
    Function.Surjective (polynomialShearExpAut (w := w) (R := R)) :=
  (polynomialShearExpLogEquiv w).surjective

theorem polynomialShearLog_injective :
    Function.Injective (polynomialShearLog (w := w) (R := R)) :=
  (polynomialShearExpLogEquiv w).symm.injective

theorem polynomialShearLog_surjective :
    Function.Surjective (polynomialShearLog (w := w) (R := R)) :=
  (polynomialShearExpLogEquiv w).symm.surjective

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def symbolicLogSlot (A : PolynomialSlots σ d w) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin d) ℝ :=
  ∑ k ∈ Finset.range (w i + 1), ((-1 : ℚ) ^ (k + 1) / k) •
    (polynomialHomDifference A.symbolicShearHom ^ k) (X (Sum.inr i))

theorem symbolicLogSlot_degree (A : PolynomialSlots σ d w) (i : Fin d) :
    A.symbolicLogSlot i ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i) := by
  apply (weightedSupportLE _ _).sum_mem
  intro k hk
  exact (weightedSupportLE (Sum.elim (fun _ : σ => 1) w) (w i)).restrictScalars ℚ |>.smul_mem _
    (A.symbolicShearDifference_pow_degree k (weightedSupportLE_X _ (Sum.inr i)))

theorem symbolicLogSlot_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (A.symbolicLogSlot i) =
      (polynomialShearLog (A.loweringAt t)).val (X i) := by
  change patchParameterSpecialization t (A.symbolicLogSlot i) = polynomialShearLogValue (A.loweringAt t) (X i)
  rw [polynomialShearLogValue_eq_sum (A.loweringAt t) (weightedSupportLE_X w i)]
  unfold symbolicLogSlot
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, symbolicShearDifference_pow_specialization, patchParameterSpecialization_X_slot]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShear_scaled_pow (D : PolynomialShearLieAlgebra w ℚ)
    (c : ℚ) (k : ℕ) (P : MvPolynomial σ ℚ) :
    ((c • D).val.toLinearMap ^ k) P = c ^ k • (D.val.toLinearMap ^ k) P := by
  change ((c • D.val.toLinearMap) ^ k) P = _
  rw [smul_pow, LinearMap.smul_apply]

theorem polynomialShear_factorial_exp_integral (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D : PolynomialShearLieAlgebra w ℚ)
    (hD : ∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) :
    polynomialShearExpAut ((s.factorial : ℚ) • D) ∈ integerWeightedLoweringSubgroup w := by
  intro i
  rw [polynomialShearExpAut_apply, polynomialShearExp_eq_sum _
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i))]
  apply (integerCoefficientPolynomials σ).sum_mem
  intro k hk
  rw [polynomialShear_scaled_pow, smul_smul]
  exact integerCoefficientPolynomials_rat_smul
    (factorial_exp_scalar_integer s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    (integerPolynomialDerivation_pow D.val hD (integerCoefficientPolynomials_X i) k)

theorem polynomialShear_factorial_log_integral (s : ℕ) (hw : ∀ i, w i ≤ s)
    (e : WeightedLoweringAut w ℚ) (he : e ∈ integerWeightedLoweringSubgroup w) (i : σ) :
    (s.factorial : ℚ) • (polynomialShearLog e).val (X i) ∈ integerCoefficientPolynomials σ := by
  rw [polynomialShearLog_apply, polynomialShearLogValue_eq_sum _
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)), Finset.smul_sum]
  apply (integerCoefficientPolynomials σ).sum_mem
  intro k hk
  rw [smul_smul]
  exact integerCoefficientPolynomials_rat_smul
    (factorial_log_scalar_integer s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    (integerWeightedLowering_difference_pow e he (integerCoefficientPolynomials_X i) k)

end Erdos3

end

end OAI
