import Surreal.HahnSeries.FiniteExponential
import Surreal.HahnSeries.ModulusStandardPart

/-!
# Finite-angle polar form in a complex Hahn field

Every nonzero complex Hahn series is its positive real Hahn modulus times
the finite exponential of an imaginary finite real angle. Two finite angles
give the same phase exactly when they differ by an ordinary integral multiple
of `2π`. This is the fixed-Hahn polar assertion in `e:prop-polar`.

The angle is built from the ordinary argument of the unit's residue and the
purely imaginary infinitesimal logarithm of its principal-unit part. No
exponential at an infinite angle or infinite actual-surreal embedding is used.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Multiplication by `i` after the real Hahn embedding. -/
def imaginaryHahn : ℝ⟦Γ⟧ →+ ℂ⟦Γ⟧ where
  toFun x := single 0 Complex.I * complexRealEmbedding x
  map_zero' := by simp
  map_add' x y := by simp only [map_add, mul_add]

@[simp] theorem coeff_imaginaryHahn (x : ℝ⟦Γ⟧) (g : Γ) :
    (imaginaryHahn x).coeff g = Complex.I * (x.coeff g : ℂ) := by
  change (single 0 Complex.I * complexRealEmbedding x).coeff g = _
  rw [single_zero_mul_eq_smul, coeff_smul, coeff_complexRealEmbedding, smul_eq_mul]

@[simp] theorem imaginaryHahn_single_zero (r : ℝ) :
    imaginaryHahn (single (0 : Γ) r) = single 0 ((r : ℂ) * Complex.I) := by
  ext g
  by_cases hg : g = 0 <;> simp [hg, mul_comm]

theorem imaginaryHahn_injective : Function.Injective (imaginaryHahn (Γ := Γ)) := by
  intro x y h
  apply _root_.HahnSeries.ext
  funext g
  simpa using congrArg (fun z : ℂ⟦Γ⟧ => (z.coeff g).im) h

@[simp] theorem orderTop_imaginaryHahn (x : ℝ⟦Γ⟧) :
    (imaginaryHahn x).orderTop = x.orderTop := by
  change (single 0 Complex.I * complexRealEmbedding x).orderTop = _
  rw [orderTop_mul, orderTop_single Complex.I_ne_zero, WithTop.coe_zero,
    zero_add, orderTop_complexRealEmbedding]

/-- A finite real angle gives a finite imaginary Hahn input. -/
def finiteImaginary : nonnegativeSubring Γ ℝ →+ nonnegativeSubring Γ ℂ where
  toFun x := ⟨imaginaryHahn (x : ℝ⟦Γ⟧), by
    change 0 ≤ (imaginaryHahn (x : ℝ⟦Γ⟧)).orderTop
    rw [orderTop_imaginaryHahn]
    exact x.property⟩
  map_zero' := by apply Subtype.ext; exact imaginaryHahn.map_zero
  map_add' x y := by apply Subtype.ext; exact imaginaryHahn.map_add _ _

@[simp] theorem coe_finiteImaginary (x : nonnegativeSubring Γ ℝ) :
    (finiteImaginary x : ℂ⟦Γ⟧) = imaginaryHahn (x : ℝ⟦Γ⟧) := rfl

/-- Every coefficientwise purely imaginary finite series has a finite real angle. -/
theorem exists_finiteImaginary_eq (q : nonnegativeSubring Γ ℂ)
    (hq : ∀ g, ((q : ℂ⟦Γ⟧).coeff g).re = 0) :
    ∃ θ : nonnegativeSubring Γ ℝ, finiteImaginary θ = q := by
  let r := ofLex (complexHahnLexEquiv (q : ℂ⟦Γ⟧)).im
  have hr : 0 ≤ r.orderTop := by
    apply le_orderTop_iff_forall.mpr
    intro g hg
    change (((q : ℂ⟦Γ⟧).coeff g).im) = 0
    rw [coeff_eq_zero_of_lt_orderTop (hg.trans_le q.property), Complex.zero_im]
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  apply _root_.HahnSeries.ext
  funext g
  apply Complex.ext <;> simp [r, hq g]

/-- The exact ordinary `2πℤ` ambiguity of finite real angles. -/
theorem finiteExp_finiteImaginary_eq_iff (θ φ : nonnegativeSubring Γ ℝ) :
    finiteExp (finiteImaginary θ) = finiteExp (finiteImaginary φ) ↔
      ∃ n : ℤ, (θ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧) = single 0 ((n : ℝ) * (2 * Real.pi)) := by
  rw [finiteExp_eq_finiteExp_iff]
  have hp (n : ℤ) :
      imaginaryHahn (single (0 : Γ) ((n : ℝ) * (2 * Real.pi))) =
        single 0 ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
    rw [imaginaryHahn_single_zero]
    congr 1
    push_cast
    ring
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, imaginaryHahn_injective ?_⟩
    rw [map_sub, hp]
    exact hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change imaginaryHahn (θ : ℝ⟦Γ⟧) - imaginaryHahn (φ : ℝ⟦Γ⟧) = _
    rw [← map_sub, hn, hp]

variable [DivisibleBy Γ ℕ]

@[simp] theorem complexModulus_inv (z : ℂ⟦Γ⟧) :
    complexModulus z⁻¹ = (complexModulus z)⁻¹ := by
  by_cases hz : z = 0
  · simp [hz]
  have h := complexModulus_mul z z⁻¹
  rw [mul_inv_cancel₀ hz, complexModulus_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem complexModulus_div (z w : ℂ⟦Γ⟧) :
    complexModulus (z / w) = complexModulus z / complexModulus w := by
  simp only [div_eq_mul_inv, complexModulus_mul, complexModulus_inv]

/-- A unit-circle Hahn series is the finite exponential of a finite imaginary angle. -/
theorem exists_finiteImaginary_exp_eq_of_modulus_eq_one (u : ℂ⟦Γ⟧)
    (hu : complexModulus u = 1) :
    ∃ θ : nonnegativeSubring Γ ℝ, finiteExp (finiteImaginary θ) = u := by
  let y : nonnegativeSubring Γ ℂ := ⟨u, (orderTop_eq_zero_of_complexModulus_eq_one u hu).ge⟩
  let c := u.coeff 0
  have hc : ‖c‖ = 1 := norm_coeff_zero_eq_one_of_complexModulus_eq_one u hu
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  let p := single 0 c⁻¹ * u
  have hp : complexModulus p = 1 := by
    change complexModulus (single 0 c⁻¹ * u) = 1
    rw [complexModulus_mul, complexModulus_single_zero, norm_inv, hc, inv_one, hu, mul_one]
    simp
  have hε : 0 < (p - 1).orderTop := orderTop_residue_normalization_sub_one_pos y hc0
  let a : nonnegativeSubring Γ ℂ :=
    ⟨single 0 ((Complex.arg c : ℂ) * Complex.I), orderTop_single_le⟩
  let b : nonnegativeSubring Γ ℂ := ⟨infLog (p - 1) hε, (infLog_orderTop_pos _ _).le⟩
  have hq : ∀ g, (((a + b : nonnegativeSubring Γ ℂ) : ℂ⟦Γ⟧).coeff g).re = 0 := by
    intro g
    change ((single 0 ((Complex.arg c : ℂ) * Complex.I) + infLog (p - 1) hε).coeff g).re = 0
    rw [coeff_add, Complex.add_re, infLog_re_eq_zero_of_modulus_eq_one p hε hp, add_zero]
    by_cases hg : g = 0 <;> simp [hg]
  obtain ⟨θ, hθ⟩ := exists_finiteImaginary_eq (a + b) hq
  refine ⟨θ, ?_⟩
  rw [hθ, finiteExp_add]
  have ha : finiteExp a = single 0 c := by
    change finiteExp (⟨single 0 ((Complex.arg c : ℂ) * Complex.I), orderTop_single_le⟩ :
      nonnegativeSubring Γ ℂ) = _
    rw [finiteExp_constant]
    congr 1
    simpa only [hc, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I c
  have hb : finiteExp b = p := by
    have h := (finiteExp_of_orderTop_pos _ (infLog_orderTop_pos (p - 1) hε)).trans
      (infExp_infLog (p - 1) hε)
    simpa only [add_sub_cancel] using h
  rw [ha, hb]
  change single 0 c * (single 0 c⁻¹ * u) = u
  rw [← mul_assoc, single_mul_single, zero_add, mul_inv_cancel₀ hc0, single_zero_one, one_mul]

/-- Every nonzero complex Hahn series has a finite real polar angle. -/
theorem exists_finite_polar (z : ℂ⟦Γ⟧) (hz : z ≠ 0) :
    ∃ θ : nonnegativeSubring Γ ℝ,
      z = complexRealEmbedding (ofLex (complexModulus z)) * finiteExp (finiteImaginary θ) := by
  let r := complexRealEmbedding (ofLex (complexModulus z))
  have hm : complexModulus z ≠ 0 := (complexModulus_eq_zero_iff z).not.mpr hz
  have hr : r ≠ 0 := by
    intro h
    have h' : ofLex (complexModulus z) = 0 :=
      complexRealEmbedding_injective (h.trans (map_zero _).symm)
    exact hm (congrArg toLex h')
  have hu : complexModulus (z / r) = 1 := by
    rw [complexModulus_div]
    change complexModulus z / complexModulus (complexRealEmbedding (ofLex (complexModulus z))) = 1
    rw [complexModulus_complexRealEmbedding, toLex_ofLex,
      abs_of_nonneg (complexModulus_nonneg z), div_self hm]
  obtain ⟨θ, hθ⟩ := exists_finiteImaginary_exp_eq_of_modulus_eq_one (z / r) hu
  refine ⟨θ, ?_⟩
  rw [hθ]
  exact (mul_div_cancel₀ z hr).symm

/-- Polar angles are unique modulo ordinary integer multiples of `2π`. -/
theorem finite_polar_angles_eq_iff (z : ℂ⟦Γ⟧) (hz : z ≠ 0)
    (θ φ : nonnegativeSubring Γ ℝ) :
    complexRealEmbedding (ofLex (complexModulus z)) * finiteExp (finiteImaginary θ) =
        complexRealEmbedding (ofLex (complexModulus z)) * finiteExp (finiteImaginary φ) ↔
      ∃ n : ℤ, (θ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧) = single 0 ((n : ℝ) * (2 * Real.pi)) := by
  have hr : complexRealEmbedding (ofLex (complexModulus z)) ≠ 0 := by
    intro h
    have h' : ofLex (complexModulus z) = 0 :=
      complexRealEmbedding_injective (h.trans (map_zero _).symm)
    exact hz ((complexModulus_eq_zero_iff z).mp (congrArg toLex h'))
  rw [mul_right_inj' hr, finiteExp_finiteImaginary_eq_iff]

end
end Surreal.HahnSeries
