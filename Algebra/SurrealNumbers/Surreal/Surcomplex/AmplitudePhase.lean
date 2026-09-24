import Surreal.Surcomplex.AngleGroup
import Surreal.Surcomplex.InverseTrigonometry
import Surreal.Surcomplex.TrigonometricFineDerivative

/-!
# Amplitude reduction and finite angle classes

The angular clauses of `trigonometry:thm:amplitude` and
`trigonometry:eq:amplitude` hold for arbitrary actual surreal coefficients.
Only the angles are required to be finite. Angle classes use the existing
quotient by ordinary integral full turns.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

abbrev FiniteAngleClass :=
  Multiplicative SignSequence.FiniteElement.{u} ⧸ anglePeriods

/-- The class of a finite angle modulo ordinary full turns. -/
def finiteAngleClass (θ : SignSequence.FiniteElement.{u}) : FiniteAngleClass.{u} :=
  QuotientGroup.mk (Multiplicative.ofAdd θ)

theorem finiteAngleClass_eq_iff (θ φ : SignSequence.FiniteElement.{u}) :
    finiteAngleClass θ = finiteAngleClass φ ↔ finitePhase θ = finitePhase φ := by
  rw [← angleQuotientEquiv.injective.eq_iff, finiteAngleClass, finiteAngleClass,
    angleQuotientEquiv_mk, angleQuotientEquiv_mk, Subtype.ext_iff]
  rfl

/-- Equality of cosines has exactly the two possible signs of sine. -/
theorem finiteCos_eq_iff_phase_eq_or_eq_neg (θ φ : SignSequence.FiniteElement.{u}) :
    finiteCos θ = finiteCos φ ↔
      finitePhase θ = finitePhase φ ∨ finitePhase θ = finitePhase (-φ) := by
  constructor
  · intro hc
    have hs : finiteSin θ ^ 2 = finiteSin φ ^ 2 := by
      have ht := finiteCos_sq_add_finiteSin_sq θ
      rw [hc] at ht
      linarith [finiteCos_sq_add_finiteSin_sq φ]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hs | hs
    · exact Or.inl (QuadraticAlgebra.ext hc hs)
    · apply Or.inr
      apply QuadraticAlgebra.ext
      · change finiteCos θ = finiteCos (-φ)
        simpa only [finiteCos_neg] using hc
      · change finiteSin θ = finiteSin (-φ)
        simpa only [finiteSin_neg] using hs
  · rintro (h | h)
    · exact congrArg QuadraticAlgebra.re h
    · have he : finiteCos θ = finiteCos (-φ) := congrArg QuadraticAlgebra.re h
      simpa only [finiteCos_neg] using he

/-- A nonzero normal vector admits the finite phase required by amplitude reduction. -/
theorem exists_amplitude_phase (A B : SignSequence.{u}) (h : 0 < A ^ 2 + B ^ 2) :
    ∃ φ : SignSequence.FiniteElement.{u},
      finiteCos φ = A / SignSequence.sqrt (A ^ 2 + B ^ 2) ∧
      finiteSin φ = B / SignSequence.sqrt (A ^ 2 + B ^ 2) := by
  let ρ := SignSequence.sqrt (A ^ 2 + B ^ 2)
  have hr : ρ ≠ 0 := (SignSequence.sqrt_pos h).ne'
  have hrs : ρ ^ 2 = A ^ 2 + B ^ 2 := SignSequence.sqrt_sq h.le
  let z : Surcomplex.{u} := ⟨A / ρ, B / ρ⟩
  have hz : modulus z = 1 := by
    apply modulus_eq_of_nonneg_sq zero_le_one
    change 1 ^ 2 = (A / ρ) ^ 2 + (B / ρ) ^ 2
    rw [div_pow, div_pow, ← add_div, ← hrs, div_self (pow_ne_zero 2 hr), one_pow]
  obtain ⟨φ, he⟩ := exists_finitePhase_eq_of_modulus_eq_one z hz
  exact ⟨φ, congrArg QuadraticAlgebra.re he, congrArg QuadraticAlgebra.im he⟩

/-- The amplitude identity does not require finite coefficients or finite amplitude. -/
theorem amplitude_phase (A B ρ : SignSequence.{u}) (hρ : ρ ≠ 0)
    (φ θ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ) :
    A * finiteCos θ + B * finiteSin θ = ρ * finiteCos (θ - φ) := by
  rw [finiteCos_sub, hc, hs]
  field_simp

/-- Translation of the two cosine branches gives exactly two candidate angle classes. -/
theorem shifted_cos_eq_iff (θ φ q : SignSequence.FiniteElement.{u}) :
    finiteCos (θ - φ) = finiteCos q ↔
      finiteAngleClass θ = finiteAngleClass (φ + q) ∨
      finiteAngleClass θ = finiteAngleClass (φ - q) := by
  rw [finiteCos_eq_iff_phase_eq_or_eq_neg, finiteAngleClass_eq_iff,
    finiteAngleClass_eq_iff, finitePhase_sub, finitePhase_add,
    finitePhase_sub, finitePhase_neg]
  have hn : finitePhase φ ≠ 0 := finiteExp_ne_zero _
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [div_eq_iff hn] at h; simpa only [mul_comm] using h)
    · exact Or.inr (by rw [div_eq_iff hn] at h; simpa only [div_eq_mul_inv, mul_comm] using h)
  · rintro (h | h)
    · exact Or.inl ((div_eq_iff hn).mpr (by simpa only [mul_comm] using h))
    · exact Or.inr ((div_eq_iff hn).mpr (by simpa only [div_eq_mul_inv, mul_comm] using h))

/-- The two translated classes coincide exactly at a cosine endpoint. -/
theorem shifted_classes_eq_iff (φ q : SignSequence.FiniteElement.{u}) :
    finiteAngleClass (φ + q) = finiteAngleClass (φ - q) ↔ |finiteCos q| = 1 := by
  rw [finiteAngleClass_eq_iff, sub_eq_add_neg, finitePhase_add, finitePhase_add,
    mul_right_inj' (show finitePhase φ ≠ 0 from finiteExp_ne_zero _)]
  constructor
  · intro h
    have hs : finiteSin q = 0 := by
      have he := congrArg QuadraticAlgebra.im h
      change finiteSin q = finiteSin (-q) at he
      rw [finiteSin_neg] at he
      linarith
    have he := finiteCos_sq_add_finiteSin_sq q
    rw [hs, zero_pow (by norm_num), add_zero] at he
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa only [sq_abs, one_pow] using he)
  · intro h
    have hs : finiteSin q = 0 := by
      have hc : finiteCos q ^ 2 = 1 := by nlinarith [sq_abs (finiteCos q)]
      have he := finiteCos_sq_add_finiteSin_sq q
      nlinarith [sq_nonneg (finiteSin q)]
    apply QuadraticAlgebra.ext
    · exact (finiteCos_neg q).symm
    · change finiteSin q = finiteSin (-q)
      rw [finiteSin_neg, hs, neg_zero]

/-- Normalization puts the intersection parameter in the actual closed cosine range. -/
theorem amplitude_ratio_mem {D ρ : SignSequence.{u}} (hρ : 0 < ρ) (hD : |D| ≤ ρ) :
    D / ρ ∈ Set.Icc (-1) 1 := by
  rcases abs_le.mp hD with ⟨hl, hu⟩
  constructor
  · exact (le_div_iff₀ hρ).mpr (by simpa only [neg_one_mul] using hl)
  · exact (div_le_iff₀ hρ).mpr (by simpa only [one_mul] using hu)

/-- The first harmonic as a function of finite-angle classes. -/
def angleClassHarmonic (A B : SignSequence.{u}) (θ : FiniteAngleClass.{u}) : SignSequence.{u} :=
  A * (angleQuotientEquiv θ).val.re + B * (angleQuotientEquiv θ).val.im

@[simp] theorem angleClassHarmonic_mk (A B : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    angleClassHarmonic A B (finiteAngleClass θ) = A * finiteCos θ + B * finiteSin θ := rfl

/-- All solutions are the displayed plus and minus inverse-cosine classes. -/
theorem amplitude_solution_iff (A B D ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ) (hD : |D| ≤ ρ)
    (θ : FiniteAngleClass.{u}) :
    angleClassHarmonic A B θ = D ↔
      θ = finiteAngleClass (φ + arccos ⟨D / ρ, amplitude_ratio_mem hρ hD⟩) ∨
      θ = finiteAngleClass (φ - arccos ⟨D / ρ, amplitude_ratio_mem hρ hD⟩) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective θ
  change A * finiteCos t.toAdd + B * finiteSin t.toAdd = D ↔ _
  rw [amplitude_phase A B ρ hρ.ne' φ t.toAdd hc hs]
  rw [mul_comm ρ, ← eq_div_iff hρ.ne']
  simpa only [finiteCos_arccos, finiteAngleClass, ofAdd_toAdd] using
    shifted_cos_eq_iff t.toAdd φ (arccos ⟨D / ρ, amplitude_ratio_mem hρ hD⟩)

/-- Above the amplitude the intersection has no finite-angle class. -/
theorem amplitude_no_solution (A B D ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ) (hD : ρ < |D|)
    (θ : FiniteAngleClass.{u}) : angleClassHarmonic A B θ ≠ D := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective θ
  change A * finiteCos t.toAdd + B * finiteSin t.toAdd ≠ D
  rw [amplitude_phase A B ρ hρ.ne' φ t.toAdd hc hs]
  intro he
  have hb := abs_le.mpr (finiteCos_mem_Icc (t.toAdd - φ))
  have hd : |D| ≤ ρ := by
    rw [← he, abs_mul, abs_of_pos hρ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hρ.le
  exact hD.not_ge hd

/-- At either endpoint the plus and minus representatives give one unique class. -/
theorem amplitude_unique_solution (A B D ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ) (hD : |D| = ρ) :
    ∃! θ : FiniteAngleClass.{u}, angleClassHarmonic A B θ = D := by
  let q := arccos ⟨D / ρ, amplitude_ratio_mem hρ hD.le⟩
  have he : finiteAngleClass (φ + q) = finiteAngleClass (φ - q) := by
    apply (shifted_classes_eq_iff φ q).mpr
    rw [finiteCos_arccos, abs_div, abs_of_pos hρ, hD, div_self hρ.ne']
  refine ⟨finiteAngleClass (φ + q), ?_, ?_⟩
  · exact (amplitude_solution_iff A B D ρ hρ φ hc hs hD.le _).mpr (Or.inl rfl)
  · intro θ hθ
    rcases (amplitude_solution_iff A B D ρ hρ φ hc hs hD.le θ).mp hθ with ht | ht
    · exact ht
    · exact ht.trans he.symm

/-- Strictly inside the amplitude there are exactly two distinct angle classes. -/
theorem amplitude_two_solutions (A B D ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ) (hD : |D| < ρ) :
    ∃ θ₁ θ₂ : FiniteAngleClass.{u}, θ₁ ≠ θ₂ ∧
      ∀ θ, angleClassHarmonic A B θ = D ↔ θ = θ₁ ∨ θ = θ₂ := by
  let q := arccos ⟨D / ρ, amplitude_ratio_mem hρ hD.le⟩
  refine ⟨finiteAngleClass (φ + q), finiteAngleClass (φ - q), ?_,
    amplitude_solution_iff A B D ρ hρ φ hc hs hD.le⟩
  intro he
  have he' := (shifted_classes_eq_iff φ q).mp he
  rw [finiteCos_arccos, abs_div, abs_of_pos hρ, div_eq_one_iff_eq hρ.ne'] at he'
  exact hD.ne he'

/-- The first angular derivative, in the native fine topology, allows infinite coefficients. -/
theorem fineHasDerivAt_firstHarmonic (A B : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (fun x => A * cosFunction x + B * sinFunction x)
      (B * finiteCos θ - A * finiteSin θ) θ.val := by
  have h := ((FineHasDerivAt.const A θ.val).mul
    (fineHasDerivAt_cosFunction θ.val θ.property)).add
    ((FineHasDerivAt.const B θ.val).mul (fineHasDerivAt_sinFunction θ.val θ.property))
  simpa only [zero_mul, zero_add, mul_neg, neg_add_eq_sub,
    cosFunction_eq_finiteCos, sinFunction_eq_finiteSin] using h

/-- The second angular derivative is the negative of the first harmonic itself. -/
theorem fineHasDerivAt_firstHarmonic_derivative (A B : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (fun x => B * cosFunction x - A * sinFunction x)
      (-(A * finiteCos θ + B * finiteSin θ)) θ.val := by
  have h := ((FineHasDerivAt.const B θ.val).mul
    (fineHasDerivAt_cosFunction θ.val θ.property)).sub
    ((FineHasDerivAt.const A θ.val).mul (fineHasDerivAt_sinFunction θ.val θ.property))
  convert h using 1
  rw [cosFunction_eq_finiteCos, sinFunction_eq_finiteSin]
  ring

end
end Surreal.Surcomplex
