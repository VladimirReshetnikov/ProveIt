import Surreal.Surcomplex.Polar
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Principal finite polar angles

Every finite real surreal angle has a unique ordinary `2πℤ` translate in
`(-π, π]`. Reduce only its real standard part by the Archimedean interval
lemma, then correct a possible infinitesimal excursion above `π` by one
more period. No Archimedean assumption is imposed on the surreal field.
This finishes the principal-angle and negative-real clauses following
`e:prop-polar` on the actual surcomplex carrier.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem finite_lt_of_standardPart_lt {θ φ : SignSequence.FiniteElement.{u}}
    (h : SignSequence.standardPartHom θ < SignSequence.standardPartHom φ) : θ.val < φ.val := by
  apply lt_of_not_ge
  intro hle
  exact h.not_ge (SignSequence.standardPartHom.monotone' hle)

/-- The principal angle lies in the actual surreal interval `(-π, π]`. -/
def IsPrincipalAngle (θ : SignSequence.FiniteElement.{u}) : Prop :=
  -SignSequence.ofReal Real.pi < θ.val ∧ θ.val ≤ SignSequence.ofReal Real.pi

/-- Two ordinary-period translates in the principal interval are equal. -/
theorem principalAngle_eq_of_period {θ φ : SignSequence.FiniteElement.{u}}
    (hθ : IsPrincipalAngle θ) (hφ : IsPrincipalAngle φ)
    (hp : ∃ n : ℤ, θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi))) :
    θ = φ := by
  obtain ⟨n, hn⟩ := hp
  have hP : (SignSequence.ofReal (2 * Real.pi) : SignSequence.{u}) =
      SignSequence.ofReal Real.pi + SignSequence.ofReal Real.pi := by
    rw [show 2 * Real.pi = Real.pi + Real.pi by ring, map_add]
  have hlo : SignSequence.ofReal (-(2 * Real.pi)) < θ.val - φ.val := by
    rw [map_neg, hP]
    have := hθ.1
    have := hφ.2
    linarith
  have hhi : θ.val - φ.val < SignSequence.ofReal (2 * Real.pi) := by
    rw [hP]
    have := hθ.2
    have := hφ.1
    linarith
  rw [hn] at hlo hhi
  have hlo' := SignSequence.ofReal_strictMono.lt_iff_lt.mp hlo
  have hhi' := SignSequence.ofReal_strictMono.lt_iff_lt.mp hhi
  have hnlo : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hnhi : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  apply ArchimedeanClass.FiniteElement.ext
  apply sub_eq_zero.mp
  simpa only [hn0, Int.cast_zero, zero_mul, map_zero] using hn

/-- Every finite angle has exactly one principal ordinary-period translate. -/
theorem existsUnique_principalAngle_period (θ : SignSequence.FiniteElement.{u}) :
    ∃! φ : SignSequence.FiniteElement.{u}, IsPrincipalAngle φ ∧
      ∃ n : ℤ, θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) := by
  let c := SignSequence.standardPartHom θ
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ioc Real.two_pi_pos c (-Real.pi)
  have hcn : -Real.pi < c - (n : ℝ) * (2 * Real.pi) ∧
      c - (n : ℝ) * (2 * Real.pi) ≤ Real.pi := by
    simpa only [Set.mem_Ioc, zsmul_eq_mul,
      show -Real.pi + 2 * Real.pi = Real.pi by ring] using hn
  let ψ : SignSequence.FiniteElement.{u} :=
    θ - SignSequence.finiteOfReal ((n : ℝ) * (2 * Real.pi))
  have hcψ : SignSequence.standardPartHom ψ = c - (n : ℝ) * (2 * Real.pi) := by
    rw [map_sub, SignSequence.standardPartHom_finiteOfReal]
  have hlo : -SignSequence.ofReal Real.pi < ψ.val := by
    apply finite_lt_of_standardPart_lt (θ := -SignSequence.finiteOfReal Real.pi)
    simpa only [map_neg, SignSequence.standardPartHom_finiteOfReal, hcψ] using hcn.1
  have hupper : ψ.val < SignSequence.ofReal (3 * Real.pi) := by
    apply finite_lt_of_standardPart_lt (φ := SignSequence.finiteOfReal (3 * Real.pi))
    rw [hcψ, SignSequence.standardPartHom_finiteOfReal]
    linarith [hcn.2, Real.pi_pos]
  have hex : ∃ φ : SignSequence.FiniteElement.{u}, IsPrincipalAngle φ ∧
      ∃ m : ℤ, θ.val - φ.val = SignSequence.ofReal ((m : ℝ) * (2 * Real.pi)) := by
    by_cases hπ : ψ.val ≤ SignSequence.ofReal Real.pi
    · refine ⟨ψ, ⟨hlo, hπ⟩, n, ?_⟩
      exact sub_sub_cancel _ _
    · let φ : SignSequence.FiniteElement.{u} := ψ - SignSequence.finiteOfReal (2 * Real.pi)
      have hφ : φ.val = ψ.val -
          (SignSequence.ofReal Real.pi + SignSequence.ofReal Real.pi) := by
        change ψ.val - SignSequence.ofReal (2 * Real.pi) = _
        rw [show 2 * Real.pi = Real.pi + Real.pi by ring, map_add]
      have h3 : (SignSequence.ofReal (3 * Real.pi) : SignSequence.{u}) =
          SignSequence.ofReal Real.pi + SignSequence.ofReal Real.pi +
            SignSequence.ofReal Real.pi := by
        rw [show 3 * Real.pi = Real.pi + Real.pi + Real.pi by ring, map_add, map_add]
      refine ⟨φ, ?_, n + 1, ?_⟩
      · constructor
        · rw [hφ]
          have := lt_of_not_ge hπ
          linarith
        · rw [hφ]
          rw [h3] at hupper
          linarith
      · change θ.val - ((θ.val - SignSequence.ofReal ((n : ℝ) * (2 * Real.pi))) -
          SignSequence.ofReal (2 * Real.pi)) = _
        rw [Int.cast_add, Int.cast_one, add_mul, one_mul, map_add]
        abel
  obtain ⟨φ, hφ, hperiod⟩ := hex
  refine ⟨φ, ⟨hφ, hperiod⟩, ?_⟩
  intro ψ hψ
  apply principalAngle_eq_of_period hψ.1 hφ
  obtain ⟨n, hn⟩ := hperiod
  obtain ⟨m, hm⟩ := hψ.2
  refine ⟨n - m, ?_⟩
  calc
    ψ.val - φ.val = (θ.val - φ.val) - (θ.val - ψ.val) := by abel
    _ = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) -
        SignSequence.ofReal ((m : ℝ) * (2 * Real.pi)) := by rw [hn, hm]
    _ = SignSequence.ofReal (((n - m : ℤ) : ℝ) * (2 * Real.pi)) := by
      rw [← map_sub, Int.cast_sub, sub_mul]

theorem isPrincipalAngle_pi :
    IsPrincipalAngle (SignSequence.finiteOfReal Real.pi : SignSequence.FiniteElement.{u}) := by
  constructor
  · change -SignSequence.ofReal Real.pi < (SignSequence.ofReal Real.pi : SignSequence.{u})
    rw [← map_neg]
    exact SignSequence.ofReal_strictMono (by linarith [Real.pi_pos])
  · exact le_rfl

/-- The ordinary angle `π` has phase `-1`. -/
theorem finitePhase_pi :
    finitePhase (SignSequence.finiteOfReal Real.pi : SignSequence.FiniteElement.{u}) = -1 := by
  have h : finiteImaginary (SignSequence.finiteOfReal Real.pi) =
      (⟨ofComplex ((Real.pi : ℂ) * Complex.I), finite_ofComplex _⟩ : finiteSubring.{u}) := by
    apply Subtype.ext
    change ofReal (SignSequence.ofReal Real.pi) * I = ofComplex ((Real.pi : ℂ) * Complex.I)
    rw [map_mul, ofComplex_ofReal, ofComplex_I]
  rw [finitePhase, h, finiteExp_constant, Complex.exp_pi_mul_I, map_neg, map_one]

/-- Every nonzero surcomplex has a unique principal polar angle. -/
theorem existsUnique_principal_polar (z : Surcomplex.{u}) (hz : z ≠ 0) :
    ∃! θ : SignSequence.FiniteElement.{u}, IsPrincipalAngle θ ∧
      z = ofReal (modulus z) * finitePhase θ := by
  obtain ⟨φ, hφ⟩ := exists_polar z hz
  obtain ⟨θ, ⟨hθ, n, hn⟩, _⟩ := existsUnique_principalAngle_period φ
  have he : finitePhase φ = finitePhase θ := (finitePhase_eq_iff φ θ).mpr ⟨n, hn⟩
  have hzθ : z = ofReal (modulus z) * finitePhase θ := by rw [← he]; exact hφ
  refine ⟨θ, ⟨hθ, hzθ⟩, ?_⟩
  rintro ψ ⟨hψ, hzψ⟩
  apply principalAngle_eq_of_period hψ hθ
  exact (polar_angle_eq_iff z hz ψ θ).mp (hzψ.symm.trans hzθ)

/-- Every negative real input, including infinite and infinitesimal ones, has angle `π`. -/
theorem negative_real_polar_pi (x : SignSequence.{u}) (hx : x < 0) :
    ofReal x = ofReal (modulus (ofReal x)) * finitePhase (SignSequence.finiteOfReal Real.pi) := by
  rw [modulus_ofReal, abs_of_neg hx, finitePhase_pi, map_neg]
  ring

/-- The unique principal angle of any negative real surcomplex is exactly `π`. -/
theorem principal_polar_angle_of_negative_real (x : SignSequence.{u}) (hx : x < 0)
    (θ : SignSequence.FiniteElement.{u}) (hθ : IsPrincipalAngle θ)
    (hp : ofReal x = ofReal (modulus (ofReal x)) * finitePhase θ) :
    θ = SignSequence.finiteOfReal Real.pi := by
  have hz : ofReal x ≠ 0 := (map_ne_zero ofReal).mpr hx.ne
  apply principalAngle_eq_of_period hθ isPrincipalAngle_pi
  exact (polar_angle_eq_iff (ofReal x) hz θ (SignSequence.finiteOfReal Real.pi)).mp
    (hp.symm.trans (negative_real_polar_pi x hx))

end

end Surreal.Surcomplex
