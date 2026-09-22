import Surreal.HahnSeries.Polar
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Principal finite Hahn angles

Every finite real Hahn angle has a unique ordinary `2πℤ` translate in
`(-π, π]`. Only its ordinary real constant coefficient is reduced modulo
`2π`; a further period is removed when an infinitesimal correction crosses
the upper endpoint. No Archimedean structure on the Hahn field is assumed.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

omit [IsOrderedAddMonoid Γ] in
/-- Comparing distinct standard parts determines the Hahn order of finite real series. -/
theorem lex_lt_of_coeff_zero_lt {x y : ℝ⟦Γ⟧} (hx : 0 ≤ x.orderTop)
    (hy : 0 ≤ y.orderTop) (h : x.coeff 0 < y.coeff 0) : toLex x < toLex y := by
  apply (_root_.HahnSeries.lt_iff _ _).mpr
  refine ⟨0, ?_, h⟩
  intro g hg
  change x.coeff g = y.coeff g
  rw [coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hg).trans_le hx),
    coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hg).trans_le hy)]

omit [IsOrderedAddMonoid Γ] in
@[simp] theorem lex_single_zero_lt_iff (a b : ℝ) :
    toLex (single (0 : Γ) a) < toLex (single 0 b) ↔ a < b := by
  rw [← sub_pos, ← toLex_sub, ← single_sub, ← leadingCoeff_pos_iff]
  simp only [ofLex_toLex, leadingCoeff_of_single, sub_pos]

/-- The ordinary principal-angle interval in the actual lexicographic Hahn order. -/
def IsPrincipalAngle (θ : nonnegativeSubring Γ ℝ) : Prop :=
  -toLex (single (0 : Γ) Real.pi) < toLex (θ : ℝ⟦Γ⟧) ∧
    toLex (θ : ℝ⟦Γ⟧) ≤ toLex (single 0 Real.pi)

/-- Distinct ordinary period translates cannot both lie in the principal interval. -/
theorem principalAngle_eq_of_period {θ φ : nonnegativeSubring Γ ℝ}
    (hθ : IsPrincipalAngle θ) (hφ : IsPrincipalAngle φ)
    (hp : ∃ n : ℤ, (θ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧) =
      single 0 ((n : ℝ) * (2 * Real.pi))) : θ = φ := by
  obtain ⟨n, hn⟩ := hp
  have hP : toLex (single (0 : Γ) (2 * Real.pi)) =
      toLex (single 0 Real.pi) + toLex (single 0 Real.pi) := by
    rw [show 2 * Real.pi = Real.pi + Real.pi by ring, single_add]
    rfl
  have hlo : toLex (single (0 : Γ) (-(2 * Real.pi))) <
      toLex (θ : ℝ⟦Γ⟧) - toLex (φ : ℝ⟦Γ⟧) := by
    rw [single_neg, toLex_neg, hP]
    have := hθ.1
    have := hφ.2
    linarith
  have hhi : toLex (θ : ℝ⟦Γ⟧) - toLex (φ : ℝ⟦Γ⟧) <
      toLex (single (0 : Γ) (2 * Real.pi)) := by
    rw [hP]
    have := hθ.2
    have := hφ.1
    linarith
  rw [← toLex_sub, hn, lex_single_zero_lt_iff] at hlo hhi
  have hnlo : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hnhi : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  apply Subtype.ext
  apply sub_eq_zero.mp
  simpa only [hn0, Int.cast_zero, zero_mul, map_zero] using hn

/-- Every finite real Hahn angle has a unique principal ordinary-period translate. -/
theorem existsUnique_principalAngle_period (θ : nonnegativeSubring Γ ℝ) :
    ∃! φ : nonnegativeSubring Γ ℝ, IsPrincipalAngle φ ∧
      ∃ n : ℤ, (θ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧) = single 0 ((n : ℝ) * (2 * Real.pi)) := by
  let c := (θ : ℝ⟦Γ⟧).coeff 0
  obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ioc Real.two_pi_pos c (-Real.pi)
  have hcn : -Real.pi < c - (n : ℝ) * (2 * Real.pi) ∧
      c - (n : ℝ) * (2 * Real.pi) ≤ Real.pi := by
    simpa only [Set.mem_Ioc, zsmul_eq_mul,
      show -Real.pi + 2 * Real.pi = Real.pi by ring] using hn
  let ψ : nonnegativeSubring Γ ℝ := θ - constantNonnegative ((n : ℝ) * (2 * Real.pi))
  have hcψ : (ψ : ℝ⟦Γ⟧).coeff 0 = c - (n : ℝ) * (2 * Real.pi) := by
    change ((θ : ℝ⟦Γ⟧) - single 0 ((n : ℝ) * (2 * Real.pi))).coeff 0 = _
    rw [coeff_sub, coeff_single_same]
  have hlo : -toLex (single (0 : Γ) Real.pi) < toLex (ψ : ℝ⟦Γ⟧) := by
    rw [← toLex_neg, ← single_neg]
    apply lex_lt_of_coeff_zero_lt orderTop_single_le ψ.property
    simpa only [coeff_single_same, hcψ] using hcn.1
  have hupper : toLex (ψ : ℝ⟦Γ⟧) < toLex (single (0 : Γ) (3 * Real.pi)) := by
    apply lex_lt_of_coeff_zero_lt ψ.property orderTop_single_le
    rw [hcψ, coeff_single_same]
    linarith [hcn.2, Real.pi_pos]
  have hex : ∃ φ : nonnegativeSubring Γ ℝ, IsPrincipalAngle φ ∧
      ∃ m : ℤ, (θ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧) = single 0 ((m : ℝ) * (2 * Real.pi)) := by
    by_cases hπ : toLex (ψ : ℝ⟦Γ⟧) ≤ toLex (single 0 Real.pi)
    · refine ⟨ψ, ⟨hlo, hπ⟩, n, ?_⟩
      change (θ : ℝ⟦Γ⟧) - ((θ : ℝ⟦Γ⟧) - single 0 ((n : ℝ) * (2 * Real.pi))) = _
      exact sub_sub_cancel _ _
    · let φ : nonnegativeSubring Γ ℝ := ψ - constantNonnegative (2 * Real.pi)
      have hφ : toLex (φ : ℝ⟦Γ⟧) =
          toLex (ψ : ℝ⟦Γ⟧) - (toLex (single (0 : Γ) Real.pi) + toLex (single 0 Real.pi)) := by
        change toLex ((ψ : ℝ⟦Γ⟧) - single 0 (2 * Real.pi)) = _
        rw [toLex_sub, show 2 * Real.pi = Real.pi + Real.pi by ring, single_add]
        rfl
      have h3 : toLex (single (0 : Γ) (3 * Real.pi)) =
          toLex (single 0 Real.pi) + toLex (single 0 Real.pi) + toLex (single 0 Real.pi) := by
        rw [show 3 * Real.pi = Real.pi + Real.pi + Real.pi by ring, single_add, single_add]
        rfl
      refine ⟨φ, ?_, n + 1, ?_⟩
      · constructor
        · rw [hφ]
          have := lt_of_not_ge hπ
          linarith
        · rw [hφ]
          rw [h3] at hupper
          linarith
      · change (θ : ℝ⟦Γ⟧) -
          (((θ : ℝ⟦Γ⟧) - single 0 ((n : ℝ) * (2 * Real.pi))) - single 0 (2 * Real.pi)) = _
        rw [Int.cast_add, Int.cast_one, add_mul, one_mul, single_add]
        abel
  obtain ⟨φ, hφ, hperiod⟩ := hex
  refine ⟨φ, ⟨hφ, hperiod⟩, ?_⟩
  intro ψ hψ
  apply principalAngle_eq_of_period hψ.1 hφ
  obtain ⟨n, hn⟩ := hperiod
  obtain ⟨m, hm⟩ := hψ.2
  refine ⟨n - m, ?_⟩
  calc
    (ψ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧) =
        ((θ : ℝ⟦Γ⟧) - (φ : ℝ⟦Γ⟧)) - ((θ : ℝ⟦Γ⟧) - (ψ : ℝ⟦Γ⟧)) := by abel
    _ = single 0 ((n : ℝ) * (2 * Real.pi)) - single 0 ((m : ℝ) * (2 * Real.pi)) := by rw [hn, hm]
    _ = single 0 (((n - m : ℤ) : ℝ) * (2 * Real.pi)) := by rw [← single_sub, Int.cast_sub, sub_mul]

theorem isPrincipalAngle_pi :
    IsPrincipalAngle (constantNonnegative (Γ := Γ) Real.pi) := by
  constructor
  · change -toLex (single (0 : Γ) Real.pi) < toLex (single 0 Real.pi)
    rw [← toLex_neg, ← single_neg, lex_single_zero_lt_iff]
    linarith [Real.pi_pos]
  · exact le_rfl

theorem finiteExp_finiteImaginary_pi :
    finiteExp (finiteImaginary (constantNonnegative (Γ := Γ) Real.pi)) = -1 := by
  have h : finiteImaginary (constantNonnegative (Γ := Γ) Real.pi) =
      constantNonnegative ((Real.pi : ℂ) * Complex.I) :=
    Subtype.ext (imaginaryHahn_single_zero Real.pi)
  rw [h]
  change finiteExp (⟨single 0 ((Real.pi : ℂ) * Complex.I), orderTop_single_le⟩ :
    nonnegativeSubring Γ ℂ) = _
  rw [finiteExp_constant, Complex.exp_pi_mul_I]
  simp

variable [DivisibleBy Γ ℕ]

/-- Every nonzero complex Hahn series has exactly one polar angle in `(-π, π]`. -/
theorem existsUnique_principal_polar (z : ℂ⟦Γ⟧) (hz : z ≠ 0) :
    ∃! θ : nonnegativeSubring Γ ℝ, IsPrincipalAngle θ ∧
      z = complexRealEmbedding (ofLex (complexModulus z)) * finiteExp (finiteImaginary θ) := by
  obtain ⟨φ, hφ⟩ := exists_finite_polar z hz
  obtain ⟨θ, ⟨hθ, n, hn⟩, _⟩ := existsUnique_principalAngle_period φ
  have he : finiteExp (finiteImaginary φ) = finiteExp (finiteImaginary θ) :=
    (finiteExp_finiteImaginary_eq_iff φ θ).mpr ⟨n, hn⟩
  refine ⟨θ, ⟨hθ, hφ.trans (congrArg (fun w => complexRealEmbedding (ofLex (complexModulus z)) * w) he)⟩, ?_⟩
  rintro ψ ⟨hψ, hzψ⟩
  apply principalAngle_eq_of_period hψ hθ
  apply (finite_polar_angles_eq_iff z hz ψ θ).mp
  exact hzψ.symm.trans (hφ.trans (congrArg (fun w => complexRealEmbedding (ofLex (complexModulus z)) * w) he))

/-- A negative real Hahn input has polar angle `π`, including infinitely large
or infinitesimal negative real inputs. -/
theorem negative_real_polar_pi (x : ℝ⟦Γ⟧) (hx : toLex x < 0) :
    complexRealEmbedding x =
      complexRealEmbedding (ofLex (complexModulus (complexRealEmbedding x))) *
        finiteExp (finiteImaginary (constantNonnegative (Γ := Γ) Real.pi)) := by
  rw [complexModulus_complexRealEmbedding, abs_of_neg hx, finiteExp_finiteImaginary_pi]
  change complexRealEmbedding x = complexRealEmbedding (-x) * (-1)
  rw [map_neg]
  ring

/-- The unique principal polar angle of every negative real Hahn input is `π`. -/
theorem principal_polar_angle_of_negative_real (x : ℝ⟦Γ⟧) (hx : toLex x < 0)
    (θ : nonnegativeSubring Γ ℝ) (hθ : IsPrincipalAngle θ)
    (hp : complexRealEmbedding x =
      complexRealEmbedding (ofLex (complexModulus (complexRealEmbedding x))) *
        finiteExp (finiteImaginary θ)) :
    θ = constantNonnegative Real.pi := by
  have hx0 : x ≠ 0 := by intro h; simp only [h, toLex_zero, lt_self_iff_false] at hx
  have hz : complexRealEmbedding x ≠ 0 := by
    intro h
    exact hx0 (complexRealEmbedding_injective (h.trans (map_zero _).symm))
  apply principalAngle_eq_of_period hθ isPrincipalAngle_pi
  apply (finite_polar_angles_eq_iff (complexRealEmbedding x) hz θ
    (constantNonnegative Real.pi)).mp
  exact hp.symm.trans (negative_real_polar_pi x hx)

end
end Surreal.HahnSeries
