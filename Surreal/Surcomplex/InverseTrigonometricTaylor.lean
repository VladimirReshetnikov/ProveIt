import Surreal.Surcomplex.InverseTrigonometricDerivative
import Surreal.Surcomplex.PowerSeriesTruncation
import Surreal.Algebra.InverseTrigonometricTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Analytic Taylor lifts of the actual inverse trigonometric functions

The geometric inverses agree with ordinary analytic Taylor lifting wherever
the ordinary standard part is in the analytic domain. This bridge supplies
strong series and exact finite remainders for `trigonometry:eq:smallseries`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Filter Topology

noncomputable section

/-- A finite actual surreal lies in an ordinary open interval whenever its residue does. -/
theorem mem_real_Ioo_of_standardPart_mem {x : SignSequence.{u}}
    (hx : SignSequence.IsFinite x) {a b : ℝ}
    (h : SignSequence.standardPart x ∈ Set.Ioo a b) :
    x ∈ Set.Ioo (SignSequence.ofReal a) (SignSequence.ofReal b) := by
  constructor
  · apply lt_of_not_ge
    intro he
    have hs := SignSequence.standardPartHom.monotone'
      (show ArchimedeanClass.FiniteElement.mk x hx ≤ SignSequence.finiteOfReal a from he)
    change SignSequence.standardPart x ≤ SignSequence.standardPart (SignSequence.ofReal a) at hs
    have hs' : SignSequence.standardPart x ≤ a := by
      simpa only [SignSequence.standardPart_ofReal] using hs
    exact h.1.not_ge hs'
  · apply lt_of_not_ge
    intro he
    have hs := SignSequence.standardPartHom.monotone'
      (show SignSequence.finiteOfReal b ≤ ArchimedeanClass.FiniteElement.mk x hx from he)
    change SignSequence.standardPart (SignSequence.ofReal b) ≤ SignSequence.standardPart x at hs
    have hs' : b ≤ SignSequence.standardPart x := by
      simpa only [SignSequence.standardPart_ofReal] using hs
    exact h.2.not_ge hs'

private theorem lift_congr_germ (f g : ℝ → ℝ) (x : SignSequence.{u})
    (hx : SignSequence.IsFinite x) (hf : AnalyticAt ℝ f (SignSequence.standardPart x))
    (hg : AnalyticAt ℝ g (SignSequence.standardPart x))
    (he : f =ᶠ[𝓝 (SignSequence.standardPart x)] g) :
    SignSequence.analyticLiftFunction f x = SignSequence.analyticLiftFunction g x := by
  rw [SignSequence.analyticLiftFunction_of_domain f x hx hf,
    SignSequence.analyticLiftFunction_of_domain g x hx hg]
  exact SignSequence.analyticTaylorEvaluation_congr hf hg he _ _

/-- At every finite input the geometrically constructed inverse tangent is its analytic lift. -/
theorem arctanFunction_eq_analyticLift (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    arctanFunction x = SignSequence.analyticLiftFunction Real.arctan x := by
  have hf : AnalyticAt ℝ Real.arctan (SignSequence.standardPart x) :=
    Real.contDiff_arctan.contDiffAt.analyticAt
  let y := SignSequence.analyticLiftFunction Real.arctan x
  have hy : SignSequence.IsFinite y := by
    dsimp only [y]
    rw [SignSequence.analyticLiftFunction_of_domain _ x hx hf]
    exact SignSequence.isFinite_analyticLift _ _ _ _
  have hstd : SignSequence.standardPart y = Real.arctan (SignSequence.standardPart x) := by
    dsimp only [y]
    rw [SignSequence.analyticLiftFunction_of_domain _ x hx hf,
      SignSequence.standardPart_analyticLift]
  have hi : y ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) :=
    mem_real_Ioo_of_standardPart_mem hy (hstd ▸ Real.arctan_mem_Ioo _)
  have hprod : Real.sin ∘ Real.arctan = (id : ℝ → ℝ) * (Real.cos ∘ Real.arctan) := by
    funext r
    change Real.sin (Real.arctan r) = r * Real.cos (Real.arctan r)
    exact (div_eq_iff (Real.cos_arctan_pos r).ne').mp
      (by simpa only [Real.tan_eq_sin_div_cos] using Real.tan_arctan r)
  have hs : sinFunction y = x * cosFunction y := by
    change SignSequence.analyticLiftFunction Real.sin
      (SignSequence.analyticLiftFunction Real.arctan x) =
        x * SignSequence.analyticLiftFunction Real.cos (SignSequence.analyticLiftFunction Real.arctan x)
    rw [← SignSequence.analyticLiftFunction_comp Real.sin Real.arctan x hx Real.analyticAt_sin hf,
      hprod, SignSequence.analyticLiftFunction_mul _ _ x hx analyticAt_id
        (Real.analyticAt_cos.comp hf), SignSequence.analyticLiftFunction_id x hx,
      SignSequence.analyticLiftFunction_comp Real.cos Real.arctan x hx Real.analyticAt_cos hf]
  let θ := ArchimedeanClass.FiniteElement.mk y hy
  have ht : finiteTan θ = x := by
    apply (div_eq_iff (finiteCos_pos_of_mem_Ioo θ hi).ne').mpr
    change sinFunction θ.val = x * cosFunction θ.val at hs
    rwa [sinFunction_eq_finiteSin, cosFunction_eq_finiteCos] at hs
  have he := arctan_finiteTan θ hi
  rw [ht] at he
  exact congrArg (fun φ : SignSequence.FiniteElement.{u} => φ.val) he

/-- Inverse sine agrees with analytic lifting on every monad over an ordinary interior input. -/
theorem arcsinFunction_eq_analyticLift (x : SignSequence.{u}) (hx : SignSequence.IsFinite x)
    (hc : SignSequence.standardPart x ∈ Set.Ioo (-1) 1) :
    arcsinFunction x = SignSequence.analyticLiftFunction Real.arcsin x := by
  have hf : AnalyticAt ℝ Real.arcsin (SignSequence.standardPart x) :=
    (Real.contDiffAt_arcsin hc.1.ne' hc.2.ne).analyticAt
  let y := SignSequence.analyticLiftFunction Real.arcsin x
  have hy : SignSequence.IsFinite y := by
    dsimp only [y]
    rw [SignSequence.analyticLiftFunction_of_domain _ x hx hf]
    exact SignSequence.isFinite_analyticLift _ _ _ _
  have hstd : SignSequence.standardPart y = Real.arcsin (SignSequence.standardPart x) := by
    dsimp only [y]
    rw [SignSequence.analyticLiftFunction_of_domain _ x hx hf,
      SignSequence.standardPart_analyticLift]
  have hi : y ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) :=
    mem_real_Ioo_of_standardPart_mem hy
      (hstd ▸ ⟨Real.neg_pi_div_two_lt_arcsin.mpr hc.1, Real.arcsin_lt_pi_div_two.mpr hc.2⟩)
  have hid : Real.sin ∘ Real.arcsin =ᶠ[𝓝 (SignSequence.standardPart x)] id := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with r hr
    exact Real.sin_arcsin hr.1.le hr.2.le
  have hs : sinFunction y = x := by
    change SignSequence.analyticLiftFunction Real.sin
      (SignSequence.analyticLiftFunction Real.arcsin x) = x
    rw [← SignSequence.analyticLiftFunction_comp Real.sin Real.arcsin x hx Real.analyticAt_sin hf,
      lift_congr_germ _ id x hx (Real.analyticAt_sin.comp hf) analyticAt_id hid,
      SignSequence.analyticLiftFunction_id x hx]
  let θ := ArchimedeanClass.FiniteElement.mk y hy
  have hsin : finiteSin θ = x := (sinFunction_eq_finiteSin θ).symm.trans hs
  have he := arcsin_finiteSin θ ⟨hi.1.le, hi.2.le⟩
  have hxc : x ∈ Set.Icc (-1) 1 := hsin ▸ finiteSin_mem_Icc θ
  have he' : arcsin ⟨x, hxc⟩ = θ := by simpa only [hsin] using he
  rw [show arcsinFunction x = (arcsin ⟨x, hxc⟩).val from arcsinFunction_eq ⟨x, hxc⟩, he']
  rfl

/-- The infinitesimal inverse tangent is exactly evaluation of its ordinary Taylor series at zero. -/
theorem arctanFunction_eq_powerSeries (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    arctanFunction x = SignSequence.powerSeriesEvaluation x hx (Analytic.taylorSeries Real.arctan 0) := by
  have hf := SignSequence.finite_of_infinitesimal hx
  have hs := (SignSequence.standardPart_eq_zero_iff hf).mpr hx
  rw [arctanFunction_eq_analyticLift x hf,
    SignSequence.analyticLiftFunction_of_domain _ x hf Real.contDiff_arctan.contDiffAt.analyticAt]
  simp only [SignSequence.analyticLift, SignSequence.analyticTaylorEvaluation, hs, map_zero, sub_zero]

/-- The infinitesimal inverse sine is exactly evaluation of its ordinary Taylor series at zero. -/
theorem arcsinFunction_eq_powerSeries (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    arcsinFunction x = SignSequence.powerSeriesEvaluation x hx (Analytic.taylorSeries Real.arcsin 0) := by
  have hf := SignSequence.finite_of_infinitesimal hx
  have hs := (SignSequence.standardPart_eq_zero_iff hf).mpr hx
  have hc : SignSequence.standardPart x ∈ Set.Ioo (-1) 1 := by rw [hs]; norm_num
  rw [arcsinFunction_eq_analyticLift x hf hc,
    SignSequence.analyticLiftFunction_of_domain _ x hf
      (Real.contDiffAt_arcsin hc.1.ne' hc.2.ne).analyticAt]
  simp only [SignSequence.analyticLift, SignSequence.analyticTaylorEvaluation, hs, map_zero, sub_zero]


/-- The alternating odd-power inverse-tangent family is strongly summable at any infinitesimal. -/
theorem stronglySummable_arctanTaylor (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.StronglySummable (fun n : ℕ =>
      SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1)) * x ^ (2 * n + 1)) := by
  have hs := SignSequence.stronglySummable_coeff_mul_powers x hx
    (fun n => (Analytic.taylorSeries Real.arctan 0).coeff n)
  simpa only [Analytic.coeff_taylorSeries_arctan_odd] using
    hs.comp_injective (fun n : ℕ => 2 * n + 1) (by intro a b h; dsimp at h; omega)

/-- The full inverse-tangent series is an actual strong sum, not an ordinary sequential limit. -/
theorem arctanFunction_eq_strongSum (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    arctanFunction x = SignSequence.strongSum (fun n : ℕ =>
      SignSequence.ofReal ((-1 : ℝ) ^ n / (2 * n + 1)) * x ^ (2 * n + 1))
      (stronglySummable_arctanTaylor x hx) := by
  have hs := SignSequence.stronglySummable_coeff_mul_powers x hx
    (fun n => (Analytic.taylorSeries Real.arctan 0).coeff n)
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k + 1) →
      SignSequence.ofReal ((Analytic.taylorSeries Real.arctan 0).coeff n) * x ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [Analytic.coeff_taylorSeries_arctan_even, map_zero, zero_mul]
    · exact (hn ⟨k, rfl⟩).elim
  have he := SignSequence.strongSum_comp_injective hs (fun n : ℕ => 2 * n + 1)
    (by intro a b h; dsimp at h; omega) hz
  rw [arctanFunction_eq_powerSeries x hx, SignSequence.powerSeriesEvaluation_eq_strongSum]
  simpa only [Analytic.coeff_taylorSeries_arctan_odd] using he.symm

/-- The inverse tangent differs from its linear term by a finite cubic remainder. -/
theorem arctanFunction_cubic_remainder (t : SignSequence.{u})
    (ht : SignSequence.IsInfinitesimal t) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ arctanFunction t = t + t ^ 3 * R := by
  obtain ⟨R, hR, _, he⟩ := SignSequence.exists_finite_powerSeries_remainder t ht
    (Analytic.taylorSeries Real.arctan 0) 3
  rw [← arctanFunction_eq_powerSeries t ht] at he
  simp_rw [Analytic.coeff_taylorSeries_arctan_zero] at he
  norm_num [Finset.sum_range_succ, map_div₀, map_neg, map_ofNat] at he
  exact ⟨R, hR, by linear_combination he⟩

/-- The inverse-tangent expansion through degree five has an exact finite seventh-order tail. -/
theorem arctanFunction_expansion (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = -1 / 7 ∧
      arctanFunction x = x - x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 * R := by
  obtain ⟨R, hR, hr, he⟩ := SignSequence.exists_finite_powerSeries_remainder x hx
    (Analytic.taylorSeries Real.arctan 0) 7
  rw [← arctanFunction_eq_powerSeries x hx] at he
  simp_rw [Analytic.coeff_taylorSeries_arctan_zero] at hr he
  norm_num [Finset.sum_range_succ, map_div₀, map_neg, map_ofNat] at hr he
  refine ⟨R, hR, by simpa only [neg_div] using hr, ?_⟩
  linear_combination he

/-- Positive infinite slopes have the exact source expansion with a finite normalized remainder. -/
theorem arctanFunction_expansion_of_positive_infinite (t : SignSequence.{u})
    (ht : 0 < t) (hinf : ¬ SignSequence.IsFinite t) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 / 7 ∧
      arctanFunction t = SignSequence.ofReal (Real.pi / 2) - t⁻¹ +
        (t⁻¹) ^ 3 / 3 - (t⁻¹) ^ 5 / 5 + (t⁻¹) ^ 7 * R := by
  have hi := (SignSequence.infinitesimal_inv_iff_not_finite ht.ne').mpr hinf
  obtain ⟨R, hR, hr, he⟩ := arctanFunction_expansion t⁻¹ hi
  have hc := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) (arctan_inv_of_pos t ht)
  change arctanFunction t⁻¹ = SignSequence.ofReal (Real.pi / 2) - arctanFunction t at hc
  refine ⟨-R, SignSequence.finite_neg hR, ?_, ?_⟩
  · rw [SignSequence.standardPart_neg, hr]
    ring
  · linear_combination hc - he


/-- Standard part of inverse tangent agrees with the ordinary inverse at every finite input. -/
theorem standardPart_arctanFunction (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    SignSequence.standardPart (arctanFunction x) = Real.arctan (SignSequence.standardPart x) := by
  rw [arctanFunction_eq_analyticLift x hx,
    SignSequence.analyticLiftFunction_of_domain _ x hx Real.contDiff_arctan.contDiffAt.analyticAt,
    SignSequence.standardPart_analyticLift]

/-- The actual inverse tangent agrees with ordinary constants. -/
theorem arctanFunction_ofReal (r : ℝ) :
    arctanFunction (SignSequence.ofReal r : SignSequence.{u}) = SignSequence.ofReal (Real.arctan r) := by
  rw [arctanFunction_eq_analyticLift _ (SignSequence.finite_ofReal r),
    SignSequence.analyticLiftFunction_ofReal _ r Real.contDiff_arctan.contDiffAt.analyticAt]

/-- An infinitesimal slope has an infinitesimal inverse-tangent angle. -/
theorem infinitesimal_arctanFunction (x : SignSequence.{u}) (hx : SignSequence.IsInfinitesimal x) :
    SignSequence.IsInfinitesimal (arctanFunction x) := by
  apply (SignSequence.standardPart_eq_zero_iff (arctan x).property).mp
  change SignSequence.standardPart (arctanFunction x) = 0
  rw [standardPart_arctanFunction x (SignSequence.finite_of_infinitesimal hx),
    (SignSequence.standardPart_eq_zero_iff (SignSequence.finite_of_infinitesimal hx)).mpr hx,
    Real.arctan_zero]

/-- A positive infinite slope gives a finite angle strictly and infinitesimally below a right angle. -/
theorem arctanFunction_positive_infinite_gap (t : SignSequence.{u}) (ht : 0 < t)
    (hinf : ¬ SignSequence.IsFinite t) :
    0 < SignSequence.ofReal (Real.pi / 2) - arctanFunction t ∧
      SignSequence.IsInfinitesimal (SignSequence.ofReal (Real.pi / 2) - arctanFunction t) := by
  have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) (arctan_inv_of_pos t ht)
  change arctanFunction t⁻¹ = SignSequence.ofReal (Real.pi / 2) - arctanFunction t at he
  refine ⟨sub_pos.mpr (arctan_mem t).2, ?_⟩
  rw [← he]
  exact infinitesimal_arctanFunction _ ((SignSequence.infinitesimal_inv_iff_not_finite ht.ne').mpr hinf)

/-- Oddness transfers the infinite-slope conclusions to negative inputs. -/
theorem arctanFunction_neg (t : SignSequence.{u}) : arctanFunction (-t) = -arctanFunction t :=
  congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) (arctan_neg t)

/-- The manuscript's omega slope has the same explicit finite-angle expansion. -/
theorem arctanFunction_omega_expansion :
    let t := (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u})
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 1 / 7 ∧
      arctanFunction t = SignSequence.ofReal (Real.pi / 2) - t⁻¹ +
        (t⁻¹) ^ 3 / 3 - (t⁻¹) ^ 5 / 5 + (t⁻¹) ^ 7 * R := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofOrdinal Ordinal.omega0 :=
    inv_pos.mp SignSequence.inv_omega0_pos
  exact arctanFunction_expansion_of_positive_infinite _ hp
    ((SignSequence.infinitesimal_inv_iff_not_finite hp.ne').mp SignSequence.infinitesimal_inv_omega0)

end
end Surreal.Surcomplex
