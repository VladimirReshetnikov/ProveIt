import Surreal.Surcomplex.ContactAngleDifference
import Surreal.Surcomplex.ArcsinSeries
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Signed perturbations of a nearly tangent intersection

The exact half-angle inverse-tangent identity proves `trigonometry:eq:contactstability`
and its sharp valuation consequence `trigonometry:eq:contactval`, the perturbation clauses
of `trigonometry:thm:tangency`. The perturbation may have either sign. Its size relative to
the positive infinitesimal defect controls a finite normalized error at the stated rate.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

private theorem contact_finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

private theorem contact_standardPart_two :
    SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
  simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)

private theorem contact_infinitesimal_lt_one {x : SignSequence.{u}}
    (hx : SignSequence.IsInfinitesimal x) : |x| < 1 := by
  simpa only [map_one] using
    (SignSequence.isInfinitesimal_iff_forall_real_abs_lt x).mp hx 1 zero_lt_one

/-- A signed relatively infinitesimal perturbation cannot cross the endpoint. -/
theorem contact_perturbed_defect_pos (τ e : SignSequence.{u}) (hp : 0 < τ)
    (hu : SignSequence.IsInfinitesimal (e / τ)) : 0 < τ + e := by
  have hlo := (abs_lt.mp (contact_infinitesimal_lt_one hu)).1
  have he : τ + e = τ * (1 + e / τ) := by field_simp [hp.ne']
  rw [he]
  exact mul_pos hp (by linarith only [hlo])

/-- The perturbed defect remains infinitesimal, including for a negative perturbation. -/
theorem contact_perturbed_defect_infinitesimal (τ e : SignSequence.{u}) (hp : 0 < τ)
    (hi : SignSequence.IsInfinitesimal τ)
    (hu : SignSequence.IsInfinitesimal (e / τ)) : SignSequence.IsInfinitesimal (τ + e) := by
  have he : e = τ * (e / τ) := by field_simp [hp.ne']
  have hei : SignSequence.IsInfinitesimal e := by
    rw [he]
    exact SignSequence.finite_mul_infinitesimal (SignSequence.finite_of_infinitesimal hi) hu
  exact SignSequence.infinitesimal_add hi hei

/-- The signed contact displacement has a finite error coefficient at the exact relative rate.
The equality also holds at the zero perturbation; nonzero input is needed only for valuation. -/
theorem arccosFunction_contact_expansion (τ e : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ)
    (hu : SignSequence.IsInfinitesimal (e / τ)) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
      arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ) =
        e / SignSequence.sqrt (τ * (2 - τ)) * (1 + (e / τ) * E) := by
  let u : SignSequence.{u} := e / τ
  let a := SignSequence.sqrt (τ * (2 - τ))
  let b := SignSequence.sqrt ((τ + e) * (2 - (τ + e)))
  let r := b / a
  let k := (2 - 2 * τ - e) / (2 - τ)
  let t := e / (a + b)
  let j := e / ((2 - τ) * (1 + r) ^ 2)
  have hτf := SignSequence.finite_of_infinitesimal hi
  have huf : SignSequence.IsFinite u := SignSequence.finite_of_infinitesimal hu
  have he : e = τ * u := by dsimp only [u]; field_simp [hp.ne']
  have hei : SignSequence.IsInfinitesimal e := by
    rw [he]
    exact SignSequence.finite_mul_infinitesimal hτf hu
  have hef := SignSequence.finite_of_infinitesimal hei
  have hτlt : τ < 1 := (le_abs_self τ).trans_lt (contact_infinitesimal_lt_one hi)
  have hσp := contact_perturbed_defect_pos τ e hp hu
  have hσi := contact_perturbed_defect_infinitesimal τ e hp hi hu
  have hσlt : τ + e < 1 := (le_abs_self _).trans_lt (contact_infinitesimal_lt_one hσi)
  have hcp : 0 < 2 - τ := by linarith only [hτlt]
  have hcf := SignSequence.finite_sub contact_finite_two hτf
  have hcs : SignSequence.standardPart (2 - τ) = 2 := by
    rw [SignSequence.standardPart_sub contact_finite_two hτf, contact_standardPart_two,
      (SignSequence.standardPart_eq_zero_iff hτf).mpr hi, sub_zero]
  have hci := SignSequence.finite_inv_of_standardPart_ne_zero hcf (by rw [hcs]; norm_num)
  have hap : 0 < a := SignSequence.sqrt_pos (mul_pos hp hcp)
  have hbp : 0 < b := SignSequence.sqrt_pos (mul_pos hσp (by linarith only [hσlt]))
  have ha2 : a ^ 2 = τ * (2 - τ) := SignSequence.sqrt_sq (mul_pos hp hcp).le
  have hb2 : b ^ 2 = (τ + e) * (2 - (τ + e)) :=
    SignSequence.sqrt_sq (mul_pos hσp (by linarith only [hσlt])).le
  have hrp : 0 < r := div_pos hbp hap
  have hkf : SignSequence.IsFinite k :=
    SignSequence.finite_mul (SignSequence.finite_sub
      (SignSequence.finite_sub contact_finite_two
        (SignSequence.finite_mul contact_finite_two hτf)) hef) hci
  have hrsq : r ^ 2 - 1 = u * k := by
    dsimp only [r, u, k]
    rw [div_pow, hb2, ha2]
    field_simp [hp.ne', hcp.ne']
    ring
  have hrnear : SignSequence.IsInfinitesimal (r - 1) := by
    apply SignSequence.infinitesimal_sub_one_of_sq_sub_one hrp.le
    rw [hrsq]
    exact SignSequence.infinitesimal_mul_finite hu hkf
  have hrf := SignSequence.finite_of_infinitesimal_sub_one hrnear
  have hrs := SignSequence.standardPart_eq_one_of_infinitesimal_sub_one hrnear
  have hdf := SignSequence.finite_add SignSequence.finite_one hrf
  have hds : SignSequence.standardPart (1 + r) = 2 := by
    rw [SignSequence.standardPart_add SignSequence.finite_one hrf,
      SignSequence.standardPart_one, hrs]
    norm_num
  have hdne : 1 + r ≠ 0 := (add_pos zero_lt_one hrp).ne'
  have hdi := SignSequence.finite_inv_of_standardPart_ne_zero hdf (by rw [hds]; norm_num)
  have hjf : SignSequence.IsFinite j := by
    dsimp only [j]
    rw [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    exact SignSequence.finite_mul hef (SignSequence.finite_mul (SignSequence.finite_pow hdi 2) hci)
  have hsumfactor : a + b = a * (1 + r) := by
    dsimp only [r]
    field_simp [hap.ne']
  have ht2 : t ^ 2 = u * j := by
    dsimp only [t, u, j]
    rw [hsumfactor, div_pow, mul_pow, ha2]
    field_simp [hp.ne', hcp.ne', hdne]
  have hti : SignSequence.IsInfinitesimal t := by
    apply (SignSequence.infinitesimal_sq_iff t).mp
    rw [ht2]
    exact SignSequence.infinitesimal_mul_finite hu hjf
  obtain ⟨R, hR, hRe⟩ := arctanFunction_cubic_remainder t hti
  let F := -k / (1 + r) ^ 2
  let G := j * R
  have hFf : SignSequence.IsFinite F := by
    dsimp only [F]
    rw [div_eq_mul_inv, ← inv_pow]
    exact SignSequence.finite_mul (SignSequence.finite_neg hkf) (SignSequence.finite_pow hdi 2)
  have hGf : SignSequence.IsFinite G := SignSequence.finite_mul hjf hR
  have hFe : 2 / (1 + r) = 1 + u * F := by
    dsimp only [F]
    field_simp [hdne]
    nlinarith only [hrsq]
  have hGe : arctanFunction t = t * (1 + u * G) := by
    rw [hRe]
    dsimp only [G]
    linear_combination t * R * ht2
  refine ⟨F + G + u * F * G,
    SignSequence.finite_add (SignSequence.finite_add hFf hGf)
      (SignSequence.finite_mul (SignSequence.finite_mul huf hFf) hGf), ?_⟩
  have hq := arccosFunction_one_sub_difference τ (τ + e)
    ⟨hp, by linarith only [hτlt]⟩ ⟨hσp, by linarith only [hσlt]⟩
  change arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ) =
    2 * arctanFunction ((τ + e - τ) / (a + b)) at hq
  rw [add_sub_cancel_left] at hq
  change arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ) =
    2 * arctanFunction t at hq
  rw [hq, hGe]
  change 2 * (t * (1 + u * G)) = e / a * (1 + u * (F + G + u * F * G))
  have ht : 2 * t = (e / a) * (2 / (1 + r)) := by
    dsimp only [t]
    rw [hsumfactor]
    field_simp [hap.ne', hdne]
  calc
    2 * (t * (1 + u * G)) = (2 * t) * (1 + u * G) := by ring
    _ = (e / a) * (1 + u * F) * (1 + u * G) := by rw [ht, hFe]
    _ = e / a * (1 + u * (F + G + u * F * G)) := by ring

/-- The exact relative error factor in contact stability has ordinary standard part one. -/
theorem arccosFunction_contact_expansion_standardPart (τ e : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ)
    (hu : SignSequence.IsInfinitesimal (e / τ)) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
      SignSequence.standardPart (1 + (e / τ) * E) = 1 ∧
      arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ) =
        e / SignSequence.sqrt (τ * (2 - τ)) * (1 + (e / τ) * E) := by
  obtain ⟨E, hE, he⟩ := arccosFunction_contact_expansion τ e hp hi hu
  refine ⟨E, hE, ?_, he⟩
  apply SignSequence.standardPart_eq_one_of_infinitesimal_sub_one
  simpa only [add_sub_cancel_left] using SignSequence.infinitesimal_mul_finite hu hE

private theorem contact_height_pos (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    0 < SignSequence.sqrt (τ * (2 - τ)) := by
  have hlt := (le_abs_self τ).trans_lt (contact_infinitesimal_lt_one hi)
  exact SignSequence.sqrt_pos (mul_pos hp (by linarith only [hlt]))

/-- The first-order contact displacement has infinitesimal relative error even for a negative input. -/
theorem arccosFunction_contact_relative_error (τ e : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) (he0 : e ≠ 0)
    (hu : SignSequence.IsInfinitesimal (e / τ)) :
    SignSequence.IsInfinitesimal
      ((arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ)) /
        (e / SignSequence.sqrt (τ * (2 - τ))) - 1) := by
  obtain ⟨E, hE, he⟩ := arccosFunction_contact_expansion τ e hp hi hu
  rw [he, mul_div_cancel_left₀ _ (div_ne_zero he0 (contact_height_pos τ hp hi).ne'),
    add_sub_cancel_left]
  exact SignSequence.infinitesimal_mul_finite hu hE

/-- The positive circle height at the contact point has exactly half the defect's valuation. -/
theorem valuation_contact_height (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.valuation (SignSequence.sqrt (τ * (2 - τ))) =
      ((-SignSequence.leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have hf := SignSequence.finite_of_infinitesimal hi
  have hcf := SignSequence.finite_sub contact_finite_two hf
  have hcs : SignSequence.standardPart (2 - τ) = 2 := by
    rw [SignSequence.standardPart_sub contact_finite_two hf, contact_standardPart_two,
      (SignSequence.standardPart_eq_zero_iff hf).mpr hi, sub_zero]
  have hlt := (le_abs_self τ).trans_lt (contact_infinitesimal_lt_one hi)
  have hcp : 0 < 2 - τ := by linarith only [hlt]
  have hcv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hcf).mpr
    (by rw [hcs]; norm_num)
  have hcL : SignSequence.leadingExponent (2 - τ) = 0 := by
    rw [SignSequence.valuation_of_ne_zero hcp.ne'] at hcv
    have he : -SignSequence.leadingExponent (2 - τ) = 0 :=
      WithTop.coe_injective (by simpa only [WithTop.coe_zero] using hcv)
    exact neg_eq_zero.mp he
  rw [SignSequence.valuation_sqrt (mul_pos hp hcp),
    SignSequence.leadingExponent_mul hp.ne' hcp.ne', hcL, add_zero]

/-- The signed contact displacement loses exactly half the defect's valuation,
with all finite exponents written as actual surreals. -/
theorem valuation_arccosFunction_contact (τ e : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) (he0 : e ≠ 0)
    (hu : SignSequence.IsInfinitesimal (e / τ)) :
    SignSequence.valuation
      (arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ)) =
      ((-SignSequence.leadingExponent e + SignSequence.leadingExponent τ / 2 :
        SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have h := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (div_ne_zero he0 (contact_height_pos τ hp hi).ne')
    (arccosFunction_contact_relative_error τ e hp hi he0 hu)
  rw [h, SignSequence.valuation_div, valuation_contact_height τ hp hi,
    SignSequence.valuation_of_ne_zero he0]
  change ((-SignSequence.leadingExponent e - (-SignSequence.leadingExponent τ / 2) :
    SignSequence.{u}) : WithTop SignSequence.{u}) = _
  congr 1
  ring

/-- The contact valuation law in intrinsic doubled-valuation notation. -/
theorem two_nsmul_valuation_arccosFunction_contact (τ e : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) (he0 : e ≠ 0)
    (hu : SignSequence.IsInfinitesimal (e / τ)) :
    2 • SignSequence.valuation
      (arccosFunction (1 - (τ + e)) - arccosFunction (1 - τ)) =
      2 • SignSequence.valuation e - SignSequence.valuation τ := by
  rw [valuation_arccosFunction_contact τ e hp hi he0 hu,
    SignSequence.valuation_of_ne_zero he0, SignSequence.valuation_of_ne_zero hp.ne',
    ← WithTop.coe_nsmul, ← WithTop.coe_nsmul]
  change ((_ : SignSequence.{u}) : WithTop SignSequence.{u}) =
    ((2 • -SignSequence.leadingExponent e - -SignSequence.leadingExponent τ :
      SignSequence.{u}) : WithTop SignSequence.{u})
  congr 1
  simp only [nsmul_eq_mul]
  ring

end Surreal.Surcomplex
