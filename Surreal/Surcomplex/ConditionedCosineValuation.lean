import Surreal.Surcomplex.ConditionedCosineExpansion
import Surreal.Foundations.SignSequencePolynomialStabilityError

/-!
# Valuation bounds for conditioned inversion of cosine

The normalized finite remainder gives all three exponents in
`trigonometry:eq:inversecos`, under `trigonometry:eq:condition`.
The result is stated first for coordinates on the upper unit semicircle,
then for every actual finite angle strictly between zero and pi.
-/

universe u

namespace Surreal.Surcomplex.ConditionedCosine

open Foundations

noncomputable section

local notation "v" => SignSequence.valuation

/-- Valuation of the normalized perturbation, with finite input valuations. -/
theorem valuation_normalized (s e k σ : SignSequence.{u})
    (hs : v s = ↑k) (he : v e = ↑σ) : v (e / s ^ 2) = ↑(σ - 2 * k) := by
  rw [SignSequence.valuation_div, pow_two, SignSequence.valuation_mul, hs, he]
  change ((σ - (k + k) : SignSequence.{u}) : WithTop SignSequence.{u}) = ↑(σ - 2 * k)
  congr 1
  ring

/-- The sharp condition is precisely infinitesimality of the normalized perturbation. -/
theorem infinitesimal_normalized (s e k σ : SignSequence.{u})
    (hs : v s = ↑k) (he : v e = ↑σ) (hσ : 2 * k < σ) :
    SignSequence.IsInfinitesimal (e / s ^ 2) := by
  rw [SignSequence.isInfinitesimal_iff_valuation_pos, valuation_normalized s e k σ hs he]
  exact WithTop.coe_pos.mpr (sub_pos.mpr hσ)

/-- The second-order formula and both displacement bounds on the upper unit semicircle. -/
theorem expansion_valuation (c s e k σ : SignSequence.{u})
    (hc : SignSequence.IsFinite c) (hsf : SignSequence.IsFinite s) (hs : 0 < s)
    (hcircle : c ^ 2 + s ^ 2 = 1) (hvs : v s = ↑k) (hve : v e = ↑σ)
    (hσ : 2 * k < σ) :
    c + e ∈ Set.Ioo (-1) 1 ∧
      ∃ R : SignSequence.{u},
        arccosFunction (c + e) - arccosFunction c = -e / s - c * e ^ 2 / (2 * s ^ 3) + R ∧
        (3 * σ - 5 * k : SignSequence.{u}) ≤ v R ∧
        v (arccosFunction (c + e) - arccosFunction c) = ↑(σ - k) ∧
        (2 * σ - 3 * k : SignSequence.{u}) ≤
          v (arccosFunction (c + e) - arccosFunction c + e / s) := by
  have hu := infinitesimal_normalized s e k σ hvs hve hσ
  refine ⟨perturbed_mem_Ioo c s e hs hcircle hu, ?_⟩
  obtain ⟨H, hH, hexp⟩ := normalized_expansion c s e hc hsf hs hcircle hu
  let u := e / s ^ 2
  have huv : v u = ↑(σ - 2 * k) := valuation_normalized s e k σ hvs hve
  have hu2 : v (u ^ 2) = ↑(2 * (σ - 2 * k)) := by
    rw [pow_two, SignSequence.valuation_mul, huv, ← WithTop.coe_add, ← two_mul]
  have hu3 : v (u ^ 3) = ↑(3 * (σ - 2 * k)) := by
    rw [pow_succ, SignSequence.valuation_mul, hu2, huv, ← WithTop.coe_add]
    congr 1
    ring
  have hhalf : SignSequence.IsFinite (1 / 2 : SignSequence.{u}) := by
    simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)
  let Q := -c / 2 + u * H
  have hQ : SignSequence.IsFinite Q :=
    SignSequence.finite_add
      (by simpa only [div_eq_mul_inv, one_mul] using
        SignSequence.finite_mul (SignSequence.finite_neg hc) hhalf)
      (SignSequence.finite_mul (SignSequence.finite_of_infinitesimal hu) hH)
  have hR : (3 * σ - 5 * k : SignSequence.{u}) ≤ v (s * u ^ 3 * H) := by
    have hp := SignSequence.valuation_mul_ge_of_ge s (u ^ 3) k (3 * (σ - 2 * k))
      hvs.ge hu3.ge
    have hr := SignSequence.valuation_mul_ge_of_ge (s * u ^ 3) H
      (k + 3 * (σ - 2 * k)) 0 hp ((SignSequence.isFinite_iff_valuation_nonneg H).mp hH)
    convert hr using 1
    congr 1
    ring
  have hcorr : (2 * σ - 3 * k : SignSequence.{u}) ≤ v (s * u ^ 2 * Q) := by
    have hp := SignSequence.valuation_mul_ge_of_ge s (u ^ 2) k (2 * (σ - 2 * k))
      hvs.ge hu2.ge
    have hr := SignSequence.valuation_mul_ge_of_ge (s * u ^ 2) Q
      (k + 2 * (σ - 2 * k)) 0 hp ((SignSequence.isFinite_iff_valuation_nonneg Q).mp hQ)
    convert hr using 1
    congr 1
    ring
  have heq : arccosFunction (c + e) - arccosFunction c = -s * u + s * u ^ 2 * Q := by
    rw [hexp]
    dsimp only [Q, u]
    ring
  have hlin : v (-s * u) = ↑(σ - k) := by
    rw [SignSequence.valuation_mul, SignSequence.valuation_neg, hvs, huv, ← WithTop.coe_add]
    congr 1
    ring
  have hval : v (arccosFunction (c + e) - arccosFunction c) = ↑(σ - k) := by
    rw [heq, SignSequence.valuation.map_add_eq_of_lt_left (by
      rw [hlin]
      exact (show ((σ - k : SignSequence.{u}) : WithTop SignSequence.{u}) <
        ↑(2 * σ - 3 * k) from WithTop.coe_lt_coe.mpr (by linarith)).trans_le hcorr), hlin]
  refine ⟨s * u ^ 3 * H, ?_, hR, hval, ?_⟩
  · rw [hexp]
    dsimp only [u]
    field_simp
  · have he : arccosFunction (c + e) - arccosFunction c + e / s = s * u ^ 2 * Q := by
      rw [heq]
      dsimp only [u]
      field_simp
      ring
    rw [he]
    exact hcorr

/-- Conditioned inversion of cosine at every actual interior angle, including infinitesimal sine. -/
theorem conditioned_inversion (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi))
    (e k σ : SignSequence.{u}) (hs : v (finiteSin θ) = ↑k)
    (he : v e = ↑σ) (hσ : 2 * k < σ) :
    finiteCos θ + e ∈ Set.Ioo (-1) 1 ∧
      ∃ R : SignSequence.{u},
        arccosFunction (finiteCos θ + e) - θ.val =
          -e / finiteSin θ - finiteCos θ * e ^ 2 / (2 * finiteSin θ ^ 3) + R ∧
        (3 * σ - 5 * k : SignSequence.{u}) ≤ v R ∧
        v (arccosFunction (finiteCos θ + e) - θ.val) = ↑(σ - k) ∧
        (2 * σ - 3 * k : SignSequence.{u}) ≤
          v (arccosFunction (finiteCos θ + e) - θ.val + e / finiteSin θ) := by
  have hinv : arccosFunction (finiteCos θ) = θ.val := by
    rw [arccosFunction_eq ⟨finiteCos θ, finiteCos_mem_Icc θ⟩,
      arccos_finiteCos θ ⟨hθ.1.le, hθ.2.le⟩]
  simpa only [hinv] using expansion_valuation (finiteCos θ) (finiteSin θ) e k σ
    (isFinite_finiteCos θ) (isFinite_finiteSin θ) (finiteSin_pos_of_mem_Ioo θ hθ)
    (finiteCos_sq_add_finiteSin_sq θ) hs he hσ

end
end Surreal.Surcomplex.ConditionedCosine
