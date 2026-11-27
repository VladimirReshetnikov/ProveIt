import GRHArticle.ProgressionFree.IntegerBoundaryExchangeReplacement
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# The reciprocal-square charge for nonsmooth ratios
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

private noncomputable def reciprocalSquareHom : ℕ →* ℝ where
  toFun n := 1/(n:ℝ)^2
  map_one' := by norm_num
  map_mul' a b := by
    simp only [Nat.cast_mul, mul_pow, one_div, mul_inv_rev]
    exact mul_comm _ _

private theorem reciprocalSquareHom_norm_lt {p : ℕ} (hp : p.Prime) :
    ‖reciprocalSquareHom p‖ < 1 := by
  change ‖1/(p:ℝ)^2‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

private theorem hasSum_reciprocalSquare_fiveSmooth :
    HasSum (fun s : Nat.smoothNumbers 6 ↦ 1/(s.val:ℝ)^2) (25/16) := by
  have h :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      reciprocalSquareHom_norm_lt 6).2
  have hP : Nat.primesBelow 6 = ({2,3,5} : Finset ℕ) := by decide
  rw [hP] at h
  have he : (∏ p ∈ ({2,3,5} : Finset ℕ), (1 - reciprocalSquareHom p)⁻¹) = (25:ℝ)/16 := by
    norm_num [reciprocalSquareHom, Finset.prod_insert]
  rw [he] at h
  exact h

/-- The total charge over nonsmooth ratios is summable. -/
theorem summable_integerExchangeBoundaryTail :
    Summable (fun r : ↥((Nat.smoothNumbers 6)ᶜ) ↦ 1/(r.val:ℝ)^2) := by
  exact hasSum_zeta_two.summable.comp_injective
    (i := (Subtype.val : ↥((Nat.smoothNumbers 6)ᶜ) → ℕ)) Subtype.val_injective

/-- The nonsmooth reciprocal-square mass, including the harmless zero term. -/
theorem integerExchangeBoundaryTail_eq :
    (∑' r : ↥((Nat.smoothNumbers 6)ᶜ), 1/(r.val:ℝ)^2) = Real.pi^2/6 - 25/16 := by
  have h := hasSum_zeta_two.summable.tsum_subtype_add_tsum_subtype_compl (Nat.smoothNumbers 6)
  rw [hasSum_zeta_two.tsum_eq, hasSum_reciprocalSquare_fiveSmooth.tsum_eq] at h
  linarith

theorem integerExchangeBoundaryTail_lt :
    (∑' r : ↥((Nat.smoothNumbers 6)ᶜ), 1/(r.val:ℝ)^2) < integerExchangeCharge := by
  rw [integerExchangeBoundaryTail_eq, integerExchangeCharge]
  have hp := Real.pi_lt_d20
  have hπ : Real.pi^2 < (3.14159265358979323847 : ℝ)^2 :=
    pow_lt_pow_left₀ hp Real.pi_pos.le (by decide)
  nlinarith only [hπ]

end GRHArticle.ProgressionFree
