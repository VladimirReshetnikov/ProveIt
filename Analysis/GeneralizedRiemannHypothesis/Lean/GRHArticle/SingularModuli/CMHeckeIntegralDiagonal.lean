import GRHArticle.SingularModuli.CMHeckePolynomialDescent
import GRHArticle.SingularModuli.ModularIntegralExpansions
import GRHArticle.SingularModuli.HeckeRootOfUnityIntegrality
import GRHArticle.SingularModuli.ClearedSeriesPolynomialDescent
import GRHArticle.SingularModuli.ConvergentPowerSeriesEvaluation
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# The prime Hecke diagonal has integer coefficients

Use the variable `u = exp(2*pi*i*z/p)` to write the normalized diagonal
as an absolutely convergent series. Its shifted factors are permuted by
the nonzero elements of `ZMod p`. The resulting integer series determines
the integer coefficients of the monic polynomial in `j`.
-/

namespace GRHArticle.SingularModuli

open UpperHalfPlane PowerSeries
open scoped PowerSeries

local notation "q" => Function.Periodic.qParam 1
local notation "qAt" => Function.Periodic.qParam
local notation "j" => modularInvariant
local notation "JSeries" => integralNormalizedJExpansion
local notation "castSeries" => PowerSeries.map (Int.castRingHom ℂ)

private theorem exists_value_integralNormalizedJExpansion :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z : ℍ, ‖q z‖ < r →
      PowerSeriesValue (castSeries JSeries) (q z) (q z * j z) := by
  obtain ⟨ε, hε, he⟩ := hasSum_integralNormalizedJExpansion
  let r := min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hε) (by norm_num)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hr₁ : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let v : ℂ := (r : ℂ)
  have hv : ‖v‖ = r := by simp [v, abs_of_pos hr]
  have hv₀ : v ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  let w : ℍ := ⟨Function.Periodic.invQParam 1 v,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos (hv.trans_lt hr₁) hv₀⟩
  have hw : q w = v := Function.Periodic.qParam_right_inv one_ne_zero hv₀
  refine ⟨r, hr, hr₁.le, fun z hz ↦ ?_⟩
  have hwNorm : ‖q w‖ < ε := by rw [hw]; exact hv.trans_lt hrε
  have hb := he w hwNorm
  rw [hw] at hb
  refine PowerSeriesValue.of_hasSum_of_norm_lt (v := v) (b := v * j w) ?_ ?_
    (hz.trans_eq hv.symm)
  · simpa only [coeff_map, Int.coe_castRingHom] using he z (hz.trans hrε)
  · simpa only [coeff_map, Int.coe_castRingHom] using hb

private theorem qAt_prime_pow (p : ℕ+) (z : ℍ) :
    (qAt (p : ℝ) z) ^ (p : ℕ) = q z := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.pos.ne'
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_one, div_one,
    Complex.ofReal_natCast]
  congr 1
  field_simp [hp]

private theorem q_heckeScaled_eq (p : ℕ+) (z : ℍ) :
    q (heckeScaledPoint p z) = (q z) ^ (p : ℕ) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_one, div_one,
    heckeScaledPoint, coe_mk, Complex.ofReal_natCast]
  congr 1
  ring

private theorem q_heckeShift_eq (p : ℕ+) (t : ZMod (p : ℕ)) (z : ℍ) :
    q (heckeShiftPoint p t.val z) = ZMod.stdAddChar t * qAt (p : ℝ) z := by
  conv_rhs => rw [← ZMod.natCast_zmod_val t]
  have hc : ((t.val : ℤ) : ZMod (p : ℕ)) = (t.val : ZMod (p : ℕ)) :=
    Int.cast_natCast _
  rw [← hc, ZMod.stdAddChar_coe]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, heckeShiftPoint, coe_mk,
    Int.cast_natCast, Complex.ofReal_natCast, ← Complex.exp_add]
  congr 1
  ring

private theorem prod_zmod_val_eq_range (p : ℕ+) (f : ℕ → ℂ) :
    (∏ t : ZMod (p : ℕ), f t.val) = ∏ t ∈ Finset.range (p : ℕ), f t := by
  refine Finset.prod_bij (fun t _ ↦ t.val)
    (fun t _ ↦ Finset.mem_range.mpr (ZMod.val_lt t)) ?_ ?_ ?_
  · exact fun _ _ _ _ h ↦ ZMod.val_injective _ h
  · intro n hn
    exact ⟨(n : ZMod (p : ℕ)), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)⟩
  · intros; rfl

private theorem value_clearedSeriesPolynomialEvaluation (P : Polynomial ℂ)
    (s : ℕ) {A : ℂ⟦X⟧} {u j₀ : ℂ} (hA : PowerSeriesValue A u (u ^ s * j₀))
    (n : ℕ) :
    PowerSeriesValue (clearedSeriesPolynomialEvaluation P s A n) u
      ((u ^ s) ^ n * ∑ i ∈ Finset.range (n + 1), P.coeff i * j₀ ^ i) := by
  induction n with
  | zero =>
    simpa [clearedSeriesPolynomialEvaluation] using PowerSeriesValue.C (P.coeff 0) u
  | succ n ih =>
    have ht := ((PowerSeriesValue.X_pow s u).mul ih).add
      ((PowerSeriesValue.C (P.coeff (n + 1)) u).mul (hA.pow (n + 1)))
    convert ht using 1
    · rw [clearedSeriesPolynomialEvaluation]
    · rw [Finset.sum_range_succ, mul_pow, pow_succ']
      ring

private theorem integralHeckeDiagonal_representation (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))]
    (P : Polynomial ℂ) (hmonic : P.Monic) (hdeg : P.natDegree = 2 * (p : ℕ))
    (hP : ∀ z : ℍ, P.eval (j z) = -analyticPrimeHeckeDiagonal p z) :
    ∃ F : ℤ⟦X⟧, castSeries F =
      clearedSeriesPolynomialEvaluation P (p : ℕ)
        (castSeries (expand (p : ℕ) p.pos.ne' JSeries)) (2 * (p : ℕ)) := by
  let m : ℕ := p
  have hm₀ : m ≠ 0 := p.pos.ne'
  have hm₁ : 1 < m := hp.out.one_lt
  let A : ℤ⟦X⟧ := expand m hm₀ JSeries
  let B : ℤ⟦X⟧ := expand (m * m) (mul_ne_zero hm₀ hm₀) JSeries
  obtain ⟨F, hF⟩ := exists_integral_primeRootProduct m A JSeries (m - 1)
  let G : ℤ⟦X⟧ := (B - X ^ (m * m - m) * A) * F
  refine ⟨G, ?_⟩
  obtain ⟨r, hr, hr₁, hJ⟩ := exists_value_integralNormalizedJExpansion
  apply eq_of_powerSeriesValues hr
  intro u hu
  by_cases hu₀ : u = 0
  · subst u
    have hJ₀ : constantCoeff (castSeries JSeries) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_integralNormalizedJExpansion]
      norm_num
    have hA₀ : constantCoeff (castSeries A) = 1 := by simpa only [A, map_expand,
      constantCoeff_expand] using hJ₀
    have hB₀ : constantCoeff (castSeries B) = 1 := by simpa only [B, map_expand,
      constantCoeff_expand] using hJ₀
    have hm₁' := Nat.sub_ne_zero_of_lt hm₁
    have hpow : m * m - m ≠ 0 := Nat.sub_ne_zero_of_lt (by nlinarith)
    have hF₀ : constantCoeff (castSeries F) = 1 := by
      rw [hF, map_prod]
      simp [hA₀, zero_pow hm₁']
    have hG₀ : constantCoeff (castSeries G) = 1 := by
      simp [G, hB₀, hF₀, zero_pow hpow]
    have hcleared : constantCoeff (clearedSeriesPolynomialEvaluation P m (castSeries A) (2*m)) = 1 := by
      have hcoef : P.coeff (2*m) = 1 := by
        simpa only [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] using hmonic
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (mul_ne_zero (by decide) hm₀ : 2*m ≠ 0)
      rw [hn] at hcoef ⊢
      simp [clearedSeriesPolynomialEvaluation, zero_pow hm₀, hA₀, hcoef]
    refine ⟨1, ?_, ?_⟩
    · simpa only [coeff_zero_eq_constantCoeff_apply, hG₀] using PowerSeriesValue.at_zero (castSeries G)
    · simpa only [coeff_zero_eq_constantCoeff_apply, hcleared] using
        PowerSeriesValue.at_zero (clearedSeriesPolynomialEvaluation P m (castSeries A) (2*m))
  · have hpR : (0 : ℝ) < p := by positivity
    let z : ℍ := ⟨Function.Periodic.invQParam (p : ℝ) u,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one hpR (hu.trans_le hr₁) hu₀⟩
    have huZ : qAt (p : ℝ) z = u := Function.Periodic.qParam_right_inv hpR.ne' hu₀
    have hx : u ^ m = q z := by simpa only [huZ] using qAt_prime_pow p z
    have hx₂ : u ^ (m*m) = q (heckeScaledPoint p z) := by rw [q_heckeScaled_eq, ← hx, pow_mul]
    have habs (n : ℕ) (hn : n ≠ 0) : ‖u ^ n‖ < r := by
      rw [norm_pow]
      rcases n with _ | n
      · exact (hn rfl).elim
      · rw [pow_succ]
        calc
          ‖u‖ ^ n * ‖u‖ ≤ 1 * ‖u‖ := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) (hu.le.trans hr₁)
          _ < r := by simpa using hu
    have hA : PowerSeriesValue (castSeries A) u (q z * j z) := by
      change PowerSeriesValue (castSeries (expand m hm₀ JSeries)) u (q z * j z)
      rw [map_expand]
      apply PowerSeriesValue.expand hm₀
      rw [hx]
      exact hJ z (hx ▸ habs m hm₀)
    have hB : PowerSeriesValue (castSeries B) u
        (q (heckeScaledPoint p z) * j (heckeScaledPoint p z)) := by
      change PowerSeriesValue (castSeries (expand (m*m) (mul_ne_zero hm₀ hm₀) JSeries)) u _
      rw [map_expand]
      apply PowerSeriesValue.expand (mul_ne_zero hm₀ hm₀)
      rw [hx₂]
      exact hJ _ (hx₂ ▸ habs (m*m) (mul_ne_zero hm₀ hm₀))
    let diff (t : ℕ) := j z - j (heckeShiftPoint p t z)
    have hprod : PowerSeriesValue (castSeries F) u
        ((q z) ^ m * ∏ t ∈ Finset.range m, diff t) := by
      have hfactor : (q z) ^ m * (∏ t ∈ Finset.range m, diff t) =
          ∏ t : ZMod m, q z * diff t.val := by
        rw [prod_zmod_val_eq_range p (fun t ↦ q z * diff t), Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_range]
      rw [hF, hfactor]
      apply PowerSeriesValue.prod
      intro t _
      have hq_t : q (heckeShiftPoint p t.val z) = ZMod.stdAddChar t * u := by
        rw [q_heckeShift_eq, huZ]
      have hn : ‖q (heckeShiftPoint p t.val z)‖ < r := by
        simpa only [hq_t, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul] using hu
      have hj_t := hJ _ hn
      rw [hq_t] at hj_t
      have ht := hA.sub (((PowerSeriesValue.C (ZMod.stdAddChar (-t)) u).mul
        (PowerSeriesValue.X_pow (m - 1) u)).mul hj_t.rescale)
      have hs : ZMod.stdAddChar (-t) * ZMod.stdAddChar t = (1 : ℂ) := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      convert ht using 1
      dsimp [diff]
      rw [mul_sub]
      congr 1
      calc
        q z * j (heckeShiftPoint p t.val z) =
            (u ^ (m - 1) * u) * j (heckeShiftPoint p t.val z) := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_of_lt hm₁), hx]
        _ = _ := by
          conv_lhs => rw [← one_mul (u ^ (m - 1) * u), ← hs]
          ring
    have hfirst :
        PowerSeriesValue (castSeries (B - X ^ (m*m-m) * A)) u
          ((q z) ^ m * (j (heckeScaledPoint p z) - j z)) := by
      rw [map_sub, map_mul, map_pow, map_X]
      have h := hB.sub ((PowerSeriesValue.X_pow (m*m-m) u).mul hA)
      convert h using 1
      rw [mul_sub, ← hx₂, ← hx, ← pow_mul]
      congr 1
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by nlinarith)]
    have hvG := hfirst.mul hprod
    rw [← map_mul] at hvG
    have hv := value_clearedSeriesPolynomialEvaluation P m (hx.symm ▸ hA) (2*m)
    rw [hx, ← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg.le), hP] at hv
    refine ⟨(q z) ^ (2*m) * (-analyticPrimeHeckeDiagonal p z), ?_, hv⟩
    unfold G
    convert hvG using 1
    simp only [analyticPrimeHeckeDiagonal, analyticPrimeHeckePolynomial, Polynomial.eval_mul,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, diff]
    rw [two_mul, pow_add]
    ring

/-- The prime Hecke diagonal, with its sign normalized to be monic, is a
polynomial over the integers of degree exactly `2*p`. -/
theorem exists_int_monic_analyticPrimeHeckeDiagonal (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * (p : ℕ) ∧
      ∀ z : ℍ, Polynomial.aeval (j z) P = -analyticPrimeHeckeDiagonal p z := by
  obtain ⟨P, hmonic, hdeg, hP⟩ := exists_monic_poly_analyticPrimeHeckeDiagonal p
  obtain ⟨F, hF⟩ := integralHeckeDiagonal_representation p P hmonic hdeg hP
  obtain ⟨Q, hQ⟩ := exists_intPolynomial_of_clearedSeriesPolynomialEvaluation P p.pos.ne'
    (expand (p : ℕ) p.pos.ne' JSeries) (by simp [constantCoeff_integralNormalizedJExpansion])
    (2 * (p : ℕ)) hdeg.le F hF
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  refine ⟨Q, hinj.monic_map_iff.mpr (by rw [hQ]; exact hmonic), ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hQ, hdeg]
  · intro z
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, algebraMap_int_eq, hQ, hP]

theorem isIntegral_modularInvariant_of_heckeDiagonal_zero (p : ℕ+)
    [Fact (Nat.Prime (p : ℕ))] {z : ℍ} (h : analyticPrimeHeckeDiagonal p z = 0) :
    IsIntegral ℤ (j z) := by
  obtain ⟨P, hmonic, _, he⟩ := exists_int_monic_analyticPrimeHeckeDiagonal p
  refine ⟨P, hmonic, ?_⟩
  change Polynomial.aeval (j z) P = 0
  rw [he, h, neg_zero]

/-- All four analytic CM values of discriminant `-55` are algebraic integers. -/
theorem quartic55_singularModulus_isIntegral (i : Fin 4) :
    let f := quartic55Form i
    IsIntegral ℤ (j (quadraticPoint 55 f.a f.b)) := by
  letI : Fact (Nat.Prime ((59 : ℕ+) : ℕ)) := ⟨by decide⟩
  exact isIntegral_modularInvariant_of_heckeDiagonal_zero 59
    (quartic55_analyticPrimeHeckePolynomial_diagonal i)

/-- All four analytic CM values of discriminant `-68` are algebraic integers. -/
theorem quartic68_singularModulus_isIntegral (i : Fin 4) :
    let f := quartic68Form i
    IsIntegral ℤ (j (quadraticPoint 68 f.a f.b)) := by
  letI : Fact (Nat.Prime ((17 : ℕ+) : ℕ)) := ⟨by decide⟩
  exact isIntegral_modularInvariant_of_heckeDiagonal_zero 17
    (quartic68_analyticPrimeHeckePolynomial_diagonal i)

end GRHArticle.SingularModuli
