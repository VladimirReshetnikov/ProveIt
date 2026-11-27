import GRHArticle.SingularModuli.PadicConvergence
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.ComputeDegree

/-!
# Exact disk certificates for two integer quartics

The coefficients come from
`10802a6b36:Analysis/GeneralizedRiemannHypothesis/Research/grh_sparse_singular_moduli/cm/class_polynomials.json`.
The statements concern these explicit polynomials and their p-adic roots.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- The quartic listed under discriminant -55 in the certificate data. -/
noncomputable def quartic55Int : Polynomial ℤ :=
  C (-18577989025032784359375) + C 172576736359017890625 * X +
    C (-20948398473375) * X ^ 2 + C 13136684625 * X ^ 3 + X ^ 4

/-- The quartic listed under discriminant -68 in the certificate data. -/
noncomputable def quartic68Int : Polynomial ℤ :=
  C (-2089297506304000000000000) + C (-318507038720000000000) * X +
    C (-75843692160000000) * X ^ 2 + C (-178211040000) * X ^ 3 + X ^ 4

/-- The rational polynomial with the coefficients of `quartic55Int`. -/
noncomputable def quartic55 : Polynomial ℚ := quartic55Int.map (Int.castRingHom ℚ)

/-- The rational polynomial with the coefficients of `quartic68Int`. -/
noncomputable def quartic68 : Polynomial ℚ := quartic68Int.map (Int.castRingHom ℚ)

theorem quartic55Int_monic : quartic55Int.Monic := by
  unfold quartic55Int
  monicity!

theorem quartic55Int_natDegree : quartic55Int.natDegree = 4 := by
  unfold quartic55Int
  compute_degree!

theorem quartic68Int_monic : quartic68Int.Monic := by
  unfold quartic68Int
  monicity!

theorem quartic68Int_natDegree : quartic68Int.natDegree = 4 := by
  unfold quartic68Int
  compute_degree!

theorem quartic55_monic : quartic55.Monic :=
  quartic55Int_monic.map _

theorem quartic55_natDegree : quartic55.natDegree = 4 :=
  (quartic55Int_monic.natDegree_map _).trans quartic55Int_natDegree

theorem quartic68_monic : quartic68.Monic :=
  quartic68Int_monic.map _

theorem quartic68_natDegree : quartic68.natDegree = 4 :=
  (quartic68Int_monic.natDegree_map _).trans quartic68Int_natDegree

private theorem norm_natCast_eq_rpow_of_factor {p m v u : ℕ} [hp : Fact (Nat.Prime p)]
    (h : m = p ^ v * u) (hu : ¬p ∣ u) :
    ‖(m : ℂ_[p])‖ = (p : ℝ) ^ (-(v : ℝ)) := by
  have hu₀ : u ≠ 0 := fun hz ↦ hu (hz ▸ dvd_zero p)
  have hpv : p ^ v ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hm : m ≠ 0 := h ▸ mul_ne_zero hpv hu₀
  have hv : padicValNat p m = v := by
    rw [h, padicValNat.mul hpv hu₀, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu, Nat.add_zero]
  rw [padicComplex_norm_natCast m hm, hv, Real.rpow_neg_natCast]

private theorem rpow_weight_domination {q r v w : ℝ} (hq : 1 < q) (d : ℕ)
    (h : w + r * d < v) : q ^ (-v) < q ^ (-w) * (q ^ (-r)) ^ d := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  rw [← Real.rpow_mul_natCast hq₀.le, ← Real.rpow_add hq₀]
  exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith only [h])

private theorem norm_lt_of_quartic_relation {K : Type*} [NormedField K] [IsUltrametricDist K]
    {x c₀ c₁ c₂ c₃ c₄ : K} {R : ℝ} (hR : 0 < R)
    (h₀ : ‖c₀‖ < ‖c₄‖ * R ^ (4 : ℕ)) (h₁ : ‖c₁‖ < ‖c₄‖ * R ^ (3 : ℕ))
    (h₂ : ‖c₂‖ < ‖c₄‖ * R ^ (2 : ℕ)) (h₃ : ‖c₃‖ < ‖c₄‖ * R ^ (1 : ℕ))
    (h : c₀ + c₁*x + c₂*x^2 + c₃*x^3 + c₄*x^4 = 0) : ‖x‖ < R := by
  by_contra! hx
  have hx₀ := hR.trans_le hx
  have hterm (c : K) (i : ℕ) (hi : i ≤ 4) (hc : ‖c‖ < ‖c₄‖ * R ^ (4 - i)) :
      ‖c * x ^ i‖ < ‖c₄ * x ^ 4‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc
      _ < (‖c₄‖ * R ^ (4 - i)) * ‖x‖ ^ i := mul_lt_mul_of_pos_right hc (pow_pos hx₀ _)
      _ ≤ (‖c₄‖ * ‖x‖ ^ (4 - i)) * ‖x‖ ^ i :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hx _) (norm_nonneg _))
          (pow_nonneg hx₀.le _)
      _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  have hadd {u v : K} (hu : ‖u‖ < ‖c₄ * x ^ 4‖) (hv : ‖v‖ < ‖c₄ * x ^ 4‖) :
      ‖u + v‖ < ‖c₄ * x ^ 4‖ :=
    (IsUltrametricDist.norm_add_le_max u v).trans_lt (max_lt hu hv)
  have h₀' : ‖c₀‖ < ‖c₄*x^4‖ := by simpa using hterm c₀ 0 (by decide) h₀
  have h₁' : ‖c₁*x‖ < ‖c₄*x^4‖ := by simpa using hterm c₁ 1 (by decide) h₁
  have hsmall := hadd (hadd (hadd h₀' h₁') (hterm c₂ 2 (by decide) h₂))
    (hterm c₃ 3 (by decide) h₃)
  rw [eq_neg_of_add_eq_zero_left h, norm_neg] at hsmall
  exact (lt_irrefl _ hsmall)

/-- Every p-adic root of the explicit quartic at discriminant -55
lies strictly within the certified relative disk. -/
theorem quartic55_root_in_disk [Fact (Nat.Prime 3)] {x : ℂ_[3]}
    (hx : aeval x quartic55 = 0) :
    ‖x / (27 : ℂ_[3]) - 1‖ < (3 : ℝ) ^ (-(1 : ℝ)) := by
  let z := x / (27 : ℂ_[3]) - 1
  have hz : (27 : ℂ_[3]) * (1 + z) = x := by
    dsimp [z]
    field_simp
    ring
  have hx' : -(18577989025032784359375 : ℂ_[3]) + 172576736359017890625 * x - 20948398473375 * x ^ 2 + 13136684625 * x ^ 3 + x ^ 4 = 0 := by
    simp [quartic55, quartic55Int, sub_eq_add_neg, neg_mul, map_ofNat] at hx ⊢
    exact hx
  have hshift : (-13918432156152424397559) + 4659542114636601413514*z + (-14495674393480104)*z^2 +
      258569365599639*z^3 + 531441*z^4 = 0 := by
    rw [← hz] at hx'
    convert hx' using 1
    ring
  have hn0 : ‖(13918432156152424397559 : ℂ_[3])‖ = (3 : ℝ) ^ (-(20 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 20) (u := 3991767357959) (by decide) (by decide)
  have hn1 : ‖(4659542114636601413514 : ℂ_[3])‖ = (3 : ℝ) ^ (-(18 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 18) (u := 12027092647226) (by decide) (by decide)
  have hn2 : ‖(14495674393480104 : ℂ_[3])‖ = (3 : ℝ) ^ (-(17 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 17) (u := 112247608) (by decide) (by decide)
  have hn3 : ‖(258569365599639 : ℂ_[3])‖ = (3 : ℝ) ^ (-(14 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 14) (u := 54060431) (by decide) (by decide)
  have hn4 : ‖(531441 : ℂ_[3])‖ = (3 : ℝ) ^ (-(12 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 12) (u := 1) (by decide) (by decide)
  refine norm_lt_of_quartic_relation (R := (3 : ℝ) ^ (-(1 : ℝ))) (by positivity)
    ?_ ?_ ?_ ?_ hshift
  · rw [norm_neg, hn0, hn4]
    exact rpow_weight_domination (by norm_num) 4 (by norm_num)
  · rw [hn1, hn4]
    exact rpow_weight_domination (by norm_num) 3 (by norm_num)
  · rw [norm_neg, hn2, hn4]
    exact rpow_weight_domination (by norm_num) 2 (by norm_num)
  · rw [hn3, hn4]
    exact rpow_weight_domination (by norm_num) 1 (by norm_num)

/-- Every p-adic root of the explicit quartic at discriminant -68
lies strictly within the certified relative disk. -/
theorem quartic68_root_in_disk [Fact (Nat.Prime 2)] {x : ℂ_[2]}
    (hx : aeval x quartic68 = 0) :
    ‖x / (192 : ℂ_[2]) - 1‖ < (2 : ℝ) ^ (-(5/2 : ℝ)) := by
  let z := x / (192 : ℂ_[2]) - 1
  have hz : (192 : ℂ_[2]) * (1 + z) = x := by
    dsimp [z]
    field_simp
    ring
  have hx' : -(2089297506304000000000000 : ℂ_[2]) - 318507038720000000000 * x - 75843692160000000 * x ^ 2 - 178211040000 * x ^ 3 + x ^ 4 = 0 := by
    simp [quartic68, quartic68Int, sub_eq_add_neg, neg_mul, map_ofNat] at hx ⊢
    exact hx
  have hshift : (-2153248020963806364565504) + (-66748939243151494742016)*z + (-2799685941122536833024)*z^2 +
      (-1261357776047702016)*z^3 + 1358954496*z^4 = 0 := by
    rw [← hz] at hx'
    convert hx' using 1
    ring
  have hn0 : ‖(2153248020963806364565504 : ℂ_[2])‖ = (2 : ℝ) ^ (-(37 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 37) (u := 15666941333357) (by decide) (by decide)
  have hn1 : ‖(66748939243151494742016 : ℂ_[2])‖ = (2 : ℝ) ^ (-(34 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 34) (u := 3885299621799) (by decide) (by decide)
  have hn2 : ‖(2799685941122536833024 : ℂ_[2])‖ = (2 : ℝ) ^ (-(30 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 30) (u := 2607410718801) (by decide) (by decide)
  have hn3 : ‖(1261357776047702016 : ℂ_[2])‖ = (2 : ℝ) ^ (-(29 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 29) (u := 2349461943) (by decide) (by decide)
  have hn4 : ‖(1358954496 : ℂ_[2])‖ = (2 : ℝ) ^ (-(24 : ℝ)) :=
    norm_natCast_eq_rpow_of_factor (v := 24) (u := 81) (by decide) (by decide)
  refine norm_lt_of_quartic_relation (R := (2 : ℝ) ^ (-(5/2 : ℝ))) (by positivity)
    ?_ ?_ ?_ ?_ hshift
  · rw [norm_neg, hn0, hn4]
    exact rpow_weight_domination (by norm_num) 4 (by norm_num)
  · rw [norm_neg, hn1, hn4]
    exact rpow_weight_domination (by norm_num) 3 (by norm_num)
  · rw [norm_neg, hn2, hn4]
    exact rpow_weight_domination (by norm_num) 2 (by norm_num)
  · rw [norm_neg, hn3, hn4]
    exact rpow_weight_domination (by norm_num) 1 (by norm_num)

end GRHArticle.SingularModuli
