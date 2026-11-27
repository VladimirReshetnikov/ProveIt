import IPRADerivations.Geometry.DesarguesInternal
import IPRADerivations.Probability.MedianWeighted

/-!
# Absolute values of integer terms and the Runge product bound

Packet: `siegel_ipra`, `paper/03_runge.tex`, Lemma `lem:runge-product-bound`.

For an integer term `x = x⁺ − x⁻` (`ZT`), `|x| = za x = (x⁺ ∸ x⁻) + (x⁻ ∸ x⁺)`.

* `D_congr`, `D_neg`, `D_add_le`, `D_mul`: `|·|` respects integer equality, `|−x| = |x|`,
  `|x + y| ≤ |x| + |y|` and `|xy| = |x||y|` (four sign cases);
* `lem:runge-product-bound`: for integers `u, v` with `uv ≠ 0`,
  `|uv| ≥ |u|`, `|uv| ≥ |v|` (`prod_ge_left`, `prod_ge_right`), `|u| + |v| ≤ |uv| + 1` (`prod_sum_le`);
  and if `v − u = 2z` then `2|z| ≤ |u| + |v|` (`half_le`), hence `|z| ≤ |u|` or `|z| ≤ |v|`
  (`half_le_max`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.RungeProduct

open_ipra exports
open LeanProofs.IPRA.Geometry.CevaMenelaus (nz)
open LeanProofs.IPRA.Geometry.DesarguesInternal (zt_dich nz_absurd)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `|x|`. -/
abbrev za (x : ZT n) : PTm n := monus x.pos x.neg + monus x.neg x.pos

/-! ## The absolute value -/

theorem ad_of_eq_add {p q t : PTm n} (h : Γ ⊢[PRAAx] p ≐ q + t) : Γ ⊢[PRAAx] monus p q + monus q p ≐ t :=
  (congrAdd ((congrMonus h (.eqRefl q)).eqTrans (add_monus' t q)) (le_of_eq_add (d := t) h)).eqTrans (add_zero _)

theorem ad_of_eq_add' {p q t : PTm n} (h : Γ ⊢[PRAAx] q ≐ p + t) : Γ ⊢[PRAAx] monus p q + monus q p ≐ t :=
  (add_comm _ _).eqTrans (ad_of_eq_add h)

theorem D_congr₁ {x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq x y) (hl : Γ ⊢[PRAAx] le x.neg x.pos) :
    Γ ⊢[PRAAx] za x ≐ za y := by
  have h' := natEq h
  have e := eq_add_of_le hl
  have e' := natEq e
  have ey : Γ ⊢[PRAAx] y.pos ≐ y.neg + monus x.pos x.neg := by
    ipra_lc -h' + e'
  exact (ad_of_eq_add e).eqTrans (ad_of_eq_add ey).eqSymm

theorem D_congr₂ {x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq x y) (hl : Γ ⊢[PRAAx] le x.pos x.neg) :
    Γ ⊢[PRAAx] za x ≐ za y := by
  have h' := natEq h
  have e := eq_add_of_le hl
  have e' := natEq e
  have ey : Γ ⊢[PRAAx] y.neg ≐ y.pos + monus x.neg x.pos := by
    ipra_lc h' + e'
  exact (ad_of_eq_add' e).eqTrans (ad_of_eq_add' ey).eqSymm

theorem D_congr {x y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq x y) : Γ ⊢[PRAAx] za x ≐ za y :=
  .orE (le_total x.neg x.pos) (D_congr₁ h.wk Prf.hyp0) (D_congr₂ h.wk Prf.hyp0)

theorem D_neg (x : ZT n) : Γ ⊢[PRAAx] za (-x) ≐ za x := add_comm (monus x.neg x.pos) (monus x.pos x.neg)

theorem D_add_le (x y : ZT n) : Γ ⊢[PRAAx] le (za (x + y)) (za x + za y) :=
  show Γ ⊢[PRAAx] le (Probability.Variance.ad (x.pos + y.pos) (x.neg + y.neg))
    (Probability.Variance.ad x.pos x.neg + Probability.Variance.ad y.pos y.neg) from ad_add_le x.pos y.pos x.neg y.neg

section Mul

variable {u v : ZT n}

theorem D_mul₁ (h₁ : Γ ⊢[PRAAx] le u.neg u.pos) (h₂ : Γ ⊢[PRAAx] le v.neg v.pos) :
    Γ ⊢[PRAAx] za (u * v) ≐ za u * za v := by
  have e₁ := eq_add_of_le h₁; have e₂ := eq_add_of_le h₂
  have a := natEq e₁; have b := natEq e₂
  have r : Γ ⊢[PRAAx] u.pos * v.pos + u.neg * v.neg ≐
      (u.pos * v.neg + u.neg * v.pos) + monus u.pos u.neg * monus v.pos v.neg := by
    ipra_lc (𝔞 v.pos - 𝔞 v.neg) * a + 𝔞 (monus u.pos u.neg) * b
  exact (ad_of_eq_add r).eqTrans (congrMul (ad_of_eq_add e₁) (ad_of_eq_add e₂)).eqSymm

theorem D_mul₂ (h₁ : Γ ⊢[PRAAx] le u.neg u.pos) (h₂ : Γ ⊢[PRAAx] le v.pos v.neg) :
    Γ ⊢[PRAAx] za (u * v) ≐ za u * za v := by
  have e₁ := eq_add_of_le h₁; have e₂ := eq_add_of_le h₂
  have a := natEq e₁; have b := natEq e₂
  have r : Γ ⊢[PRAAx] u.pos * v.neg + u.neg * v.pos ≐
      (u.pos * v.pos + u.neg * v.neg) + monus u.pos u.neg * monus v.neg v.pos := by
    ipra_lc (𝔞 v.neg - 𝔞 v.pos) * a + 𝔞 (monus u.pos u.neg) * b
  exact (ad_of_eq_add' r).eqTrans (congrMul (ad_of_eq_add e₁) (ad_of_eq_add' e₂)).eqSymm

theorem D_mul₃ (h₁ : Γ ⊢[PRAAx] le u.pos u.neg) (h₂ : Γ ⊢[PRAAx] le v.neg v.pos) :
    Γ ⊢[PRAAx] za (u * v) ≐ za u * za v := by
  have e₁ := eq_add_of_le h₁; have e₂ := eq_add_of_le h₂
  have a := natEq e₁; have b := natEq e₂
  have r : Γ ⊢[PRAAx] u.pos * v.neg + u.neg * v.pos ≐
      (u.pos * v.pos + u.neg * v.neg) + monus u.neg u.pos * monus v.pos v.neg := by
    ipra_lc (𝔞 v.pos - 𝔞 v.neg) * a + 𝔞 (monus u.neg u.pos) * b
  exact (ad_of_eq_add' r).eqTrans (congrMul (ad_of_eq_add' e₁) (ad_of_eq_add e₂)).eqSymm

theorem D_mul₄ (h₁ : Γ ⊢[PRAAx] le u.pos u.neg) (h₂ : Γ ⊢[PRAAx] le v.pos v.neg) :
    Γ ⊢[PRAAx] za (u * v) ≐ za u * za v := by
  have e₁ := eq_add_of_le h₁; have e₂ := eq_add_of_le h₂
  have a := natEq e₁; have b := natEq e₂
  have r : Γ ⊢[PRAAx] u.pos * v.pos + u.neg * v.neg ≐
      (u.pos * v.neg + u.neg * v.pos) + monus u.neg u.pos * monus v.neg v.pos := by
    ipra_lc (𝔞 v.neg - 𝔞 v.pos) * a + 𝔞 (monus u.neg u.pos) * b
  exact (ad_of_eq_add r).eqTrans (congrMul (ad_of_eq_add' e₁) (ad_of_eq_add' e₂)).eqSymm

/-- `|uv| = |u| |v|`. -/
theorem D_mul (u v : ZT n) : Γ ⊢[PRAAx] za (u * v) ≐ za u * za v :=
  .orE (le_total u.neg u.pos)
    (.orE (le_total v.neg v.pos) (D_mul₁ Prf.hyp1 Prf.hyp0) (D_mul₂ Prf.hyp1 Prf.hyp0))
    (.orE (le_total v.neg v.pos) (D_mul₃ Prf.hyp1 Prf.hyp0) (D_mul₄ Prf.hyp1 Prf.hyp0))

end Mul

theorem D_two : Γ ⊢[PRAAx] za (ZT.natLit 2 : ZT n) ≐ two := by
  show Γ ⊢[PRAAx] monus (num 2) zero + monus zero (num 2) ≐ two
  exact (congrAdd (monus_zero _) (zero_monus _)).eqTrans ((add_zero _).eqTrans (by ipra_ring))

theorem nat_ge {U V W : PTm n} (hm : Γ ⊢[PRAAx] W ≐ U * V) (hv : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx] le U W := by
  have m := natEq hm; have e := natEq (eq_add_of_le hv)
  refine le_of_eq_add (d := U * monus V one) ?_
  ipra_lc m + 𝔞 U * e

theorem nat_sum {U V W : PTm n} (hm : Γ ⊢[PRAAx] W ≐ U * V) (hu : Γ ⊢[PRAAx] le one U) (hv : Γ ⊢[PRAAx] le one V) :
    Γ ⊢[PRAAx] le (U + V) (W + one) := by
  have m := natEq hm; have a := natEq (eq_add_of_le hu); have b := natEq (eq_add_of_le hv)
  refine le_of_eq_add (d := monus U one * monus V one) ?_
  ipra_lc m + 𝔞 (monus U one) * b + (𝔞 V - 1) * a

/-! ## `lem:runge-product-bound` -/

section Product

variable {u v : ZT n} (h : Γ ⊢[PRAAx] nz (u * v))
include h

theorem one_le_D_right : Γ ⊢[PRAAx] le one (za v) := by
  refine .orE (zt_dich v) Prf.hyp0 ?_
  exact nz_absurd _ h.wk ((D_mul u v).eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

theorem one_le_D_left : Γ ⊢[PRAAx] le one (za u) := by
  refine .orE (zt_dich u) Prf.hyp0 ?_
  exact nz_absurd _ h.wk ((D_mul u v).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))

/-- `|uv| ≥ |u|`. -/
theorem prod_ge_left : Γ ⊢[PRAAx] le (za u) (za (u * v)) := nat_ge (D_mul u v) (one_le_D_right h)

/-- `|uv| ≥ |v|`. -/
theorem prod_ge_right : Γ ⊢[PRAAx] le (za v) (za (u * v)) :=
  nat_ge ((D_mul u v).eqTrans (mul_comm _ _)) (one_le_D_left h)

/-- `|u| + |v| ≤ |uv| + 1`, from `(|u| − 1)(|v| − 1) ≥ 0`. -/
theorem prod_sum_le : Γ ⊢[PRAAx] le (za u + za v) (za (u * v) + one) :=
  nat_sum (D_mul u v) (one_le_D_left h) (one_le_D_right h)

end Product

/-- If `v − u = 2z` then `2|z| ≤ |u| + |v|`. -/
theorem half_le {u v z : ZT n} (hz : Γ ⊢[PRAAx] ZT.eq (v - u) (ZT.natLit 2 * z)) :
    Γ ⊢[PRAAx] le (two * za z) (za u + za v) := by
  have e : Γ ⊢[PRAAx] za (v - u) ≐ two * za z :=
    (D_congr hz).eqTrans ((D_mul _ _).eqTrans (congrMul D_two (.eqRefl _)))
  have t := D_add_le (Γ := Γ) v (-u)
  exact le_congr e (by have a := natEq (D_neg (Γ := Γ) u); apply deriveNat; ipra_simps; linear_combination a)
    (show Γ ⊢[PRAAx] le (za (v - u)) (za v + za (-u)) from t)

/-- Hence `max(|u|, |v|) ≥ |z|`. -/
theorem half_le_max {u v z : ZT n} (hz : Γ ⊢[PRAAx] ZT.eq (v - u) (ZT.natLit 2 * z)) :
    Γ ⊢[PRAAx] le (za z) (za u) ⋎ le (za z) (za v) := by
  have hl := half_le hz
  refine .orE (le_total (za u) (za v)) (.orI₂ ?_) (.orI₁ ?_)
  · refine mul_le_cancel (d' := one) (le_trans hl.wk ?_)
    exact le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ Prf.hyp0 (le_refl _))
  · refine mul_le_cancel (d' := one) (le_trans hl.wk ?_)
    exact le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_refl _) Prf.hyp0)

end LeanProofs.IPRA.DiophantineNumberTheory.RungeProduct

export_ipra DiophantineNumberTheory.RungeProduct (D_congr D_mul)
