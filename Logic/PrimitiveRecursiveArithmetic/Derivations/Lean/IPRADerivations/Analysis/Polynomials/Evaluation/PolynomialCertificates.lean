import IPRADerivations.Analysis.Inequalities.Contraction.FeedbackInexact

/-!
# Monomial difference bounds, the a posteriori estimate and parameter stability

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/04_polynomial.tex`, "A certified
compiler for polynomial implicit equations":

* `pow_ad` (`lem:monomial`, one variable: "`|s^m − t^m| ≤ m R^{m−1} |s − t|`"), for natural terms
  `s, t ≤ R` (a nonnegative box): `|s^{k+1} − t^{k+1}| ≤ (k+1) R^k |s − t|`;
* `mono_ad` (`lem:monomial`: "replace the factors one at a time … Summing the resulting `d` inequalities"): for a
  list of factors `(x_j, y_j, R_j, α_j)` with `x_j, y_j ≤ R_j`, `|∏ x_j^{α_j} − ∏ y_j^{α_j}| ≤ bnd`, where `bnd`
  is `∑_j D_{α,j}(R) |x_j − y_j|` written by the same telescoping (`D_{α,j} = α_j R_j^{α_j−1} ∏_{k≠j} R_k^{α_k}`,
  with the factors after `j` bounded by their radii and those before `j` kept as radii powers);
* `apost`, `apost_closed` (`prop:polyapost`, "Residual controls distance"): for a point `z` of the domain with
  `|z_k − c_k| ≤ r w_k` and fixed-point residual `|z_i − T_i z| ≤ η w_i`,
  `2ⁿ |z_i − h_{n,i}| + 2 η w_i ≤ (r + 2^{n+1} η) w_i`, i.e. `|z − h_n| ≤ r 2^{−n} + 2η(1 − 2^{−n})`;
* `param_stability` (`eq:paramstability`): for two maps `T_a` (certified) and `T_b` with
  `|T_{b,i} x − T_{a,i} x| ≤ Lδ w_i` on the domain, the iterations from the same start satisfy
  `2ⁿ |h_n(a) − h_n(b)|_i + 2 Lδ w_i ≤ 2^{n+1} Lδ w_i`.

The last two are specializations of `Analysis/FeedbackInexact.inexact_budget`, with the closed form of the budget
for constant defects (`budget_const`).
-/

namespace LeanProofs.IPRA.Analysis.PolynomialCertificates

open_ipra
open LeanProofs.IPRA.Analysis.WeightedFeedback (Cert contract_scaled orbit orbit_dom)
open LeanProofs.IPRA.Analysis.FeedbackInexact (budget inexact_budget)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ClipLaws (ad_triangle)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul ad_le_of)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Monomial differences -/

theorem ad_congr {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

theorem ad_self (a : PTm n) : Γ ⊢[PRAAx] le (ad a a) zero :=
  ad_le_of (a := a) (b := a) (c := zero) (by ipra_le 0) (by ipra_le 0)

/-- `s^k` for a fixed exponent. -/
def mpow (s : PTm n) : ℕ → PTm n
  | 0 => one
  | k + 1 => s * mpow s k

theorem mpow_le {s R : PTm n} (h : Γ ⊢[PRAAx] le s R) : ∀ k, Γ ⊢[PRAAx] le (mpow s k) (mpow R k)
  | 0 => le_refl _
  | k + 1 => by
    have ih := mpow_le h k
    show Γ ⊢[PRAAx] le (s * mpow s k) (R * mpow R k)
    ipra_le 𝔟 R * sl ih + 𝔟 (mpow s k) * sl h

/-- Replacing one factor: `|s P − t Q| ≤ s |P − Q| + Q |s − t|`. -/
theorem ad_mul_step (s t P Q : PTm n) : Γ ⊢[PRAAx] le (ad (s * P) (t * Q)) (s * ad P Q + Q * ad s t) := by
  have tri := ad_triangle (Γ := Γ) (s * P) (s * Q) (t * Q)
  have n2 := natEq ((ad_congr (Γ := Γ) (mul_comm s Q) (mul_comm t Q)).eqTrans (ad_mul Q s t))
  ipra_le sl tri with (-1) * natEq (ad_mul (Γ := Γ) s P Q) + (-1) * n2

/-- `lem:monomial`, one variable: `|s^{k+1} − t^{k+1}| ≤ (k+1) R^k |s − t|` for `s, t ≤ R`. -/
theorem pow_ad {s t R : PTm n} (hs : Γ ⊢[PRAAx] le s R) (ht : Γ ⊢[PRAAx] le t R) :
    ∀ k, Γ ⊢[PRAAx] le (ad (mpow s (k + 1)) (mpow t (k + 1))) (num (k + 1) * mpow R k * ad s t)
  | 0 => by
    have step := ad_mul_step (Γ := Γ) s t one one
    have h11 := ad_self (Γ := Γ) (one : PTm n)
    show Γ ⊢[PRAAx] le (ad (s * one) (t * one)) (num 1 * one * ad s t)
    ipra_le sl step + 𝔟 s * sl h11
  | k + 1 => by
    have step := ad_mul_step (Γ := Γ) s t (mpow s (k + 1)) (mpow t (k + 1))
    have ih := pow_ad hs ht k
    have hm : Γ ⊢[PRAAx] le (mpow t (k + 1)) (R * mpow R k) := mpow_le ht (k + 1)
    show Γ ⊢[PRAAx] le (ad (s * mpow s (k + 1)) (t * mpow t (k + 1))) (num (k + 2) * (R * mpow R k) * ad s t)
    ipra_le sl step + 𝔟 R * sl ih + (𝔟 (monus (mpow s (k + 1)) (mpow t (k + 1))) +
      𝔟 (monus (mpow t (k + 1)) (mpow s (k + 1)))) * sl hs +
      (𝔟 (monus s t) + 𝔟 (monus t s)) * sl hm using push_cast; ring

/-- A factor `x^α` (and `y^α`) with radius `R`. -/
structure Fac (n : ℕ) where
  x : PTm n
  y : PTm n
  R : PTm n
  e : ℕ

/-- The difference coefficient of one factor: `α R^{α−1}`, or `0` for `α = 0`. -/
def dcoef (f : Fac n) : PTm n :=
  match f.e with
  | 0 => zero
  | k + 1 => num (k + 1) * mpow f.R k

def prodX : List (Fac n) → PTm n
  | [] => one
  | f :: L => mpow f.x f.e * prodX L

def prodY : List (Fac n) → PTm n
  | [] => one
  | f :: L => mpow f.y f.e * prodY L

def prodR : List (Fac n) → PTm n
  | [] => one
  | f :: L => mpow f.R f.e * prodR L

/-- `∑_j D_{α,j}(R) |x_j − y_j|`, by telescoping. -/
def bnd : List (Fac n) → PTm n
  | [] => zero
  | f :: L => dcoef f * prodR L * ad f.x f.y + mpow f.R f.e * bnd L

theorem prodY_le : (L : List (Fac n)) → (∀ f ∈ L, Γ ⊢[PRAAx] le f.y f.R) → (Γ ⊢[PRAAx] le (prodY L) (prodR L))
  | [], _ => le_refl _
  | f :: L, h => by
    have hf := mpow_le (h f List.mem_cons_self) f.e
    have ih := prodY_le L fun g hg => h g (List.mem_cons_of_mem _ hg)
    show Γ ⊢[PRAAx] le (mpow f.y f.e * prodY L) (mpow f.R f.e * prodR L)
    ipra_le 𝔟 (mpow f.R f.e) * sl ih + 𝔟 (prodY L) * sl hf

theorem fac_ad (f : Fac n) (hx : Γ ⊢[PRAAx] le f.x f.R) (hy : Γ ⊢[PRAAx] le f.y f.R) :
    Γ ⊢[PRAAx] le (ad (mpow f.x f.e) (mpow f.y f.e)) (dcoef f * ad f.x f.y) := by
  rcases f with ⟨x, y, R, e⟩
  cases e with
  | zero =>
    have h := ad_self (Γ := Γ) (one : PTm n)
    show Γ ⊢[PRAAx] le (ad one one) (zero * ad x y)
    ipra_le sl h
  | succ k =>
    have h := pow_ad hx hy k
    show Γ ⊢[PRAAx] le (ad (mpow x (k + 1)) (mpow y (k + 1))) (num (k + 1) * mpow R k * ad x y)
    exact h

/-- `lem:monomial`: `|∏ x_j^{α_j} − ∏ y_j^{α_j}| ≤ ∑_j D_{α,j}(R) |x_j − y_j|`. -/
theorem mono_ad : (L : List (Fac n)) → (∀ f ∈ L, (Γ ⊢[PRAAx] le f.x f.R) ∧ (Γ ⊢[PRAAx] le f.y f.R)) →
    (Γ ⊢[PRAAx] le (ad (prodX L) (prodY L)) (bnd L))
  | [], _ => by
    have h := ad_self (Γ := Γ) (one : PTm n)
    exact h
  | f :: L, h => by
    have hf := h f List.mem_cons_self
    have hL : ∀ g ∈ L, (Γ ⊢[PRAAx] le g.x g.R) ∧ (Γ ⊢[PRAAx] le g.y g.R) :=
      fun g hg => h g (List.mem_cons_of_mem _ hg)
    have step := ad_mul_step (Γ := Γ) (mpow f.x f.e) (mpow f.y f.e) (prodX L) (prodY L)
    have ih := mono_ad L hL
    have hxe := mpow_le hf.1 f.e
    have hpow := fac_ad f hf.1 hf.2
    have hPY := prodY_le L fun g hg => (hL g hg).2
    show Γ ⊢[PRAAx] le (ad (mpow f.x f.e * prodX L) (mpow f.y f.e * prodY L))
      (dcoef f * prodR L * ad f.x f.y + mpow f.R f.e * bnd L)
    ipra_le sl step + 𝔟 (mpow f.x f.e) * sl ih + 𝔟 (bnd L) * sl hxe + 𝔟 (prodY L) * sl hpow +
      𝔟 (dcoef f) * (𝔟 (monus f.x f.y) + 𝔟 (monus f.y f.x)) * sl hPY

/-! ## The a posteriori estimate and parameter stability -/

/-- The budget for constant defects: `budget + 2 (e₁ + e₂) = E₀ + 2^{k+1} (e₁ + e₂)`. -/
theorem budget_const (E₀ e₁ e₂ : PTm n) :
    ∀ k, Γ ⊢[PRAAx] budget E₀ (fun _ => e₁) (fun _ => e₂) k + num 2 * (e₁ + e₂) ≐ E₀ + num (2 ^ (k + 1)) * (e₁ + e₂)
  | 0 => .eqRefl _
  | k + 1 => by
    show Γ ⊢[PRAAx] (budget E₀ (fun _ => e₁) (fun _ => e₂) k + num (2 ^ (k + 1)) * (e₁ + e₂)) + num 2 * (e₁ + e₂) ≐
      E₀ + num (2 ^ (k + 1 + 1)) * (e₁ + e₂)
    ipra_lc natEq (budget_const E₀ e₁ e₂ k)

variable {a : Fin m → Fin m → PTm n} {w : Fin m → PTm n} {T : (Fin m → PTm n) → Fin m → PTm n}
  {D : (Fin m → PTm n) → Prop}

/-- `prop:polyapost`: `2ⁿ |z_i − h_{n,i}| ≤ budget w_i` for the orbit `h` from `c`. -/
theorem apost (C : Cert Γ a w T D) {c z : Fin m → PTm n} (hc : D c) (hz : D z) {r η : PTm n}
    (hz0 : ∀ k, Γ ⊢[PRAAx] le (ad (z k) (c k)) (r * w k))
    (hη : ∀ i, Γ ⊢[PRAAx] le (ad (z i) (T z i)) (η * w i)) (k : ℕ) (i : Fin m) :
    Γ ⊢[PRAAx] le (num (2 ^ k) * ad (z i) (orbit T c k i)) (budget r (fun _ => η) (fun _ => zero) k * w i) :=
  inexact_budget C (u := fun _ => z) (v := orbit T c) (fun _ => hz) (orbit_dom C hc) hz0
    (fun _ i => hη i)
    (fun j i => by
      have h := ad_self (Γ := Γ) (T (orbit T c j) i)
      show Γ ⊢[PRAAx] le (ad (T (orbit T c j) i) (T (orbit T c j) i)) (zero * w i)
      ipra_le sl h) k i

/-- `prop:polyapost`, closed form: `2ⁿ |z_i − h_{n,i}| + 2 η w_i ≤ (r + 2^{n+1} η) w_i`. -/
theorem apost_closed (C : Cert Γ a w T D) {c z : Fin m → PTm n} (hc : D c) (hz : D z) {r η : PTm n}
    (hz0 : ∀ k, Γ ⊢[PRAAx] le (ad (z k) (c k)) (r * w k))
    (hη : ∀ i, Γ ⊢[PRAAx] le (ad (z i) (T z i)) (η * w i)) (k : ℕ) (i : Fin m) :
    Γ ⊢[PRAAx] le (num (2 ^ k) * ad (z i) (orbit T c k i) + num 2 * (η * w i)) ((r + num (2 ^ (k + 1)) * η) * w i) := by
  have h := apost C hc hz hz0 hη k i
  ipra_le sl h with (-𝔟 (w i)) * natEq (budget_const (Γ := Γ) r η zero k)

/-- `eq:paramstability`: `2ⁿ |h_n(a) − h_n(b)|_i + 2 Lδ w_i ≤ 2^{n+1} Lδ w_i`. -/
theorem param_stability (C : Cert Γ a w T D) {Tb : (Fin m → PTm n) → Fin m → PTm n}
    (hDb : ∀ x, D x → D (Tb x)) {c : Fin m → PTm n} (hc : D c) {Ld : PTm n}
    (hab : ∀ x, D x → ∀ i, Γ ⊢[PRAAx] le (ad (Tb x i) (T x i)) (Ld * w i)) (k : ℕ) (i : Fin m) :
    Γ ⊢[PRAAx] le (num (2 ^ k) * ad (orbit T c k i) (orbit Tb c k i) + num 2 * (Ld * w i))
      (num (2 ^ (k + 1)) * Ld * w i) := by
  have hvb : ∀ j, D (orbit Tb c j) := fun j => by
    induction j with
    | zero => exact hc
    | succ j ih => exact hDb _ ih
  have h := inexact_budget C (u := orbit T c) (v := orbit Tb c) (E₀ := zero) (ε := fun _ => zero)
    (η := fun _ => Ld) (orbit_dom C hc) hvb
    (fun q => by
      have h := ad_self (Γ := Γ) (c q)
      show Γ ⊢[PRAAx] le (ad (c q) (c q)) (zero * w q)
      ipra_le sl h)
    (fun j i => by
      have h := ad_self (Γ := Γ) (T (orbit T c j) i)
      show Γ ⊢[PRAAx] le (ad (T (orbit T c j) i) (T (orbit T c j) i)) (zero * w i)
      ipra_le sl h)
    (fun j i => hab _ (hvb j) i) k i
  ipra_le sl h with (-𝔟 (w i)) * natEq (budget_const (Γ := Γ) zero zero Ld k)

end LeanProofs.IPRA.Analysis.PolynomialCertificates
