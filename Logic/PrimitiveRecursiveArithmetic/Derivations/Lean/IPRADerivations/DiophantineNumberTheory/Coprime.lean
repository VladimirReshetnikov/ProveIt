import IPRADerivations.Foundations.ChineseRemainder

/-!
# Coprimality

The integer tools of `flt_ipra` (Lemma `lem:integer-tools`) that the descent proofs use:

* `gauss`: `gcd(m, a) = 1 → m ∣ a y → m ∣ y`;
* `coprime_dvd_left`, `coprime_mul`: coprimality passes to divisors and to products;
* `square_of_coprime`: if `a b = c²` with `gcd(a, b) = 1` and `a ≥ 1`, then
  `a = gcd(a, c)²`.

The square lemma avoids factorization. With `u = gcd(a, c)`, `a = u a₁`, `c = u c₁`, one has
`gcd(a₁, c₁) = 1` and `a₁ b = u c₁²`. Gauss's lemma then gives `a₁ ∣ u` (as `a₁` is prime to
`c₁²`) and `u ∣ a₁` (as `u ∣ a` is prime to `b`), so `u = a₁`.

Divisors are arbitrary positive terms `d` (with `d = S (pred d)`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.Coprime

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Divisibility by positive terms -/

theorem dvd_of_eq' {d x w : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] x ≐ d * w) :
    Γ ⊢[PRAAx] dvd d x :=
  dvd_congr_left hd.eqSymm (dvd_of_eq (h.eqTrans (congrMul hd (.eqRefl _))))

theorem eq_of_dvd' {d x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] dvd d x) :
    Γ ⊢[PRAAx] x ≐ d * quo x d :=
  (eq_of_dvd (dvd_congr_left hd h)).eqTrans (congrMul hd.eqSymm (congrAp2 quoF (.eqRefl _) hd.eqSymm))

theorem dvd_le' {d x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] dvd d x)
    (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) : Γ ⊢[PRAAx] le d x :=
  le_congr hd.eqSymm (.eqRefl _) (dvd_le (dvd_congr_left hd h) hx)

theorem gcd_greatest' {a b d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (ha : Γ ⊢[PRAAx] dvd d a)
    (hb : Γ ⊢[PRAAx] dvd d b) : Γ ⊢[PRAAx] dvd d (gcd a b) :=
  dvd_congr_left hd.eqSymm (gcd_greatest_at (dvd_congr_left hd ha) (dvd_congr_left hd hb))

theorem gcd_dvd' {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] dvd (gcd a b) a ⋏ dvd (gcd a b) b := gcd_dvd_at (gcd_pos ha)

theorem dvd_trans' {d e z : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (h₁ : Γ ⊢[PRAAx] dvd d e) (h₂ : Γ ⊢[PRAAx] dvd e z) : Γ ⊢[PRAAx] dvd d z := by
  refine dvd_of_eq' hd (w := quo e d * quo z e) ?_
  have e₁ := natEq (eq_of_dvd' hd h₁); have e₂ := natEq (eq_of_dvd' he h₂)
  apply deriveNat; ipra_simps
  linear_combination e₂ + Groth.ι (IPRA.Q.mk Γ (quo z e)) * e₁

theorem one_le_of_pos {e : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) : Γ ⊢[PRAAx] le one e :=
  le_of_eq_add (d := pred e) (he.eqTrans (by apply deriveNat; ipra_simps; ring))

theorem eq_one_of_dvd_one {e : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] dvd e one) :
    Γ ⊢[PRAAx] e ≐ one :=
  le_antisymm (dvd_le' he h (congrSucc (pred_succ zero).eqSymm)) (one_le_of_pos he)

/-! ## Gauss's lemma -/

/-- `gcd(m, a) = 1 → m ∣ a y → m ∣ y`. -/
theorem gauss {m a y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hg : Γ ⊢[PRAAx] gcd m a ≐ one)
    (h : Γ ⊢[PRAAx] dvd m (a * y)) : Γ ⊢[PRAAx] dvd m y := by
  have w := eq_of_dvd (dvd_congr_left hm h)
  refine dvd_congr_left hm.eqSymm ?_
  refine .orE (bezout_at m a) ?_ ?_
  · exact dvd_sub (dvd_of_eq (euclid_alg₁ Prf.hyp0 hg.wk w.wk hm.wk)) (dvd_of_eq (.eqRefl _))
  · exact dvd_sub (dvd_of_eq (euclid_alg₂ Prf.hyp0 hg.wk w.wk hm.wk)) (dvd_of_eq (.eqRefl _))

/-! ## Coprimality of divisors and products -/

theorem coprime_dvd_left {u a b : PTm n} (hu : Γ ⊢[PRAAx] u ≐ succ (pred u)) (hua : Γ ⊢[PRAAx] dvd u a)
    (h : Γ ⊢[PRAAx] gcd a b ≐ one) : Γ ⊢[PRAAx] gcd u b ≐ one := by
  have hd := gcd_pos (B := b) hu
  have hdd := gcd_dvd' (b := b) hu
  exact eq_one_of_dvd_one hd (dvd_congr h (gcd_greatest' hd (dvd_trans' hd hu (Prf.andE₁ hdd) hua)
    (Prf.andE₂ hdd)))

theorem coprime_mul {a c c' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (h₁ : Γ ⊢[PRAAx] gcd a c ≐ one)
    (h₂ : Γ ⊢[PRAAx] gcd a c' ≐ one) : Γ ⊢[PRAAx] gcd a (c * c') ≐ one := by
  have hd := gcd_pos (B := c * c') ha
  have hdd := gcd_dvd' (b := c * c') ha
  have hdc := coprime_dvd_left hd (Prf.andE₁ hdd) h₁
  have hdc' := gauss hd hdc (Prf.andE₂ hdd)
  exact eq_one_of_dvd_one hd (dvd_congr h₂ (gcd_greatest' hd (Prf.andE₁ hdd) hdc'))

/-! ## Coprime factors of a square -/

theorem square_alg₁ {a a₁ u e t : PTm n} (eA : Γ ⊢[PRAAx] a ≐ u * a₁) (e₁ : Γ ⊢[PRAAx] a₁ ≐ e * t) :
    Γ ⊢[PRAAx] a ≐ (u * e) * t := by
  have h₁ := natEq eA; have h₂ := natEq e₁
  apply deriveNat; ipra_simps
  linear_combination h₁ + Groth.ι (IPRA.Q.mk Γ u) * h₂

theorem square_alg₂ {a b c a₁ c₁ u : PTm n} (h : Γ ⊢[PRAAx] a * b ≐ c * c) (eA : Γ ⊢[PRAAx] a ≐ u * a₁)
    (eC : Γ ⊢[PRAAx] c ≐ u * c₁) : Γ ⊢[PRAAx] u * (a₁ * b) ≐ u * (u * (c₁ * c₁)) := by
  have h₁ := natEq h; have h₂ := natEq eA; have h₃ := natEq eC
  apply deriveNat; ipra_simps
  linear_combination h₁ - Groth.ι (IPRA.Q.mk Γ b) * h₂ +
    (Groth.ι (IPRA.Q.mk Γ c) + Groth.ι (IPRA.Q.mk Γ u) * Groth.ι (IPRA.Q.mk Γ c₁)) * h₃

/-- `a b = c²`, `gcd(a, b) = 1`, `a ≥ 1` give `a = gcd(a, c)²`. -/
theorem square_of_coprime {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hg : Γ ⊢[PRAAx] gcd a b ≐ one) (h : Γ ⊢[PRAAx] a * b ≐ c * c) :
    Γ ⊢[PRAAx] a ≐ gcd a c * gcd a c := by
  have hu := gcd_pos (B := c) ha
  have hud := gcd_dvd' (b := c) ha
  have eA := eq_of_dvd' hu (Prf.andE₁ hud)
  have eC := eq_of_dvd' hu (Prf.andE₂ hud)
  -- `a₁ = a / u ≥ 1`.
  have ha₁ : Γ ⊢[PRAAx] quo a (gcd a c) ≐ succ (pred (quo a (gcd a c))) := by
    refine .orE (zero_or_succ (quo a (gcd a c))) ?_ Prf.hyp0
    exact succ_ne_zero' _ (ha.wk.eqSymm.eqTrans (eA.wk.eqTrans
      ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))
  -- `gcd(a₁, c₁) = 1`: `u e` divides `a` and `c`, hence `u`, so `e ≤ 1`.
  have he := gcd_pos (B := quo c (gcd a c)) ha₁
  have hed := gcd_dvd' (b := quo c (gcd a c)) ha₁
  have hue := pos_mul hu he
  have hueA := dvd_of_eq' hue (square_alg₁ eA (eq_of_dvd' he (Prf.andE₁ hed)))
  have hueC := dvd_of_eq' hue (square_alg₁ eC (eq_of_dvd' he (Prf.andE₂ hed)))
  have hle := dvd_le' hue (gcd_greatest' hue hueA hueC) hu
  have hle' : Γ ⊢[PRAAx] le (succ (pred (gcd a c)) * gcd (quo a (gcd a c)) (quo c (gcd a c)))
      (succ (pred (gcd a c)) * one) :=
    le_congr (congrMul hu (.eqRefl _)) ((mul_comm _ _).eqTrans (one_mul _) |>.eqSymm.eqTrans
      (congrMul hu (.eqRefl _))) hle
  have he1 := le_antisymm (mul_le_cancel hle') (one_le_of_pos he)
  -- `a₁` is prime to `c₁²`, and `a₁ b = u c₁²`.
  have hcc := coprime_mul ha₁ he1 he1
  have eB := mul_cancel hu (square_alg₂ h eA eC)
  have d₁ : Γ ⊢[PRAAx] dvd (quo a (gcd a c)) ((quo c (gcd a c) * quo c (gcd a c)) * gcd a c) :=
    dvd_of_eq' ha₁ (w := b) ((mul_comm _ _).eqTrans eB.eqSymm)
  have a₁u := gauss ha₁ hcc d₁
  have hub := coprime_dvd_left hu (Prf.andE₁ hud) hg
  have d₂ : Γ ⊢[PRAAx] dvd (gcd a c) (b * quo a (gcd a c)) := dvd_of_eq' hu ((mul_comm _ _).eqTrans eB)
  have ua₁ := gauss hu hub d₂
  have eq := le_antisymm (dvd_le' hu ua₁ ha₁) (dvd_le' ha₁ a₁u hu)
  exact eA.eqTrans (congrMul (.eqRefl _) eq.eqSymm)

/-! ## Closed statements -/

/-- Gauss's lemma; variables `0 = m - 1`, `1 = a`, `2 = y`. -/
abbrev gaussFormula : Fm PTm 3 :=
  gcd (succ (var 0)) (var 1) ≐ one ⟶ dvd (succ (var 0)) (var 1 * var 2) ⟶ dvd (succ (var 0)) (var 2)

theorem gauss_lemma : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 gaussFormula :=
  closeUniv 3 (.impI (.impI (gauss (congrSucc (pred_succ _).eqSymm) Prf.hyp1 Prf.hyp0)))

/-- Coprime factors of a square; variables `0 = a - 1`, `1 = b`, `2 = c`. -/
abbrev squareFormula : Fm PTm 3 :=
  gcd (succ (var 0)) (var 1) ≐ one ⟶ succ (var 0) * var 1 ≐ var 2 * var 2 ⟶
    succ (var 0) ≐ gcd (succ (var 0)) (var 2) * gcd (succ (var 0)) (var 2)

theorem coprime_square : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 squareFormula :=
  closeUniv 3 (.impI (.impI (square_of_coprime (congrSucc (pred_succ _).eqSymm) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.Coprime
