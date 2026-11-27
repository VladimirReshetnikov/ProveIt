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

namespace LeanProofs.IPRA.DiophantineNumberTheory.Coprime

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)

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
  ipra_lc natEq (eq_of_dvd' he h₂) + Groth.ι (IPRA.Q.mk Γ (quo z e)) * natEq (eq_of_dvd' hd h₁)

alias one_le_of_pos := Common.one_le_of_pos

theorem eq_one_of_dvd_one {e : PTm n} (he : Γ ⊢[PRAAx] e ≐ succ (pred e)) (h : Γ ⊢[PRAAx] dvd e one) :
    Γ ⊢[PRAAx] e ≐ one :=
  le_antisymm (dvd_le' he h (congrSucc (pred_succ zero).eqSymm)) (one_le_of_pos he)

theorem dvd_self' {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) : Γ ⊢[PRAAx] dvd d d :=
  dvd_of_eq' hd (w := one) ((mul_comm _ _).eqTrans (one_mul _)).eqSymm

theorem dvd_add' {d x y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hx : Γ ⊢[PRAAx] dvd d x)
    (hy : Γ ⊢[PRAAx] dvd d y) : Γ ⊢[PRAAx] dvd d (x + y) :=
  dvd_congr_left hd.eqSymm (dvd_add (dvd_congr_left hd hx) (dvd_congr_left hd hy))

theorem dvd_sub' {d x y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hxy : Γ ⊢[PRAAx] dvd d (x + y))
    (hy : Γ ⊢[PRAAx] dvd d y) : Γ ⊢[PRAAx] dvd d x :=
  dvd_congr_left hd.eqSymm (dvd_sub (dvd_congr_left hd hxy) (dvd_congr_left hd hy))

theorem dvd_mul' {d x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (c : PTm n) (hx : Γ ⊢[PRAAx] dvd d x) :
    Γ ⊢[PRAAx] dvd d (x * c) :=
  dvd_congr_left hd.eqSymm (dvd_mul c (dvd_congr_left hd hx))

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

/-- `gcd(d, y) = 1` and `d ∣ y` give `d = 1`. -/
theorem eq_one_of_coprime_dvd {d y : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hg : Γ ⊢[PRAAx] gcd d y ≐ one) (hy : Γ ⊢[PRAAx] dvd d y) : Γ ⊢[PRAAx] d ≐ one :=
  eq_one_of_dvd_one hd (dvd_congr hg (gcd_greatest' hd (dvd_self' hd) hy))

/-! ## Squares and quotients by the gcd -/

/-- `x² ≤ y² → x ≤ y`. -/
alias le_of_sq_le := Common.le_of_sq_le

/-- `x² = y² → x = y`. -/
theorem sq_inj {x y : PTm n} (h : Γ ⊢[PRAAx] x * x ≐ y * y) : Γ ⊢[PRAAx] x ≐ y :=
  le_antisymm (le_of_sq_le (le_congr (.eqRefl _) h (le_refl _)))
    (le_of_sq_le (le_congr (.eqRefl _) h.eqSymm (le_refl _)))

theorem gcd_comm_one {a b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (h : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ ⊢[PRAAx] gcd b a ≐ one := by
  have hd := gcd_pos (B := a) hb
  have hdd := gcd_dvd' (b := a) hb
  exact eq_one_of_dvd_one hd (dvd_congr h (gcd_greatest' hd (Prf.andE₂ hdd) (Prf.andE₁ hdd)))

/-- A factor of a positive number is positive. -/
theorem pos_of_eq_mul {x e q : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (h : Γ ⊢[PRAAx] x ≐ e * q) :
    Γ ⊢[PRAAx] q ≐ succ (pred q) := by
  refine .orE (zero_or_succ q) ?_ Prf.hyp0
  exact succ_ne_zero' _ (hx.wk.eqSymm.eqTrans (h.wk.eqTrans
    ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))))

theorem square_alg₁ {a a₁ u e t : PTm n} (eA : Γ ⊢[PRAAx] a ≐ u * a₁) (e₁ : Γ ⊢[PRAAx] a₁ ≐ e * t) :
    Γ ⊢[PRAAx] a ≐ (u * e) * t := by
  ipra_lc natEq eA + Groth.ι (IPRA.Q.mk Γ u) * natEq e₁

/-- `gcd(a / g, c / g) = 1` for `g = gcd(a, c)`, `a ≥ 1`. -/
theorem coprime_quotients {a c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] gcd (quo a (gcd a c)) (quo c (gcd a c)) ≐ one := by
  have hu := gcd_pos (B := c) ha
  have hud := gcd_dvd' (b := c) ha
  have eA := eq_of_dvd' hu (Prf.andE₁ hud)
  have eC := eq_of_dvd' hu (Prf.andE₂ hud)
  have ha₁ := pos_of_eq_mul ha eA
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
  exact le_antisymm (mul_le_cancel hle') (one_le_of_pos he)

/-! ## Coprime factors of a square -/

theorem square_alg₂ {a b c a₁ c₁ u : PTm n} (h : Γ ⊢[PRAAx] a * b ≐ c * c) (eA : Γ ⊢[PRAAx] a ≐ u * a₁)
    (eC : Γ ⊢[PRAAx] c ≐ u * c₁) : Γ ⊢[PRAAx] u * (a₁ * b) ≐ u * (u * (c₁ * c₁)) := by
  ipra_lc natEq h - Groth.ι (IPRA.Q.mk Γ b) * natEq eA +
    (Groth.ι (IPRA.Q.mk Γ c) + Groth.ι (IPRA.Q.mk Γ u) * Groth.ι (IPRA.Q.mk Γ c₁)) * natEq eC

/-- `a b = c²`, `gcd(a, b) = 1`, `a ≥ 1` give `a = gcd(a, c)²`. -/
theorem square_of_coprime {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hg : Γ ⊢[PRAAx] gcd a b ≐ one) (h : Γ ⊢[PRAAx] a * b ≐ c * c) :
    Γ ⊢[PRAAx] a ≐ gcd a c * gcd a c := by
  have hu := gcd_pos (B := c) ha
  have hud := gcd_dvd' (b := c) ha
  have eA := eq_of_dvd' hu (Prf.andE₁ hud)
  have eC := eq_of_dvd' hu (Prf.andE₂ hud)
  have ha₁ := pos_of_eq_mul ha eA
  have he1 := coprime_quotients (c := c) ha
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

/-- `d² ∣ z² → d ∣ z` for `d, z ≥ 1`. -/
theorem dvd_of_sq_dvd_sq {d z : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hz : Γ ⊢[PRAAx] z ≐ succ (pred z))
    (h : Γ ⊢[PRAAx] dvd (d * d) (z * z)) : Γ ⊢[PRAAx] dvd d z := by
  have he := gcd_pos (B := z) hd
  have hed := gcd_dvd' (b := z) hd
  have eD := eq_of_dvd' he (Prf.andE₁ hed)
  have eZ := eq_of_dvd' he (Prf.andE₂ hed)
  have hd₁ := pos_of_eq_mul hd eD
  have hz₁ := pos_of_eq_mul hz eZ
  have hcop := coprime_quotients (c := z) hd
  have ew := eq_of_dvd' (pos_mul hd hd) h
  -- `z₁² = d₁² w` after cancelling `g²`.
  have e₁ : Γ ⊢[PRAAx] (gcd d z * gcd d z) * (quo z (gcd d z) * quo z (gcd d z) * one) ≐
      (gcd d z * gcd d z) * (quo d (gcd d z) * quo d (gcd d z) * quo (z * z) (d * d)) := by
    ipra_lc natEq ew -
      (Groth.ι (IPRA.Q.mk Γ z) + Groth.ι (IPRA.Q.mk Γ (gcd d z)) * Groth.ι (IPRA.Q.mk Γ (quo z (gcd d z)))) * natEq eZ +
      (Groth.ι (IPRA.Q.mk Γ d) + Groth.ι (IPRA.Q.mk Γ (gcd d z)) * Groth.ι (IPRA.Q.mk Γ (quo d (gcd d z)))) * Groth.ι (IPRA.Q.mk Γ (quo (z * z) (d * d))) * natEq eD
  have e₂ := mul_cancel (pos_mul he he) e₁
  have hzz := pos_mul hz₁ hz₁
  have hdd := pos_mul hd₁ hd₁
  have c₁ := coprime_mul hd₁ hcop hcop
  have c₂ := gcd_comm_one hzz c₁
  have c₃ := coprime_mul hzz c₂ c₂
  have c₄ := gcd_comm_one hdd c₃
  have h1 := gauss hdd c₄ (dvd_of_eq' hdd e₂)
  have d₁1 := sq_inj ((eq_one_of_dvd_one hdd h1).eqTrans ((mul_comm _ _).eqTrans (one_mul _)).eqSymm)
  have ed : Γ ⊢[PRAAx] gcd d z ≐ d :=
    ((mul_comm _ _).eqTrans (one_mul _)).eqSymm.eqTrans ((congrMul (.eqRefl _) d₁1.eqSymm).eqTrans eD.eqSymm)
  exact dvd_congr_left ed (Prf.andE₂ hed)

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

export_ipra DiophantineNumberTheory.Coprime (coprime_dvd_left coprime_mul coprime_quotients dvd_add' dvd_le' dvd_mul'
  dvd_of_eq' dvd_self' dvd_sub' dvd_trans' eq_of_dvd' eq_one_of_dvd_one gauss gcd_comm_one gcd_dvd' gcd_greatest'
  pos_of_eq_mul)
