import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Parity
import IPRADerivations.Core.Tactic

/-!
# Basic lemmas used throughout

Small facts about positivity, the order, truncated subtraction, the equality test, the signum and powers that
many modules need. They used to be restated, under various names, in each module that needed them; they are
proved once here, in the namespace `LeanProofs.IPRA.Common`, and the module-local names are aliases.

* semiring: `mul_one_right`, `mul_one_right'`, `two_mul_succ`;
* positivity (`a = succ (pred a)`, equivalently `1 ≤ a`): `succ_pos`, `pos_of_succ`, `pos_of_one_le`, `one_le_of_pos`,
  `one_le_succ`, `pos_mul`, `pos_of_two_le`;
* order: `le_of_eq_zero`, `succ_le_succ`, `le_of_lt_succ`, `lt_succ_of_le`, `ne_of_lt`, `pred_lt`, `add_le_add`,
  `mul_le_mul`, cancellation `mul_cancel_le`, `mul_cancel_eq`, `two_mul_cancel`, and `le_of_sq_le`, `lt_of_sq_lt`;
* truncated subtraction: `monus_le_self`, `monus_of_eq`, `monus_succ_of_le`, `monus_monus_of_le`,
  `add_eq_zero_left`, `add_eq_zero_right`, `monus_one_of_zero`;
* congruences: `congrPairT`, `congrEqb`, `congrSg`;
* the equality test and the signum: `eqb_zero_or_one`, `eqb_le_one`, `eq_of_eqb`, `sg_le_one`,
  `sg_zero_or_one`, `sg_of_one_le`;
* powers: `pw_one`, `pw_two`, `pw_double`.
-/

namespace LeanProofs.IPRA.Common

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Semiring -/

theorem mul_one_right (a : PTm n) : Γ ⊢[PRAAx] a * one ≐ a := by ipra_ring

theorem mul_one_right' (a : PTm n) : Γ ⊢[PRAAx] a ≐ a * one := by ipra_ring

theorem two_mul_succ (a : PTm n) : Γ ⊢[PRAAx] two * succ a ≐ succ (succ (two * a)) := by ipra_ring

/-! ## Positivity -/

theorem succ_pos (a : PTm n) : Γ ⊢[PRAAx] succ a ≐ succ (pred (succ a)) := congrSucc (pred_succ _).eqSymm

theorem pos_of_succ {a c : PTm n} (h : Γ ⊢[PRAAx] a ≐ succ c) : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
  h.eqTrans (congrSucc ((congrPred h).eqTrans (pred_succ c)).eqSymm)

theorem pos_of_one_le {a : PTm n} (h : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
  pos_of_succ ((eq_add_of_le h).eqTrans (succ_add _ _))

theorem one_le_succ (a : PTm n) : Γ ⊢[PRAAx] le one (succ a) := (succ_monus_succ _ _).eqTrans (zero_le a)

theorem one_le_of_pos {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] le one a :=
  le_congr (.eqRefl _) h.eqSymm (one_le_succ _)

theorem pos_mul {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] a * b ≐ succ (pred (a * b)) :=
  pos_of_succ (c := pred a * succ (pred b) + pred b) ((congrMul ha hb).eqTrans (by ipra_ring))

theorem pos_of_two_le {a : PTm n} (h : Γ ⊢[PRAAx] le two a) : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
  pos_of_succ ((eq_add_of_le h).eqTrans (succ_add _ _))

/-! ## Order -/

theorem le_of_eq_zero {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] le a b :=
  le_congr h.eqSymm (.eqRefl _) (zero_le _)

theorem succ_le_succ {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (succ a) (succ b) :=
  le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one h)

theorem le_of_lt_succ {a b : PTm n} (h : Γ ⊢[PRAAx] lt a (succ b)) : Γ ⊢[PRAAx] le a b :=
  (succ_monus_succ _ _).eqSymm.eqTrans h

theorem lt_succ_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a (succ b) :=
  (succ_monus_succ a b).eqTrans h

theorem ne_of_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] neg (a ≐ b) :=
  .impI (lt_irrefl _ _ (lt_congr Prf.hyp0 (.eqRefl _) h.wk))

theorem pred_lt {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ succ (pred a)) : Γ ⊢[PRAAx] lt (pred a) a :=
  le_congr (.eqRefl _) h.eqSymm (le_refl _)

theorem add_le_add {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a + c) (b + d) :=
  le_trans (add_le_add_right c h₁) (le_congr (add_comm c b) (add_comm d b) (add_le_add_right b h₂))

theorem mul_le_mul {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a * c) (b * d) :=
  le_trans (mul_le_mul_right c h₁) (le_congr (mul_comm c b) (mul_comm d b) (mul_le_mul_right b h₂))

/-- Cancellation of a positive factor in `≤`. -/
theorem mul_cancel_le {c a b : PTm n} (hc : Γ ⊢[PRAAx] le one c) (h : Γ ⊢[PRAAx] le (c * a) (c * b)) :
    Γ ⊢[PRAAx] le a b :=
  mul_le_cancel (le_congr (congrMul (pos_of_one_le hc) (.eqRefl _)) (congrMul (pos_of_one_le hc) (.eqRefl _)) h)

/-- Cancellation of a positive factor in an equation. -/
theorem mul_cancel_eq {c a b : PTm n} (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (h : Γ ⊢[PRAAx] c * a ≐ c * b) :
    Γ ⊢[PRAAx] a ≐ b :=
  le_antisymm (mul_cancel_le (one_le_of_pos hc) (le_congr (.eqRefl _) h (le_refl _)))
    (mul_cancel_le (one_le_of_pos hc) (le_congr (.eqRefl _) h.eqSymm (le_refl _)))

theorem two_mul_cancel {a b : PTm n} (h : Γ ⊢[PRAAx] two * a ≐ two * b) : Γ ⊢[PRAAx] a ≐ b :=
  mul_cancel_eq (succ_pos _) h

theorem le_of_sq_le {a b : PTm n} (h : Γ ⊢[PRAAx] le (a * a) (b * b)) : Γ ⊢[PRAAx] le a b := by
  refine .orE (lt_or_le b a) ?_ Prf.hyp0
  have h₁ : (lt b a :: Γ) ⊢[PRAAx] lt (b * b) (succ b * succ b) := le_of_eq_add (d := b + b) (by ipra_ring)
  exact le_lt_absurd _ h.wk (le_trans h₁ (sq_le_sq Prf.hyp0))

theorem lt_of_sq_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt (a * a) (b * b)) : Γ ⊢[PRAAx] lt a b :=
  .orE (lt_or_le a b) Prf.hyp0 (le_lt_absurd _ (sq_le_sq Prf.hyp0) h.wk)

/-! ## Truncated subtraction -/

theorem monus_le_self (a b : PTm n) : Γ ⊢[PRAAx] le (monus a b) a := by
  refine .orE (lt_or_le a b) ?_ ?_
  · exact le_congr (le_of_lt Prf.hyp0 : (lt a b :: Γ) ⊢[PRAAx] monus a b ≐ zero).eqSymm (.eqRefl _) (zero_le _)
  · exact le_of_eq_add (d := b) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))

theorem monus_of_eq {a b d : PTm n} (h : Γ ⊢[PRAAx] a ≐ b + d) : Γ ⊢[PRAAx] monus a b ≐ d :=
  (congrMonus h (.eqRefl _)).eqTrans ((congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus _ _))

theorem monus_succ_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] monus (succ b) a ≐ succ (monus b a) :=
  (congrMonus ((congrSucc (eq_add_of_le h)).eqTrans (add_succ a _).eqSymm) (.eqRefl a)).eqTrans (add_monus' _ a)

theorem monus_monus_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] monus b (monus b a) ≐ a :=
  (congrMonus ((eq_add_of_le h).eqTrans (add_comm _ _)) (.eqRefl _)).eqTrans (add_monus' a (monus b a))

theorem add_eq_zero_left {a b : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ zero) : Γ ⊢[PRAAx] a ≐ zero :=
  (monus_zero a).eqSymm.eqTrans (le_congr (.eqRefl _) h (le_add_right a b))

theorem add_eq_zero_right {a b : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ zero) : Γ ⊢[PRAAx] b ≐ zero :=
  add_eq_zero_left ((add_comm b a).eqTrans h)

theorem monus_one_of_zero {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] monus one a ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

/-! ## Congruences -/

theorem congrPairT {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pairT a b ≐ pairT a' b' :=
  congrAdd (congrMul (congrAdd ha hb) (congrAdd ha hb)) ha

theorem congrEqb {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] eqb a b ≐ eqb a' b' :=
  congrMonus (.eqRefl _) (congrAdd (congrMonus ha hb) (congrMonus hb ha))

theorem congrSg {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] sg a ≐ sg b :=
  congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)

/-! ## The equality test and the signum -/

theorem eqb_zero_or_one (a b : PTm n) : Γ ⊢[PRAAx] (eqb a b ≐ zero) ⋎ (eqb a b ≐ one) :=
  .orE (eq_or_ne a b) (.orI₂ (eqb_of_eq Prf.hyp0)) (.orI₁ (eqb_of_ne Prf.hyp0))

theorem eqb_le_one (a b : PTm n) : Γ ⊢[PRAAx] le (eqb a b) one := monus_le_self _ _

theorem eq_of_eqb {a b : PTm n} (h : Γ ⊢[PRAAx] eqb a b ≐ one) : Γ ⊢[PRAAx] a ≐ b :=
  .orE (eq_or_ne a b) Prf.hyp0 (succ_ne_zero' _ (h.wk.eqSymm.eqTrans (eqb_of_ne Prf.hyp0)))

theorem sg_le_one (a : PTm n) : Γ ⊢[PRAAx] le (sg a) one := monus_le_self _ _

theorem sg_zero_or_one (a : PTm n) : Γ ⊢[PRAAx] (sg a ≐ zero) ⋎ (sg a ≐ one) :=
  .orE (zero_or_succ a) (.orI₁ ((congrSg Prf.hyp0).eqTrans sg_zero))
    (.orI₂ ((congrSg Prf.hyp0).eqTrans (sg_succ _)))

theorem sg_of_one_le {a : PTm n} (h : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] sg a ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

/-! ## Powers -/

theorem pw_one (a : PTm n) : Γ ⊢[PRAAx] pw a one ≐ a :=
  (pw_succ a zero).eqTrans ((congrMul (pw_zero a) (.eqRefl a)).eqTrans (one_mul a))

theorem pw_two (a : PTm n) : Γ ⊢[PRAAx] pw a two ≐ a * a :=
  (pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl _))

theorem pw_double (a k : PTm n) : Γ ⊢[PRAAx] pw a (two * k) ≐ pw a k * pw a k :=
  (congrAp2 powF (by ipra_ring) (.eqRefl a)).eqTrans (pw_add a k k)

end LeanProofs.IPRA.Common
