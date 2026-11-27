import IPRADerivations.Core.Monus
import ConciseIPRA.GuardedWitness
import IPRADerivations.Core.SubstCommand

/-!
# The order of iPRA

`a ≤ b` is the quantifier-free formula `a ∸ b = 0` (`le`), and `a < b` is
`S a ≤ b` (`lt`). Derived here:

* witnesses: `le_of_eq_add` (`b = a + d` gives `a ≤ b`) and `eq_add_of_le`
  (`a ≤ b` gives `b = a + (b ∸ a)`), which reduce order reasoning to the ring tools;
* `le_refl`, `zero_le`, `le_trans`, `le_antisymm`, `le_total`;
* `not_succ_le_self`, `lt_or_eq_of_le`, `lt_or_le`, and decidability of equality
  `eq_or_ne : a = b ∨ ¬ a = b`;
* monotonicity of `+` and `*`, and cancellation of `+` in `≤`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `a ≤ b`. -/
def le (a b : PTm n) : Fm PTm n := monus a b ≐ zero
/-- `a < b`. -/
def lt (a b : PTm n) : Fm PTm n := le (succ a) b
/-- `¬ φ`. -/
def neg (φ : Fm PTm n) : Fm PTm n := φ ⟶ Fm.bot

ipra_subst le
ipra_subst lt
ipra_subst neg

theorem le_QF (a b : PTm n) : (le a b).QF := trivial
theorem lt_QF (a b : PTm n) : (lt a b).QF := trivial

namespace Order

/-- Shift a derived comparison into the context with one fresh variable. -/
theorem shift_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  simpa only [Fm.shift, subst_le, Syn.shift] using h.shift

theorem shift_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) :
    Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) := by
  simpa only [Fm.shift, subst_lt, Syn.shift] using h.shift

/-- Shift a derived equality into the context with one fresh variable. -/
theorem shift_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift a ≐ Syn.shift b := by
  simpa only [Fm.shift, Fm.subst_eq, Syn.shift] using h.shift

theorem shift_one_le {a : PTm n} (h : Γ ⊢[PRAAx] le (succ zero) a) :
    Γ.map Fm.shift ⊢[PRAAx] le (succ zero) (Syn.shift a) := by
  simpa only [Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using shift_le h

theorem succ_le_succ {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (succ a) (succ b) :=
  (succ_monus_succ a b).eqTrans h

/-- A bound below a successor gives a weak bound at its predecessor. -/
theorem le_of_lt_succ {a b : PTm n} (h : Γ ⊢[PRAAx] lt a (succ b)) : Γ ⊢[PRAAx] le a b :=
  (succ_monus_succ a b).eqSymm.eqTrans h

theorem lt_succ_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a (succ b) :=
  succ_le_succ h

end Order

/-! ## Witnesses -/

theorem le_of_eq_add {a b d : PTm n} (h : Γ ⊢[PRAAx] b ≐ a + d) : Γ ⊢[PRAAx] le a b :=
  (congrMonus (.eqRefl a) h).eqTrans (monus_add a d)

theorem eq_add_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] b ≐ a + monus b a := by
  have m := monus_max (Γ := Γ) a b
  have e : Γ ⊢[PRAAx] b ≐ monus b a + a :=
    (zero_add b).eqSymm.eqTrans ((congrAdd h (.eqRefl b)).eqSymm.eqTrans m)
  exact e.eqTrans (add_comm _ _)

theorem le_refl (a : PTm n) : Γ ⊢[PRAAx] le a a := monus_self a

theorem zero_le (a : PTm n) : Γ ⊢[PRAAx] le zero a := zero_monus a

theorem le_add_right (a c : PTm n) : Γ ⊢[PRAAx] le a (a + c) := monus_add a c

theorem le_add_left (a c : PTm n) : Γ ⊢[PRAAx] le a (c + a) := le_of_eq_add (add_comm _ _)

theorem le_succ_self (a : PTm n) : Γ ⊢[PRAAx] le a (succ a) := le_of_eq_add (succ_eq_add_one a)

/-- A nonzero term is the successor of its truncated difference from one. -/
theorem eq_monus_one_add_one {a : PTm n} (ha : Γ ⊢[PRAAx] neg (a ≐ zero)) :
    Γ ⊢[PRAAx] a ≐ monus a (succ zero) + succ zero := by
  refine .orE (zero_or_succ a) (.botE _ (.impE ha.wk Prf.hyp0)) ?_
  have hs : (a ≐ succ (pred a)) :: Γ ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
  have hp := (congrMonus hs (.eqRefl (succ zero))).eqTrans
    ((succ_monus_succ (pred a) zero).eqTrans (monus_zero (pred a)))
  exact hs.eqTrans ((succ_eq_add_one _).eqTrans (congrAdd hp.eqSymm (.eqRefl _)))

/-- Normalize the guarded predecessor witness for any body, preserving the
bound and instantiating the body at the canonical witness `a ∸ 1`. -/
theorem predecessor_witness (a : PTm n) (body : Fm PTm (n + 1)) :
    Γ ⊢[PRAAx] Fm.iff
      (.ex ((le (var 0) (Syn.shift a) ⋏ (Syn.shift a ≐ var 0 + succ zero)) ⋏ body))
      (neg (a ≐ zero) ⋏ body.subst (Syn.inst (monus a (succ zero)))) := by
  let row := le (var 0) (Syn.shift a) ⋏ (Syn.shift a ≐ var 0 + succ zero)
  let w := monus a (succ zero)
  refine Prf.guardedWitness row body (neg (a ≐ zero)) w ?_ ?_
  · have he : row :: Γ.map Fm.shift ⊢[PRAAx] Syn.shift a ≐ var 0 + succ zero :=
      Prf.andE₂ Prf.hyp0
    have hne : row :: Γ.map Fm.shift ⊢[PRAAx] neg (Syn.shift a ≐ zero) := .impI <|
      succ_ne_zero (((succ_eq_add_one (var 0)).eqTrans he.wk.eqSymm).eqTrans Prf.hyp0)
    have hw : row :: Γ.map Fm.shift ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ monus (Syn.shift a) (succ zero) :=
      ((congrMonus he (.eqRefl _)).eqTrans (add_monus (var 0) (succ zero))).eqSymm
    simpa [w, Fm.shift, Syn.shift] using Prf.andI hne hw
  · have h : (neg (a ≐ zero) :: Γ) ⊢[PRAAx] neg (a ≐ zero) := Prf.hyp0
    have he := eq_monus_one_add_one h
    simpa [row, w] using Prf.andI (le_of_eq_add he) he

theorem le_trans {a b c : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] le a c :=
  le_of_eq_add ((eq_add_of_le h₂).eqTrans <|
    (congrAdd (eq_add_of_le h₁) (.eqRefl _)).eqTrans (add_assoc _ _ _))

theorem le_antisymm {a b : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] a ≐ b := by
  have m := monus_max (Γ := Γ) a b
  refine (zero_add a).eqSymm.eqTrans ?_
  refine (congrAdd h₂ (.eqRefl a)).eqSymm.eqTrans ?_
  exact m.eqSymm.eqTrans ((congrAdd h₁ (.eqRefl b)).eqTrans (zero_add b))

/-- `x · y = 0` gives `x = 0 ∨ y = 0`. -/
theorem zero_or_zero_of_mul {x y : PTm n} (h : Γ ⊢[PRAAx] x * y ≐ zero) :
    Γ ⊢[PRAAx] (x ≐ zero) ⋎ (y ≐ zero) := by
  refine .orE (zero_or_succ x) (.orI₁ Prf.hyp0) (.orI₂ (eq_zero_of_succ_mul (c := pred x) ?_))
  exact (congrMul Prf.hyp0 (.eqRefl y)).eqSymm.eqTrans h.wk

theorem le_total (a b : PTm n) : Γ ⊢[PRAAx] le a b ⋎ le b a :=
  zero_or_zero_of_mul (monus_mul a b)

theorem le_congr {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le a' b' :=
  (congrMonus h₁.eqSymm h₂.eqSymm).eqTrans h

theorem lt_congr {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b')
    (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] lt a' b' :=
  le_congr (congrSucc h₁) h₂ h

/-- A natural term equal to a successor is positive. -/
theorem Order.zero_lt_of_eq_succ {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ succ b) : Γ ⊢[PRAAx] lt zero a :=
  le_congr (.eqRefl _) h.eqSymm (Order.lt_succ_of_le (zero_le b))

/-! ## Strict order and decidability -/

theorem not_succ_le_self (a : PTm n) (φ : Fm PTm n) (h : Γ ⊢[PRAAx] le (succ a) a) : Γ ⊢[PRAAx] φ := by
  refine succ_ne_zero' φ (a := zero) ?_
  refine .eqTrans ?_ h
  exact (add_monus' (succ zero) a).eqSymm.eqTrans (congrMonus (succ_eq_add_one a).eqSymm (.eqRefl a))

theorem lt_irrefl (a : PTm n) (φ : Fm PTm n) (h : Γ ⊢[PRAAx] lt a a) : Γ ⊢[PRAAx] φ :=
  not_succ_le_self a φ h

theorem lt_or_eq_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] lt a b ⋎ (a ≐ b) := by
  have e := eq_add_of_le h
  refine .orE (zero_or_succ (monus b a)) ?_ ?_
  · exact .orI₂ ((add_zero a).eqSymm.eqTrans ((congrAdd (.eqRefl a) Prf.hyp0).eqSymm.eqTrans e.wk.eqSymm))
  · refine .orI₁ (le_of_eq_add (d := pred (monus b a)) ?_)
    refine e.wk.eqTrans ?_
    exact (congrAdd (.eqRefl a) Prf.hyp0).eqTrans ((add_succ _ _).eqTrans (succ_add _ _).eqSymm)

theorem Order.lt_succ_cases {a b : PTm n} (h : Γ ⊢[PRAAx] lt a (succ b)) :
    Γ ⊢[PRAAx] lt a b ⋎ (a ≐ b) :=
  lt_or_eq_of_le (Order.le_of_lt_succ h)

theorem le_of_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] le a b :=
  le_trans (le_succ_self a) h

theorem lt_of_lt_of_le {a b c : PTm n} (h₁ : Γ ⊢[PRAAx] lt a b) (h₂ : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] lt a c := le_trans h₁ h₂

theorem lt_of_le_of_lt {a b c : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] lt b c) :
    Γ ⊢[PRAAx] lt a c :=
  le_trans (Order.succ_le_succ h₁) h₂

/-- `a ≤ b` and `b < a` are incompatible. -/
theorem le_lt_absurd {a b : PTm n} (φ : Fm PTm n) (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] lt b a) :
    Γ ⊢[PRAAx] φ := lt_irrefl a φ (lt_of_le_of_lt h₁ h₂)

theorem lt_or_le (a b : PTm n) : Γ ⊢[PRAAx] lt a b ⋎ le b a := by
  refine .orE (le_total a b) ?_ (.orI₂ Prf.hyp0)
  refine .orE (lt_or_eq_of_le Prf.hyp0) (.orI₁ Prf.hyp0) ?_
  exact .orI₂ (le_congr Prf.hyp0 (.eqRefl a) (le_refl a))

theorem Order.ne_symm {a b : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ b)) : Γ ⊢[PRAAx] neg (b ≐ a) :=
  .impI (.impE h.wk Prf.hyp0.eqSymm)

/-- A weak inequality is strict when equality is excluded. -/
theorem Order.lt_of_le_of_ne {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) (hne : Γ ⊢[PRAAx] neg (a ≐ b)) :
    Γ ⊢[PRAAx] lt a b :=
  .orE (lt_or_eq_of_le h) Prf.hyp0 (.botE _ (.impE hne.wk Prf.hyp0))

/-- Distinct terms admit exactly the two strict order cases. -/
theorem Order.lt_or_gt_of_ne {a b : PTm n} (hne : Γ ⊢[PRAAx] neg (a ≐ b)) :
    Γ ⊢[PRAAx] lt a b ⋎ lt b a :=
  .orE (lt_or_le a b) (.orI₁ Prf.hyp0)
    (.orI₂ (Order.lt_of_le_of_ne Prf.hyp0 (Order.ne_symm hne).wk))

theorem eq_or_ne (a b : PTm n) : Γ ⊢[PRAAx] (a ≐ b) ⋎ neg (a ≐ b) := by
  refine .orE (lt_or_le a b) ?_ ?_
  · refine .orI₂ (.impI ?_)
    exact lt_irrefl a _ (lt_congr (.eqRefl a) Prf.hyp0.eqSymm Prf.hyp1)
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ (.orI₁ Prf.hyp0.eqSymm)
    refine .orI₂ (.impI ?_)
    exact lt_irrefl a _ (lt_congr Prf.hyp0.eqSymm (.eqRefl a) Prf.hyp1)

/-! ## Monotonicity and cancellation -/

theorem add_le_add_right {a b : PTm n} (c : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (a + c) (b + c) := by
  refine le_of_eq_add (d := monus b a) ?_
  exact (congrAdd (eq_add_of_le h) (.eqRefl c)).eqTrans (add_right_comm _ _ _)

theorem add_le_add_left {a b : PTm n} (c : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (c + a) (c + b) :=
  le_congr (add_comm _ _) (add_comm _ _) (add_le_add_right c h)

theorem mul_le_mul_right {a b : PTm n} (c : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (a * c) (b * c) :=
  le_of_eq_add (d := monus b a * c) ((congrMul (eq_add_of_le h) (.eqRefl c)).eqTrans (add_mul _ _ _))

theorem mul_le_mul_left {a b : PTm n} (c : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (c * a) (c * b) :=
  le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right c h)

/-- The index `i * R + j` lies in the first `N` blocks of length `R`. -/
theorem Order.mul_add_lt_mul {i j N R : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j R) :
    Γ ⊢[PRAAx] lt (i * R + j) (N * R) :=
  lt_of_lt_of_le (le_congr (add_succ _ _) (succ_mul _ _).eqSymm (add_le_add_left _ hj))
    (mul_le_mul_right R hi)

namespace Order

/-- Multiplication by a positive natural term preserves strict order. -/
theorem mul_lt_mul_right {a b c : PTm n} (hc : Γ ⊢[PRAAx] le (succ zero) c)
    (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] lt (a * c) (b * c) :=
  lt_congr (add_zero _) (.eqRefl _) (mul_add_lt_mul h hc)

theorem mul_lt_mul_left {a b c : PTm n} (hc : Γ ⊢[PRAAx] le (succ zero) c)
    (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] lt (c * a) (c * b) :=
  lt_congr (mul_comm _ _) (mul_comm _ _) (mul_lt_mul_right hc h)

/-- Strict order of the products entails strict order before scaling. -/
theorem lt_of_mul_lt_mul_left {a b c : PTm n} (h : Γ ⊢[PRAAx] lt (c * a) (c * b)) :
    Γ ⊢[PRAAx] lt a b :=
  .orE (lt_or_le a b) Prf.hyp0 (le_lt_absurd _ (mul_le_mul_left c Prf.hyp0) h.wk)

theorem lt_of_mul_lt_mul_right {a b c : PTm n} (h : Γ ⊢[PRAAx] lt (a * c) (b * c)) :
    Γ ⊢[PRAAx] lt a b :=
  lt_of_mul_lt_mul_left (lt_congr (mul_comm _ _) (mul_comm _ _) h)

/-- A positive margin between scaled terms gives a strict comparison of the original terms. -/
theorem lt_of_mul_add_le_mul {a b c d : PTm n} (hd : Γ ⊢[PRAAx] le (succ zero) d)
    (h : Γ ⊢[PRAAx] le (c * a + d) (c * b)) : Γ ⊢[PRAAx] lt a b :=
  lt_of_mul_lt_mul_left
    (le_trans (le_congr (succ_eq_add_one _).eqSymm (.eqRefl _) (add_le_add_left (c * a) hd)) h)

end Order

/-- Variables: `0 = c` (induction), `1 = a`, `2 = b`. -/
private abbrev mcF : Fm PTm 3 := monus (var 1 + var 0) (var 2 + var 0) ≐ monus (var 1) (var 2)

private theorem monus_add_add₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] mcF := by
  refine ind _ trivial ?_ ?_
  · ipra_subst'
    exact congrMonus (add_zero _) (add_zero _)
  · ipra_subst'
    exact (congrMonus (add_succ _ _) (add_succ _ _)).eqTrans ((succ_monus_succ _ _).eqTrans Prf.hyp0)

theorem monus_add_add (a b c : PTm n) : Γ ⊢[PRAAx] monus (a + c) (b + c) ≐ monus a b := by
  simpa using inst (Γ := Γ) monus_add_add₀ (![c, a, b] : Fin 3 → PTm n)

theorem le_of_add_le_add_right {a b c : PTm n} (h : Γ ⊢[PRAAx] le (a + c) (b + c)) :
    Γ ⊢[PRAAx] le a b := (monus_add_add a b c).eqSymm.eqTrans h

end LeanProofs.IPRA
