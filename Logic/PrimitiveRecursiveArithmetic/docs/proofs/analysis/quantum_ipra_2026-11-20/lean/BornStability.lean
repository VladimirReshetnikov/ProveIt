import IPRADerivations.Core.Tactic
import IPRADerivations.Core.Order

/-! A variable-error stability estimate for the squared norm of one complex
amplitude, proved as a universally closed derivation in object iPRA. -/

namespace QuantumIPRA.Born
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zle (x y : ZT n) : Fm PTm n := le (x.pos + y.neg) (y.pos + x.neg)

private def slack (x y : ZT n) : PTm n :=
  PTm.monus (y.pos + x.neg) (x.pos + y.neg)

private theorem slack_eq {x y : ZT n} (h : Γ ⊢[PRAAx] zle x y) :
    ZT.toZ Γ y - ZT.toZ Γ x = ZT.toZ Γ (ZT.ofNat (slack x y)) := by
  have e := natEq (eq_add_of_le (a := x.pos + y.neg) (b := y.pos + x.neg) h)
  rw [ZT.toZ_ofNat]
  simp only [slack, ZT.toZ, Q.mk_add, map_add] at *
  linear_combination e

private theorem by_slack (x y : ZT n) (s : PTm n)
    (h : ZT.toZ Γ y - ZT.toZ Γ x = ZT.toZ Γ (ZT.ofNat s)) : Γ ⊢[PRAAx] zle x y := by
  apply le_of_eq_add (d := s)
  apply deriveNat
  rw [ZT.toZ_ofNat] at h
  simp only [ZT.toZ, Q.mk_add, map_add] at *
  linear_combination h

def bounded (x : ZT n) (M : PTm n) : Fm PTm n :=
  zle x (ZT.ofNat M) ⋏ zle (-x) (ZT.ofNat M)

def close (x y : ZT n) (e : PTm n) : Fm PTm n :=
  zle (x-y) (ZT.ofNat e) ⋏ zle (y-x) (ZT.ofNat e)

private def twice (x : ZT n) : ZT n := ZT.natLit 2 * x
private def sqDiff (x y : ZT n) : ZT n := ZT.sq x - ZT.sq y

/-- The nonnegative slack is (2M-x-y)(e+x-y)+(2M+x+y)(e-x+y). -/
private theorem square_upper (x y : ZT n) (M e : PTm n)
    (hx : Γ ⊢[PRAAx] bounded x M) (hy : Γ ⊢[PRAAx] bounded y M)
    (hd : Γ ⊢[PRAAx] close x y e) :
    Γ ⊢[PRAAx] zle (twice (sqDiff x y)) (ZT.ofNat (PTm.num 4*M*e)) := by
  have xm := slack_eq hx.andE₁
  have xp := slack_eq hx.andE₂
  have ym := slack_eq hy.andE₁
  have yp := slack_eq hy.andE₂
  have dm := slack_eq hd.andE₁
  have dp := slack_eq hd.andE₂
  apply by_slack _ _
    ((slack x (ZT.ofNat M) + slack y (ZT.ofNat M)) * slack (y-x) (ZT.ofNat e) +
     (slack (-x) (ZT.ofNat M) + slack (-y) (ZT.ofNat M)) * slack (x-y) (ZT.ofNat e))
  unfold twice sqDiff
  ipra_simps
  rw [← xm, ← ym, ← dp, ← xp, ← yp, ← dm]
  ring

def weight (a b : ZT n) : ZT n := ZT.sq a + ZT.sq b

private theorem weight_upper (a b c d : ZT n) (M e : PTm n)
    (ha : Γ ⊢[PRAAx] bounded a M) (hb : Γ ⊢[PRAAx] bounded b M)
    (hc : Γ ⊢[PRAAx] bounded c M) (hd : Γ ⊢[PRAAx] bounded d M)
    (hr : Γ ⊢[PRAAx] close a c e) (hi : Γ ⊢[PRAAx] close b d e) :
    Γ ⊢[PRAAx] zle (twice (weight a b - weight c d)) (ZT.ofNat (PTm.num 8*M*e)) := by
  have r := slack_eq (square_upper a c M e ha hc hr)
  have i := slack_eq (square_upper b d M e hb hd hi)
  apply by_slack _ _
    (slack (twice (sqDiff a c)) (ZT.ofNat (PTm.num 4*M*e)) +
     slack (twice (sqDiff b d)) (ZT.ofNat (PTm.num 4*M*e)))
  unfold weight twice sqDiff at *
  ipra_simps
  linear_combination r + i

/-- Cancellation of a factor two in natural order, using decidable comparison. -/
private theorem halve_nat {a b : PTm n} (h : Γ ⊢[PRAAx] le (a+a) (b+b)) :
    Γ ⊢[PRAAx] le a b := by
  refine .orE (le_total a b) Prf.hyp0 ?_
  have hb : le b a :: Γ ⊢[PRAAx] le b a := Prf.hyp0
  have hba := add_le_add_right a hb
  have hab := le_congr (add_comm b a) (.eqRefl _) hba
  exact le_of_add_le_add_right (le_trans hab h.wk)

/-- Transfer the doubled slack estimate back to the sharp four-radius form. -/
private theorem halve_weight (x : ZT n) (M e : PTm n)
    (h : Γ ⊢[PRAAx] zle (twice x) (ZT.ofNat (PTm.num 8*M*e))) :
    Γ ⊢[PRAAx] zle x (ZT.ofNat (PTm.num 4*M*e)) := by
  change Γ ⊢[PRAAx] le (x.pos + PTm.zero) (PTm.num 4*M*e + x.neg)
  apply halve_nat
  apply le_of_eq_add (d := slack (twice x) (ZT.ofNat (PTm.num 8*M*e)))
  apply deriveNat
  have v := slack_eq h
  simp only [twice, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_ofNat] at v
  simp only [ZT.toZ, Q.mk_mul, Q.mk_num, Q.mk_add, Q.mk_zero, map_mul, map_natCast,
    map_add, map_zero] at *
  unfold twice
  linear_combination v

def premises (a b c d : ZT n) (M e : PTm n) : Fm PTm n :=
  bounded a M ⋏ (bounded b M ⋏ (bounded c M ⋏
    (bounded d M ⋏ (close a c e ⋏ close b d e))))

/-- The two inequalities express |weight(a,b)-weight(c,d)| ≤ 4 M e. -/
def statement (a b c d : ZT n) (M e : PTm n) : Fm PTm n :=
  premises a b c d M e ⟶
    (zle (weight a b - weight c d) (ZT.ofNat (PTm.num 4*M*e)) ⋏
     zle (weight c d - weight a b) (ZT.ofNat (PTm.num 4*M*e)))

theorem stability_at (a b c d : ZT n) (M e : PTm n) :
    Γ ⊢[PRAAx] statement a b c d M e := by
  apply Prf.impI
  have h : premises a b c d M e :: Γ ⊢[PRAAx] premises a b c d M e := Prf.hyp0
  have ha := h.andE₁
  have hb := h.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₁
  have hd := h.andE₂.andE₂.andE₂.andE₁
  have hr := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hi := h.andE₂.andE₂.andE₂.andE₂.andE₂
  exact .andI (halve_weight _ M e (weight_upper a b c d M e ha hb hc hd hr hi))
    (halve_weight _ M e (weight_upper c d a b M e hc hd ha hb
      (.andI hr.andE₂ hr.andE₁) (.andI hi.andE₂ hi.andE₁)))

def stabilitySentence : Fm PTm 0 := univ 10
  (statement (ZT.var2 0 1) (ZT.var2 2 3) (ZT.var2 4 5) (ZT.var2 6 7) (var 8) (var 9))

theorem stability_closed : [] ⊢[PRAAx] stabilitySentence := closeUniv 10 (stability_at _ _ _ _ _ _)

#print axioms stability_closed
end QuantumIPRA.Born
