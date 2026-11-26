import IPRADerivations.Analysis.Stirling.Robbins.RobbinsSeries

/-!
# Finite Stirling series at a positive rational argument

For x = a/b, put u = b², w = (2a+b)², and v = w−u.
The first K terms of the difference series have denominator w^K L!,
where 2K+1 ≤ L. Retaining the j=2 term gives a sharp upper bound on
the series including the geometric tail u^(K+1)/(3vw^K).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.StirlingRationalSeries

open_ipra
open RobbinsSeries (gq g_eq)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def stepBody : PTm 3 :=
  fstT (var 2)*var 1 + pw (fstT (sndT (var 2))) (succ (var 0))*gq (succ (var 0)) (sndT (sndT (var 2)))
def foldF : PR 2 := rec2 zero stepBody
def fold (w u L K : PTm n) : PTm n := ap2 foldF K (pairT w (pairT u L))

ipra_subst fold

theorem fold_zero (w u L : PTm n) : Γ ⊢[PRAAx] fold w u L zero ≐ zero := by
  simpa [fold,foldF] using rec2_zero (Γ := Γ) zero stepBody (pairT w (pairT u L))

theorem fold_succ (w u L K : PTm n) : Γ ⊢[PRAAx]
    fold w u L (succ K) ≐ w*fold w u L K + pw u (succ K)*gq (succ K) L := by
  let x := pairT w (pairT u L)
  have src := rec2_succ (Γ := Γ) zero stepBody K x
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT u L := snd_pair _ _
  have result : Γ ⊢[PRAAx]
      fstT x*fold w u L K + pw (fstT (sndT x)) (succ K)*gq (succ K) (sndT (sndT x)) ≐
      w*fold w u L K + pw u (succ K)*gq (succ K) L :=
    congrAdd (congrMul (fst_pair _ _) (.eqRefl _))
      (congrMul (congrAp2 powF (.eqRefl _) tail.fstE)
        (congrAp2 quoF (congrAp2 factF tail.sndE (.eqRefl _)) (.eqRefl _)))
  have e : Γ ⊢[PRAAx] fold w u L (succ K) ≐
      fstT x*fold w u L K + pw (fstT (sndT x)) (succ K)*gq (succ K) (sndT (sndT x)) := by
    simpa [x,fold,foldF,stepBody,ConciseIPRA.PTm.subst_succ] using src
  exact e.eqTrans result

def lowerFormula (w u L k : PTm n) : Fm PTm n :=
  le (u*pw w k*fact L) (num 3*fold w u L (succ k))

ipra_subst lowerFormula

private theorem lower_base (w u L : PTm n) (hL : Γ ⊢[PRAAx] le (num 3) L) :
    Γ ⊢[PRAAx] lowerFormula w u L zero := by
  have bound : Γ ⊢[PRAAx] le (succ (two*succ zero)) L := le_congr (by ipra_ring) (.eqRefl _) hL
  have coef := natEq (g_eq bound)
  have t0 := natEq (fold_zero (Γ := Γ) w u L)
  have t1 := natEq (fold_succ (Γ := Γ) w u L zero)
  have p := natEq (pw_succ (Γ := Γ) u zero)
  have u0 := natEq (pw_zero (Γ := Γ) u)
  have w0 := natEq (pw_zero (Γ := Γ) w)
  change Γ ⊢[PRAAx] le (u*pw w zero*fact L) (num 3*fold w u L (succ zero))
  ipra_le 0 using
    rw [t1,t0,p,u0,w0]
    linear_combination -𝔞 u*coef

private theorem lower_step (w u L k : PTm n) (h : Γ ⊢[PRAAx] lowerFormula w u L k) :
    Γ ⊢[PRAAx] lowerFormula w u L (succ k) := by
  have unfoldFold := natEq (fold_succ (Γ := Γ) w u L (succ k))
  have p := natEq (pw_succ (Γ := Γ) w k)
  change Γ ⊢[PRAAx] le (u*pw w (succ k)*fact L) (num 3*fold w u L (succ (succ k)))
  change Γ ⊢[PRAAx] le (u*pw w k*fact L) (num 3*fold w u L (succ k)) at h
  ipra_le 𝔞 w*sl h + 3*𝔞 (pw u (succ (succ k)))*𝔞 (gq (succ (succ k)) L) using rw [unfoldFold,p]; ring

theorem lower (w u L k : PTm n) (hL : Γ ⊢[PRAAx] le (num 3) L) :
    Γ ⊢[PRAAx] lowerFormula w u L k := by
  have all : Γ ⊢[PRAAx] .all (lowerFormula (Syn.shift w) (Syn.shift u) (Syn.shift L) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_lowerFormula,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using lower_base w u L hL
    · simp only [subst_lowerFormula,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact lower_step _ _ _ _ Prf.hyp0
  simpa only [subst_lowerFormula,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def upperWithBase (w v u L k : PTm n) : Fm PTm n :=
  let K := succ (succ k)
  le (num 15*(w*w)*v*fold w u L K + num 5*(w*w)*pw u (succ K)*fact L +
        two*v*(u*u)*pw w K*fact L)
    (num 5*u*pw w (succ (succ K))*fact L)

def upperFormula (v u L k : PTm n) : Fm PTm n := upperWithBase (v+u) v u L k

ipra_subst upperWithBase

ipra_subst upperFormula

private theorem upper_base (v u L : PTm n) (hL : Γ ⊢[PRAAx] le (succ (two*succ (succ zero))) L) :
    Γ ⊢[PRAAx] upperFormula v u L zero := by
  let w := v+u
  have wsum : 𝔞 w = 𝔞 v+𝔞 u := by
    change 𝔞 (v+u) = _
    simp only [IPRA.Q.mk_add,map_add]
  have h3 := le_trans (le_of_eq_add (d := two) (by ipra_ring :
    Γ ⊢[PRAAx] succ (two*succ (succ zero)) ≐ succ (two*succ zero)+two)) hL
  have c3 := natEq (g_eq h3)
  have c5 := natEq (g_eq hL)
  have t0 := natEq (fold_zero (Γ := Γ) w u L)
  have t1 := natEq (fold_succ (Γ := Γ) w u L zero)
  have t2 := natEq (fold_succ (Γ := Γ) w u L (succ zero))
  have Eu0 := natEq (pw_zero (Γ := Γ) u)
  have Eu1 := natEq (pw_succ (Γ := Γ) u zero)
  have Eu2 := natEq (pw_succ (Γ := Γ) u (succ zero))
  have Eu3 := natEq (pw_succ (Γ := Γ) u (succ (succ zero)))
  have Ew0 := natEq (pw_zero (Γ := Γ) w)
  have Ew1 := natEq (pw_succ (Γ := Γ) w zero)
  have Ew2 := natEq (pw_succ (Γ := Γ) w (succ zero))
  have Ew3 := natEq (pw_succ (Γ := Γ) w (succ (succ zero)))
  have Ew4 := natEq (pw_succ (Γ := Γ) w (succ (succ (succ zero))))
  change Γ ⊢[PRAAx] le
    (num 15*(w*w)*v*fold w u L (succ (succ zero)) + num 5*(w*w)*pw u (succ (succ (succ zero)))*fact L +
      two*v*(u*u)*pw w (succ (succ zero))*fact L)
    (num 5*u*pw w (succ (succ (succ (succ zero))))*fact L)
  ipra_le 0 using
    rw [t2,t1,t0,Eu3,Eu2,Eu1,Eu0,Ew4,Ew3,Ew2,Ew1,Ew0]
    linear_combination (5*(𝔞 w)^3*𝔞 v*𝔞 u)*c3 + (3*(𝔞 w)^2*𝔞 v*(𝔞 u)^2)*c5 +
      5*𝔞 u*(𝔞 w)^2*𝔞 (fact L)*(𝔞 w+𝔞 u)*wsum

private theorem upper_step (v u L k : PTm n) (hL : Γ ⊢[PRAAx] le (succ (two*succ (succ (succ k)))) L)
    (h : Γ ⊢[PRAAx] upperFormula v u L k) : Γ ⊢[PRAAx] upperFormula v u L (succ k) := by
  let w := v+u
  let K := succ (succ k)
  have wsum : 𝔞 w = 𝔞 v+𝔞 u := by
    change 𝔞 (v+u) = _
    simp only [IPRA.Q.mk_add,map_add]
  have coef := natEq (g_eq hL)
  have e := natEq (fold_succ (Γ := Γ) w u L K)
  have eU := natEq (pw_succ (Γ := Γ) u (succ K))
  have eW := natEq (pw_succ (Γ := Γ) w K)
  have eW' := natEq (pw_succ (Γ := Γ) w (succ (succ K)))
  change Γ ⊢[PRAAx] le
    (num 15*(w*w)*v*fold w u L (succ K) + num 5*(w*w)*pw u (succ (succ K))*fact L +
      two*v*(u*u)*pw w (succ K)*fact L)
    (num 5*u*pw w (succ (succ (succ K)))*fact L)
  change Γ ⊢[PRAAx] le (num 15*(w*w)*v*fold w u L K + num 5*(w*w)*pw u (succ K)*fact L +
    two*v*(u*u)*pw w K*fact L) (num 5*u*pw w (succ (succ K))*fact L) at h
  ipra_le 𝔞 w*sl h + 5*(𝔞 w)^2*𝔞 v*𝔞 (pw u (succ K))*(2*(𝔞 k+2))*𝔞 (gq (succ K) L) using
    rw [e,eU,eW,eW']
    linear_combination (5*(𝔞 w)^2*𝔞 v*𝔞 (pw u (succ K)))*coef +
      5*(𝔞 w)^2*𝔞 (fact L)*𝔞 (pw u (succ K))*wsum

theorem upper (v u L k : PTm n) (hL : Γ ⊢[PRAAx] le (succ (two*succ (succ k))) L) :
    Γ ⊢[PRAAx] upperFormula v u L k := by
  have all : Γ ⊢[PRAAx] .all
      (le (succ (two*succ (succ (var 0)))) (Syn.shift L) ⟶ upperFormula (Syn.shift v) (Syn.shift u) (Syn.shift L) (var 0)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_upperFormula, one, two]
    · exact .impI (upper_base v u L Prf.hyp0)
    · refine .impI (upper_step _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans ?_ Prf.hyp0)))
      exact le_of_eq_add (d := two) (by ipra_ring)
  have h : Γ ⊢[PRAAx] le (succ (two*succ (succ k))) L ⟶ upperFormula v u L k := by
    simpa only [Fm.subst_imp,subst_le,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,subst_upperFormula,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,one,two,ConciseIPRA.PTm.subst_zero] using all.allE k
  exact .impE h hL

theorem upper_at_base (w v u L k : PTm n) (e : Γ ⊢[PRAAx] w ≐ v+u)
    (hL : Γ ⊢[PRAAx] le (succ (two*succ (succ k))) L) : Γ ⊢[PRAAx] upperWithBase w v u L k := by
  let law := (upperWithBase (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
  have src : Γ ⊢[PRAAx] law.subst ![v+u,v,u,L,k] := by
    simpa only [law,upperFormula,subst_upperWithBase,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using upper v u L k hL
  simpa only [law,upperFormula,subst_upperWithBase,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (Ax := PRAAx) law ![v+u,v,u,L,k] ![w,v,u,L,k]
      (fun i => by fin_cases i; exact e.eqSymm; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _) src

theorem actual_finite_rational_stirling_series_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (succ (two*succ (succ (var 3)))) (var 2) ⟶ upperFormula (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (upper _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.StirlingRationalSeries
