import IPRADerivations.Analysis.RationalArithmetic.RationalSupMetric
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Actual least minimization of independently denominated signed rationals

A scalar code is `(signed numerator pair, denominator predecessor)`, the
same coordinate format as `RationalSupMetric`. Every decoded denominator
is positive. The actual PR index scan updates only at a strict rational
decrease, retaining the earlier index on ties. Numerical horizon, candidate
indices and persistent input data are internal; the evaluator is a fixed
PR2 program. No sign bound or common denominator is required.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalArgmin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def left (a b : PTm n) : PTm n :=
  (numeratorOf a).pos*denominatorOf b+(numeratorOf b).neg*denominatorOf a
def rationalLE (a b : PTm n) : Fm PTm n := le (left a b) (left b a)
def rationalEq (a b : PTm n) : Fm PTm n := left a b ≐ left b a

@[simp] theorem subst_left {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (left a b) = left (Syn.subst σ a) (Syn.subst σ b) := by
  simp [left, numeratorOf, denominatorOf]
@[simp] theorem subst_rationalLE {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (rationalLE a b).subst σ = rationalLE (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [rationalLE, subst_le, subst_left]
@[simp] theorem subst_rationalEq {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (rationalEq a b).subst σ = rationalEq (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [rationalEq, Fm.subst_eq, subst_left]

theorem denominator_positive (a : PTm n) : Γ ⊢[PRAAx] le one (denominatorOf a) :=
  (succ_monus_succ zero _).eqTrans (zero_le _)

theorem reflexive (a : PTm n) : Γ ⊢[PRAAx] rationalLE a a := le_refl _
theorem total (a b : PTm n) : Γ ⊢[PRAAx] rationalLE a b ⋎ rationalLE b a := le_total _ _
theorem antisymm {a b : PTm n} (hab : Γ ⊢[PRAAx] rationalLE a b)
    (hba : Γ ⊢[PRAAx] rationalLE b a) : Γ ⊢[PRAAx] rationalEq a b := le_antisymm hab hba
theorem eq_le {a b : PTm n} (h : Γ ⊢[PRAAx] rationalEq a b) : Γ ⊢[PRAAx] rationalLE a b :=
  le_congr (.eqRefl _) h (le_refl _)

private theorem scaled_left (a b : PTm n) : Γ ⊢[PRAAx] left a b ≐
    (numeratorOf a * ZT.ofNat (denominatorOf b)).pos+
      (numeratorOf b * ZT.ofNat (denominatorOf a)).neg := by
  change Γ ⊢[PRAAx] left a b ≐
    ((numeratorOf a).pos*denominatorOf b+(numeratorOf a).neg*zero)+
      ((numeratorOf b).pos*zero+(numeratorOf b).neg*denominatorOf a)
  unfold left
  ipra_ring

theorem to_zle (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) :
    Γ ⊢[PRAAx] zle (numeratorOf a * ZT.ofNat (denominatorOf b))
      (numeratorOf b * ZT.ofNat (denominatorOf a)) :=
  le_congr (scaled_left a b) (scaled_left b a) h

theorem of_zle (a b : PTm n)
    (h : Γ ⊢[PRAAx] zle (numeratorOf a * ZT.ofNat (denominatorOf b))
      (numeratorOf b * ZT.ofNat (denominatorOf a))) : Γ ⊢[PRAAx] rationalLE a b :=
  le_congr (scaled_left a b).eqSymm (scaled_left b a).eqSymm h

private alias positive_cancel := Common.mul_cancel_le

/-- Rational transitivity cancels only the proved positive middle denominator. -/
theorem transitive {a b c : PTm n} (hab : Γ ⊢[PRAAx] rationalLE a b)
    (hbc : Γ ⊢[PRAAx] rationalLE b c) : Γ ⊢[PRAAx] rationalLE a c := by
  have ea := natEq (eq_add_of_le hab)
  have eb := natEq (eq_add_of_le hbc)
  have scaled : Γ ⊢[PRAAx] le (denominatorOf b*left a c) (denominatorOf b*left c a) := by
    refine le_of_eq_add (d := denominatorOf c*monus (left b a) (left a b)+
      denominatorOf a*monus (left c b) (left b c)) ?_
    unfold left at ea eb ⊢
    ipra_lc 𝔞(denominatorOf c)*ea+𝔞(denominatorOf a)*eb
  exact positive_cancel (denominator_positive b) scaled

theorem left_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] left a b ≐ left a' b' := by
  ipra_congr (left (var 0) (var 1) : PTm 2) with [ha, hb]

theorem rationalLE_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (h : Γ ⊢[PRAAx] rationalLE a b) :
    Γ ⊢[PRAAx] rationalLE a' b' := le_congr (left_congr ha hb) (left_congr hb ha) h

theorem rationalEq_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (h : Γ ⊢[PRAAx] rationalEq a b) :
    Γ ⊢[PRAAx] rationalEq a' b' := (left_congr ha hb).eqSymm.eqTrans (h.eqTrans (left_congr hb ha))

def value (v : PR 2) (i x : PTm n) : PTm n := ap2 v i x
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (v : PR 2) (i x : PTm n) :
    Syn.subst σ (value v i x) = value v (Syn.subst σ i) (Syn.subst σ x) := by simp [value]

def better (v : PR 2) (i j x : PTm n) : PTm n :=
  sg (monus (left (value v i x) (value v j x)) (left (value v j x) (value v i x)))
def choose (v : PR 2) (i j x : PTm n) : PTm n :=
  better v i j x*j+monus one (better v i j x)*i

@[simp] theorem subst_better {m : ℕ} (σ : Fin n → PTm m) (v : PR 2) (i j x : PTm n) :
    Syn.subst σ (better v i j x) = better v (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ x) := by
  simp [better, sg]
@[simp] theorem subst_choose {m : ℕ} (σ : Fin n → PTm m) (v : PR 2) (i j x : PTm n) :
    Syn.subst σ (choose v i j x) = choose v (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ x) := by
  simp [choose]

theorem choose_old (v : PR 2) (i j x : PTm n) (h : Γ ⊢[PRAAx] rationalLE (value v i x) (value v j x)) :
    Γ ⊢[PRAAx] choose v i j x ≐ i := by
  have bit : Γ ⊢[PRAAx] better v i j x ≐ zero := sg_le h
  unfold choose
  exact (congrAdd (congrMul bit (.eqRefl _)) (congrMul (congrMonus (.eqRefl _) bit) (.eqRefl _))).eqTrans
    ((congrAdd (zero_mul j) (congrMul (monus_zero one) (.eqRefl i))).eqTrans
      ((congrAdd (.eqRefl zero) (one_mul i)).eqTrans (zero_add i)))

theorem choose_new (v : PR 2) (i j x : PTm n)
    (h : Γ ⊢[PRAAx] lt (left (value v j x) (value v i x)) (left (value v i x) (value v j x))) :
    Γ ⊢[PRAAx] choose v i j x ≐ j := by
  have bit : Γ ⊢[PRAAx] better v i j x ≐ one := sg_lt h
  unfold choose
  exact (congrAdd (congrMul bit (.eqRefl _)) (congrMul (congrMonus (.eqRefl _) bit) (.eqRefl _))).eqTrans
    ((congrAdd (one_mul _) (congrMul (monus_self _) (.eqRefl _))).eqTrans (by ipra_ring))

theorem choice_minima (v : PR 2) (i j x : PTm n) :
    Γ ⊢[PRAAx] rationalLE (value v (choose v i j x) x) (value v i x) ⋏
      rationalLE (value v (choose v i j x) x) (value v j x) := by
  refine .orE (lt_or_le (left (value v j x) (value v i x)) (left (value v i x) (value v j x))) ?_ ?_
  · have eq : (lt (left (value v j x) (value v i x)) (left (value v i x) (value v j x)) :: Γ) ⊢[PRAAx]
        value v j x ≐ value v (choose v i j x) x :=
      congrAp2 v (choose_new v i j x Prf.hyp0).eqSymm (.eqRefl x)
    exact .andI (rationalLE_congr eq (.eqRefl _) (le_of_lt Prf.hyp0))
      (rationalLE_congr eq (.eqRefl _) (reflexive _))
  · have eq : (rationalLE (value v i x) (value v j x) :: Γ) ⊢[PRAAx]
        value v i x ≐ value v (choose v i j x) x :=
      congrAp2 v (choose_old v i j x Prf.hyp0).eqSymm (.eqRefl x)
    exact .andI (rationalLE_congr eq (.eqRefl _) (reflexive _))
      (rationalLE_congr eq (.eqRefl _) Prf.hyp0)

theorem choice_bound (v : PR 2) (i j x K : PTm n)
    (hi : Γ ⊢[PRAAx] le i K) (hj : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] le (choose v i j x) K := by
  refine .orE (lt_or_le (left (value v j x) (value v i x)) (left (value v i x) (value v j x))) ?_ ?_
  · exact le_congr (choose_new v i j x Prf.hyp0).eqSymm (.eqRefl _) hj.wk
  · exact le_congr (choose_old v i j x Prf.hyp0).eqSymm (.eqRefl _) hi.wk

def selectedStep (v : PR 2) : PTm 3 := choose v (var 1) (succ (var 0)) (var 2)
def selectedF (v : PR 2) : PR 2 := rec2 zero (selectedStep v)
def selected (v : PR 2) (K x : PTm n) : PTm n := ap2 (selectedF v) K x

@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (v : PR 2) (K x : PTm n) :
    Syn.subst σ (selected v K x) = selected v (Syn.subst σ K) (Syn.subst σ x) := by simp [selected]

theorem selected_zero (v : PR 2) (x : PTm n) : Γ ⊢[PRAAx] selected v zero x ≐ zero := by
  simpa [selected, selectedF] using rec2_zero (Γ := Γ) zero (selectedStep v) x
theorem selected_succ (v : PR 2) (K x : PTm n) :
    Γ ⊢[PRAAx] selected v (succ K) x ≐ choose v (selected v K x) (succ K) x := by
  simpa only [selected, selectedF, selectedStep, subst_choose, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_succ] using rec2_succ (Γ := Γ) zero (selectedStep v) K x

theorem selected_spec (v : PR 2) (K x : PTm n) : Γ ⊢[PRAAx] le (selected v K x) K := by
  have all : Γ ⊢[PRAAx] .all (le (selected v (var 0) (Syn.shift x)) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_selected, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact le_congr (selected_zero v x).eqSymm (.eqRefl _) (le_refl zero)
    · simp only [subst_le, subst_selected, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact le_congr (selected_succ v (var 0) (Syn.shift x)).eqSymm (.eqRefl _)
        (choice_bound v _ _ _ _ (le_trans Prf.hyp0 (le_succ_self _)) (le_refl _))
  simpa only [subst_le, subst_selected, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE K all

theorem selected_le_old (v : PR 2) (K x : PTm n) :
    Γ ⊢[PRAAx] rationalLE (value v (selected v (succ K) x) x) (value v (selected v K x) x) :=
  rationalLE_congr (congrAp2 v (selected_succ v K x).eqSymm (.eqRefl _)) (.eqRefl _)
    (Prf.andE₁ (choice_minima v _ _ _))
theorem selected_le_new (v : PR 2) (K x : PTm n) :
    Γ ⊢[PRAAx] rationalLE (value v (selected v (succ K) x) x) (value v (succ K) x) :=
  rationalLE_congr (congrAp2 v (selected_succ v K x).eqSymm (.eqRefl _)) (.eqRefl _)
    (Prf.andE₂ (choice_minima v _ _ _))

theorem selected_minimal (v : PR 2) (K i x : PTm n) (hi : Γ ⊢[PRAAx] le i K) :
    Γ ⊢[PRAAx] rationalLE (value v (selected v K x) x) (value v i x) := by
  have all : Γ ⊢[PRAAx] .all (le (Syn.shift i) (var 0) ⟶
      rationalLE (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)) (value v (Syn.shift i) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_rationalLE, subst_value, subst_selected,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI ?_
      have i0 : (le i zero :: Γ) ⊢[PRAAx] i ≐ zero := le_antisymm Prf.hyp0 (zero_le i)
      exact rationalLE_congr (congrAp2 v (selected_zero v x).eqSymm (.eqRefl _))
        (congrAp2 v i0.eqSymm (.eqRefl _)) (reflexive (value v zero x))
    · simp only [Fm.subst_imp, subst_le, subst_rationalLE, subst_value, subst_selected,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
      · exact transitive (selected_le_old v (var 0) (Syn.shift x))
          (Prf.impE Prf.hyp1.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))
      · exact rationalLE_congr (.eqRefl _) (congrAp2 v Prf.hyp0.eqSymm (.eqRefl _))
          (selected_le_new v (var 0) (Syn.shift x))
  have result : Γ ⊢[PRAAx] le i K ⟶ rationalLE (value v (selected v K x) x) (value v i x) := by
    simpa only [Fm.subst_imp, subst_le, subst_rationalLE, subst_value, subst_selected,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE K all
  exact .impE result hi

theorem selected_new (v : PR 2) (K x : PTm n)
    (h : Γ ⊢[PRAAx] lt (left (value v (succ K) x) (value v (selected v K x) x))
      (left (value v (selected v K x) x) (value v (succ K) x))) :
    Γ ⊢[PRAAx] selected v (succ K) x ≐ succ K :=
  (selected_succ v K x).eqTrans (choose_new v _ _ _ h)

theorem selected_old (v : PR 2) (K x : PTm n)
    (h : Γ ⊢[PRAAx] rationalLE (value v (selected v K x) x) (value v (succ K) x)) :
    Γ ⊢[PRAAx] selected v (succ K) x ≐ selected v K x :=
  (selected_succ v K x).eqTrans (choose_old v _ _ _ h)

/-- No earlier index has the selected rational value, including when
different signed pairs or denominators encode that same value. -/
theorem earlier_distinct (v : PR 2) (K i x : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (selected v K x)) :
    Γ ⊢[PRAAx] neg (rationalEq (value v i x) (value v (selected v K x) x)) := by
  have all : Γ ⊢[PRAAx] .all (lt (Syn.shift i) (selected v (var 0) (Syn.shift x)) ⟶
      neg (rationalEq (value v (Syn.shift i) (Syn.shift x))
        (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _, trivial, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_lt, subst_neg, subst_rationalEq, subst_value, subst_selected,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (lt_zero_absurd _ (lt_congr (.eqRefl _) (selected_zero v x) Prf.hyp0))
    · simp only [Fm.subst_imp, subst_lt, subst_neg, subst_rationalEq, subst_value, subst_selected,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI (.orE (lt_or_le
        (left (value v (succ (var 0)) (Syn.shift x)) (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)))
        (left (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)) (value v (succ (var 0)) (Syn.shift x)))) ?_ ?_)
      · let I : Fm PTm (n+1) := lt (Syn.shift i) (selected v (var 0) (Syn.shift x)) ⟶
          neg (rationalEq (value v (Syn.shift i) (Syn.shift x))
            (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)))
        let C : Fm PTm (n+1) := lt
          (left (value v (succ (var 0)) (Syn.shift x)) (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)))
          (left (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)) (value v (succ (var 0)) (Syn.shift x)))
        let Δ := C :: lt (Syn.shift i) (selected v (succ (var 0)) (Syn.shift x)) :: I :: Γ.map Fm.shift
        have next : Δ ⊢[PRAAx] selected v (succ (var 0)) (Syn.shift x) ≐ succ (var 0) :=
          selected_new v _ _ Prf.hyp0
        have index : Δ ⊢[PRAAx] le (Syn.shift i) (var 0) :=
          (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) next Prf.hyp1)
        have minimum := selected_minimal v (var 0) (Syn.shift i) (Syn.shift x) index
        refine .impI ?_
        have tied : (rationalEq (value v (Syn.shift i) (Syn.shift x))
            (value v (selected v (succ (var 0)) (Syn.shift x)) (Syn.shift x)) :: Δ) ⊢[PRAAx]
            rationalEq (value v (Syn.shift i) (Syn.shift x)) (value v (succ (var 0)) (Syn.shift x)) :=
          rationalEq_congr (.eqRefl _) (congrAp2 v next.wk (.eqRefl _)) Prf.hyp0
        have back := transitive minimum.wk (eq_le tied)
        exact lt_irrefl _ _ (le_trans (Prf.hyp1 : _ ⊢[PRAAx] C) back)
      · let I : Fm PTm (n+1) := lt (Syn.shift i) (selected v (var 0) (Syn.shift x)) ⟶
          neg (rationalEq (value v (Syn.shift i) (Syn.shift x))
            (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x)))
        let C := rationalLE (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x))
          (value v (succ (var 0)) (Syn.shift x))
        let Δ := C :: lt (Syn.shift i) (selected v (succ (var 0)) (Syn.shift x)) :: I :: Γ.map Fm.shift
        have old : Δ ⊢[PRAAx] selected v (succ (var 0)) (Syn.shift x) ≐ selected v (var 0) (Syn.shift x) :=
          selected_old v _ _ Prf.hyp0
        have distinct : Δ ⊢[PRAAx] neg (rationalEq (value v (Syn.shift i) (Syn.shift x))
            (value v (selected v (var 0) (Syn.shift x)) (Syn.shift x))) :=
          Prf.impE Prf.hyp1.wk (lt_congr (.eqRefl _) old Prf.hyp1)
        exact .impI (.impE distinct.wk
          (rationalEq_congr (.eqRefl _) (congrAp2 v old.wk (.eqRefl _)) Prf.hyp0))
  have result : Γ ⊢[PRAAx] lt i (selected v K x) ⟶
      neg (rationalEq (value v i x) (value v (selected v K x) x)) := by
    simpa only [Fm.subst_imp, subst_lt, subst_neg, subst_rationalEq, subst_value, subst_selected,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE K all
  exact .impE result hi

theorem selected_least (v : PR 2) (K i x : PTm n)
    (tie : Γ ⊢[PRAAx] rationalEq (value v i x) (value v (selected v K x) x)) :
    Γ ⊢[PRAAx] le (selected v K x) i :=
  .orE (lt_or_le i (selected v K x))
    (.botE _ (.impE (earlier_distinct v K i x Prf.hyp0) tie.wk)) Prf.hyp0

theorem selected_spec_closed (v : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (le (selected v (var 0) (var 1)) (var 0)) :=
  closeUniv 2 (selected_spec v _ _)

theorem selected_minimal_closed (v : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le (var 1) (var 0) ⟶
        rationalLE (value v (selected v (var 0) (var 2)) (var 2)) (value v (var 1) (var 2))) :=
  closeUniv 3 (.impI (selected_minimal v _ _ _ Prf.hyp0))

theorem selected_least_closed (v : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (rationalEq (value v (var 1) (var 2)) (value v (selected v (var 0) (var 2)) (var 2)) ⟶
        le (selected v (var 0) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (selected_least v _ _ _ Prf.hyp0))

theorem selected_program_closed (v : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((selected v zero (var 1) ≐ zero) ⋏
        (selected v (succ (var 0)) (var 1) ≐ choose v (selected v (var 0) (var 1)) (succ (var 0)) (var 1))) :=
  closeUniv 2 (.andI (selected_zero v _) (selected_succ v _ _))

theorem rational_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (denominatorOf (var 0))) ⋏
        (rationalLE (var 0) (var 1) ⟶ rationalLE (var 1) (var 2) ⟶ rationalLE (var 0) (var 2))) :=
  closeUniv 3 (.andI (denominator_positive _) (.impI (.impI (transitive Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalArgmin
