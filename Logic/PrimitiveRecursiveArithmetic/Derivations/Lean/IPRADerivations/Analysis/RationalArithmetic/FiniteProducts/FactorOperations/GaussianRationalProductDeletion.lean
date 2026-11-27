import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Foundations.RuntimePermutationDeletion

/-!
# Removing one factor from a genuine bounded product

Split the actual fold at the specified position. The original factors of
the shorter product match the bounded skip map, so the two remaining
segments give the shorter product in its original order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalProductDeletion

open_ipra
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (slot slot_before slot_after subst_slot)
open LeanProofs.IPRA.Foundations.SequenceComposition (add_lt_left)
open GaussianRationalFiniteProduct (qprod product_split product_succ product_index_congr product_congr_bounded offset_at)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalHorner (qmul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def retainedValues (t u : PTm 2) (N p x y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ inst2 u (var 0) (Syn.shift y) ≐ inst2 t (slot (Syn.shift p) (var 0)) (Syn.shift x))

ipra_subst retainedValues [Syn.subst_shift, Syn.shift_subst]

theorem retained_at (t u : PTm 2) (N p x y i : PTm n)
    (h : Γ ⊢[PRAAx] retainedValues t u N p x y) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 u i y ≐ inst2 t (slot p i) x := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ inst2 u i y ≐ inst2 t (slot p i) x := by
    ipra_simpa_inst [retainedValues,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_slot,subst_inst2] using h.allE i
  exact .impE rule hi

theorem product_before (t u : PTm 2) (p q x y : PTm n) (h : Γ ⊢[PRAAx] retainedValues t u (p+q) p x y) :
    Γ ⊢[PRAAx] qprod t p x ≐ qprod u p y := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  let a := Syn.shift p
  let b := Syn.shift q
  let v := Syn.shift x
  let w := Syn.shift y
  let Δ := lt (var 0) a :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) a := Prf.hyp0
  have old : Δ ⊢[PRAAx] retainedValues t u (a+b) a v w := by
    simpa only [Δ,a,b,v,w,Fm.shift,Syn.shift,subst_retainedValues,PTm.subst_add] using h.shift.wk
  have term := retained_at t u (a+b) a v w (var 0) old (lt_of_lt_of_le hi (le_add_right a b))
  exact (term.eqTrans (congrInst2 t (slot_before a (var 0) hi) (.eqRefl v))).eqSymm

theorem product_after (t u : PTm 2) (p q x y : PTm n) (h : Γ ⊢[PRAAx] retainedValues t u (p+q) p x y) :
    Γ ⊢[PRAAx] qprod (offB t) q (pairT (succ p) x) ≐ qprod (offB u) q (pairT p y) := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  let a := Syn.shift p
  let b := Syn.shift q
  let v := Syn.shift x
  let w := Syn.shift y
  let Δ := lt (var 0) b :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) b := Prf.hyp0
  have old : Δ ⊢[PRAAx] retainedValues t u (a+b) a v w := by
    simpa only [Δ,a,b,v,w,Fm.shift,Syn.shift,subst_retainedValues,PTm.subst_add] using h.shift.wk
  have fromOld := retained_at t u (a+b) a v w (a+var 0) old (add_lt_left a hi)
  have skip := (slot_after a (a+var 0) (le_add_right (Γ := Δ) a (var 0))).eqTrans (succ_add a (var 0)).eqSymm
  have e := (offset_at u a (var 0) w).eqTrans
    (fromOld.eqTrans ((congrInst2 t skip (.eqRefl _)).eqTrans (offset_at t (succ a) (var 0) v).eqSymm))
  simpa only [Δ,a,b,v,w,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_succ] using e.eqSymm

theorem product_remove (t u : PTm 2) (p q x y : PTm n) (h : Γ ⊢[PRAAx] retainedValues t u (p+q) p x y) :
    Γ ⊢[PRAAx] qprod t (succ p+q) x ≐ qmul (inst2 t p x) (qprod u (p+q) y) := by
  have left := product_before t u p q x y h
  have right := product_after t u p q x y h
  let a := qprod u p y
  let b := inst2 t p x
  let c := qprod (offB u) q (pairT p y)
  have move : Γ ⊢[PRAAx] qmul (qmul a b) c ≐ qmul b (qmul a c) :=
    (qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative a b) (.eqRefl c)).eqTrans
      (GaussianReciprocalHorner.qmul_associative b a c)
  exact (product_split t (succ p) q x).eqTrans
    ((qmul_congr ((product_succ t p x).eqTrans (qmul_congr left (.eqRefl _))) right).eqTrans
      (move.eqTrans (qmul_congr (.eqRefl _) (product_split u p q y).eqSymm)))

theorem actual_product_remove_closed (t u : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (retainedValues t u (var 0+var 1) (var 0) (var 2) (var 3) ⟶
      qprod t (succ (var 0)+var 1) (var 2) ≐ qmul (inst2 t (var 0) (var 2)) (qprod u (var 0+var 1) (var 3))) :=
  closeUniv 4 (.impI (product_remove t u _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalProductDeletion
