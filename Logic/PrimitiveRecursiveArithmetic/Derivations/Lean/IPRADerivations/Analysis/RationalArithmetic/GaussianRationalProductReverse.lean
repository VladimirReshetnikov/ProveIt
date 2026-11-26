import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalFiniteRoots

/-!
# Exact reversal of an actual rational product

The product of the consumed reverse prefix and the remaining forward
prefix is the whole product. This preserves zero factors throughout
the reversal and uses the actual primitive-recursive product folds.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalProductReverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalFiniteProduct (qprod product_succ product_zero product_canonical product_index_congr)
open GaussianRationalHorner (qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reverseBody (t : PTm 2) : PTm 2 :=
  inst2 t (monus (fstT (var 1)) (succ (var 0))) (sndT (var 1))
def reversed (t : PTm 2) (N x k : PTm n) : PTm n := qprod (reverseBody t) k (pairT N x)

@[simp] theorem subst_reversed {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N x k : PTm n) :
    Syn.subst σ (reversed t N x k) = reversed t (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ k) := by
  simp [reversed]

theorem reverse_at (t : PTm 2) (N x k : PTm n) :
    Γ ⊢[PRAAx] inst2 (reverseBody t) k (pairT N x) ≐ inst2 t (monus N (succ k)) x := by
  change Γ ⊢[PRAAx] Syn.subst ![k,pairT N x]
    (inst2 t (monus (fstT (var 1)) (succ (var 0))) (sndT (var 1))) ≐ _
  simpa only [subst_inst2,PTm.subst_monus,ConciseIPRA.PTm.subst_succ,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    congrInst2 t (congrMonus (fst_pair (Γ := Γ) N x) (.eqRefl (succ k))) (snd_pair N x)

def prefixLaw (t : PTm 2) (N x k : PTm n) : Fm PTm n := le k N ⟶
  qmul (reversed t N x k) (qprod t (monus N k) x) ≐ qprod t N x

@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N x k : PTm n) :
    (prefixLaw t N x k).subst σ = prefixLaw t (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ k) := by
  simp [prefixLaw]

private theorem prefix_zero (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] prefixLaw t N x zero := by
  refine .impI ?_
  exact (qmul_congr (product_zero _ _) (product_index_congr t (monus_zero N) (.eqRefl _))).eqTrans
    ((qmul_commutative _ _).eqTrans (qmul_one_right _ (product_canonical _ _ _)))

private theorem prefix_succ (t : PTm 2) (N x k : PTm n) (h : Γ ⊢[PRAAx] prefixLaw t N x k) :
    Γ ⊢[PRAAx] prefixLaw t N x (succ k) := by
  refine .impI ?_
  let Δ := le (succ k) N :: Γ
  let r := monus N (succ k)
  let a := reversed t N x k
  let b := qprod t r x
  let v := inst2 t r x
  have step : Δ ⊢[PRAAx] lt k N := Prf.hyp0
  have rev : Δ ⊢[PRAAx] reversed t N x (succ k) ≐ qmul a v :=
    (product_succ (reverseBody t) k (pairT N x)).eqTrans (qmul_congr (.eqRefl _) (reverse_at t N x k))
  have rest : Δ ⊢[PRAAx] qprod t (monus N k) x ≐ qmul b v :=
    (product_index_congr t (GaussianRationalFiniteRoots.remaining_step N k step) (.eqRefl _)).eqTrans
      (product_succ t r x)
  have old := Prf.impE h.wk (le_of_lt step)
  exact (qmul_congr rev (.eqRefl _)).eqTrans
    ((qmul_associative a v b).eqTrans
      ((qmul_congr (.eqRefl _) ((qmul_commutative v b).eqTrans rest.eqSymm)).eqTrans old))

theorem prefix_all (t : PTm 2) (N x k : PTm n) : Γ ⊢[PRAAx] prefixLaw t N x k := by
  have h : Γ ⊢[PRAAx] .all (prefixLaw t (Syn.shift N) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) t N x
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ t (Syn.shift N) (Syn.shift x) (var 0) Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE k

theorem reverse_product (t : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] reversed t N x N ≐ qprod t N x := by
  have h := Prf.impE (prefix_all (Γ := Γ) t N x N) (le_refl N)
  exact (qmul_one_right _ (product_canonical _ _ _)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) ((product_index_congr t (monus_self N) (.eqRefl _)).eqTrans
      (product_zero t x)).eqSymm).eqTrans h)

theorem actual_rational_product_reversal_closed (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (reversed t (var 0) (var 1) (var 0) ≐ qprod t (var 0) (var 1)) :=
  closeUniv 2 (reverse_product t _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalProductReverse
