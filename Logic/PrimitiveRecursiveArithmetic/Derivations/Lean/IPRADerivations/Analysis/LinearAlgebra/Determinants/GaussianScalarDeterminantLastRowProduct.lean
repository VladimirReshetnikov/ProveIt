import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminant
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductDeletion
import IPRADerivations.Foundations.RuntimePermutationInsertion
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual Leibniz product on either side of a deleted column

For a word whose largest label is inserted at a bounded column, the
corresponding original product is the entry in its last row times the
actual product of the smaller word on the column-deleted matrix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLastRowProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (digit digit_bound)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (slot slot_bound subst_slot)
open LeanProofs.IPRA.Foundations.RuntimePermutationInsertion (insertedWord inserted_digit recovered_at recovered_skip)
open GaussianRationalFiberVandermonde (table table_lookup)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianScalarDeterminant (factorBody factorData rawProduct factor_body_at)
open GaussianRationalFiniteProduct (product_index_congr qprod)
open GaussianRationalProductDeletion (retainedValues product_remove)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def minorBody : PTm 3 := cell (fstT (var 2)) (var 0) (slot (sndT (var 2)) (var 1))
def minorTable (A m p : PTm n) : PTm n := table minorBody m m (pairT A p)

@[simp] theorem subst_minorTable {k : ℕ} (σ : Fin n → PTm k) (A m p : PTm n) :
    Syn.subst σ (minorTable A m p) = minorTable (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ p) := by
  simp [minorTable]

theorem cell_congr {A B i j k l : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B)
    (hi : Γ ⊢[PRAAx] i ≐ j) (hk : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx] cell A i k ≐ cell B j l := by
  ipra_congr (cell (var 0) (var 1) (var 2) : PTm 3) with [hA, hi, hk]

theorem minor_body_at (A p i j : PTm n) : Γ ⊢[PRAAx] inst3 minorBody i j (pairT A p) ≐ cell A i (slot p j) := by
  have e := LeanProofs.IPRA.Foundations.RuntimePermutationInsertion.slot_congr (snd_pair (Γ := Γ) A p) (.eqRefl j)
  simpa [minorBody,inst3] using cell_congr (fst_pair A p) (.eqRefl i) e

theorem minor_lookup (A m p i j : PTm n) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] cell (minorTable A m p) i j ≐ cell A i (slot p j) :=
  (table_lookup minorBody m m (pairT A p) i j hi hj).eqTrans (minor_body_at A p i j)

theorem inserted_factor (A m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    inst2 factorBody p (factorData A (succ m) (insertedWord m p d)) ≐ cell A m p := by
  have hit := (inserted_digit m p d p hp hp).eqTrans (recovered_at m p d p (.eqRefl _))
  exact (factor_body_at A (succ m) (insertedWord m p d) p).eqTrans (cell_congr (.eqRefl _) hit (.eqRefl _))

theorem retained_factor (A m p d j : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    inst2 factorBody j (factorData (minorTable A m p) m d) ≐
      inst2 factorBody (slot p j) (factorData A (succ m) (insertedWord m p d)) := by
  have original := factor_body_at (Γ := Γ) (minorTable A m p) m d j
  have small := minor_lookup A m p (digit m d j) j (digit_bound _ _ _ hj) hj
  have slotRead := (inserted_digit m p d (slot p j) hp (slot_bound m p j hj)).eqTrans (recovered_skip m p d j)
  have full := factor_body_at (Γ := Γ) A (succ m) (insertedWord m p d) (slot p j)
  exact original.eqTrans (small.eqTrans ((cell_congr (.eqRefl _) slotRead.eqSymm (.eqRefl _)).eqTrans full.eqSymm))

theorem last_row_product (A m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx]
    rawProduct A (succ m) (insertedWord m p d) ≐ qmul (cell A m p) (rawProduct (minorTable A m p) m d) := by
  let q := monus m p
  let x := factorData A (succ m) (insertedWord m p d)
  let y := factorData (minorTable A m p) m d
  have small : Γ ⊢[PRAAx] p+q ≐ m := (eq_add_of_le ((succ_monus_succ p m).eqSymm.eqTrans hp)).eqSymm
  have full : Γ ⊢[PRAAx] succ p+q ≐ succ m := (succ_add p q).eqTrans (congrSucc small)
  have retained : Γ ⊢[PRAAx] retainedValues factorBody factorBody (p+q) p x y := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let m' := Syn.shift m
    let p' := Syn.shift p
    let d' := Syn.shift d
    let Δ := lt (var 0) (Syn.shift (p+q)) :: Γ.map Fm.shift
    have hp' : Δ ⊢[PRAAx] lt p' (succ m') := by
      simpa only [Δ,p',m',Fm.shift,Syn.shift,subst_lt,ConciseIPRA.PTm.subst_succ] using hp.shift.wk
    have s : Δ ⊢[PRAAx] Syn.shift (p+q) ≐ m' := by
      simpa only [Δ,m',Fm.shift,Syn.shift,Fm.subst_eq] using small.shift.wk
    have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (p+q)) := Prf.hyp0
    simpa only [Δ,A',m',p',d',x,y,Syn.shift,GaussianScalarDeterminant.subst_factorData,subst_minorTable,
      LeanProofs.IPRA.Foundations.RuntimePermutationInsertion.subst_insertedWord,ConciseIPRA.PTm.subst_succ] using
      retained_factor A' m' p' d' (var 0) hp' (lt_congr (.eqRefl _) s hi)
  exact (product_index_congr factorBody full.eqSymm (.eqRefl x)).eqTrans
    ((product_remove factorBody factorBody p q x y retained).eqTrans
      (qmul_congr (inserted_factor A m p d hp) (product_index_congr factorBody small (.eqRefl y))))

theorem actual_last_row_minor_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ lt (var 4) (var 1) ⟶
      cell (minorTable (var 0) (var 1) (var 2)) (var 3) (var 4) ≐ cell (var 0) (var 3) (slot (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (minor_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_last_row_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (succ (var 1)) ⟶ rawProduct (var 0) (succ (var 1)) (insertedWord (var 1) (var 2) (var 3)) ≐
      qmul (cell (var 0) (var 1) (var 2)) (rawProduct (minorTable (var 0) (var 1) (var 2)) (var 1) (var 3))) :=
  closeUniv 4 (.impI (last_row_product _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLastRowProduct
