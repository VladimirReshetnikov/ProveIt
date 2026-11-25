import IPRADerivations.Algebra.QuadraticTowerGrowth
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Core.CongruenceTactic

/-!
# Bounded height verification for the actual five-call table

Original rational heights and stored constructors give a bounded table
invariant. Genuine reflected QF induction along the actual forward pass
proves it without a table-output premise. The actual computed be operand
then fits the preceding budget, and the exact third lower address is in
range. Cross-budget field properness and tower sign/order are separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationHeight

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width width_zero width_succ singleton)
open QuadraticTowerArrayCodec (arrayHeight height_at restored)
open QuadraticTowerScalarBudget (height amp growth codeCap height_congr height_mono)
open QuadraticTowerMultiplicationTable (leftHalf rightHalf)
open LeanProofs.IPRA.Foundations
open MasterCertificate (entry)
open SequenceComposition (length append entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem array_mono (h A b B : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hb : Γ ⊢[PRAAx] le b B) : Γ ⊢[PRAAx] arrayHeight h A B := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using ha.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hb.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,QuadraticTowerCoefficients.subst_width] using
    height_mono (entry (Syn.shift A) (var 0)) (Syn.shift b) (Syn.shift B)
      (height_at (Syn.shift h) (Syn.shift A) (Syn.shift b) (var 0) hs.wk Prf.hyp0) bs.wk

theorem restored_height (h A b B : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hb : Γ ⊢[PRAAx] le b B) : Γ ⊢[PRAAx] arrayHeight h (restored h A B) b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using ha.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hb.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have source := height_at (Syn.shift h) (Syn.shift A) (Syn.shift b) (var 0) hs.wk hi
  have eq := QuadraticTowerArrayCodec.restored_entry (Syn.shift h) (Syn.shift A) (Syn.shift B) (var 0)
    (array_mono _ _ _ _ hs.wk bs.wk) hi
  have result := height_congr eq.eqSymm (.eqRefl _) (QuadraticTowerScalarBudget.recode_height _ _ source)
  simpa only [Δ,Syn.shift,QuadraticTowerArrayCodec.subst_restored] using result

theorem left_height (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) :
    Γ ⊢[PRAAx] arrayHeight h (leftHalf h A) b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (succ (Syn.shift h)) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,ConciseIPRA.PTm.subst_succ,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have source := height_at (succ (Syn.shift h)) (Syn.shift A) (Syn.shift b) (var 0) hs.wk
    (lt_of_lt_of_le hi (QuadraticTowerCoefficientArithmetic.width_le_next _))
  have eq : Δ ⊢[PRAAx] entry (leftHalf (Syn.shift h) (Syn.shift A)) (var 0) ≐ entry (Syn.shift A) (var 0) :=
    (RealizerComposition.slice_lookup _ zero _ _ hi).eqTrans (entry_congr (.eqRefl _) (zero_add _))
  simpa only [Δ,Syn.shift,QuadraticTowerMultiplicationTable.subst_leftHalf] using height_congr eq.eqSymm (.eqRefl _) source

theorem right_height (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) :
    Γ ⊢[PRAAx] arrayHeight h (rightHalf h A) b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (succ (Syn.shift h)) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,ConciseIPRA.PTm.subst_succ,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have source := height_at (succ (Syn.shift h)) (Syn.shift A) (Syn.shift b)
    (width (Syn.shift h)+var 0) hs.wk (QuadraticTowerCoefficientArithmetic.right_half_bound _ _ hi)
  have eq : Δ ⊢[PRAAx] entry (rightHalf (Syn.shift h) (Syn.shift A)) (var 0) ≐
      entry (Syn.shift A) (width (Syn.shift h)+var 0) := RealizerComposition.slice_lookup _ _ _ _ hi
  simpa only [Δ,Syn.shift,QuadraticTowerMultiplicationTable.subst_rightHalf] using height_congr eq.eqSymm (.eqRefl _) source

theorem added_height (h A C b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) :
    Γ ⊢[PRAAx] arrayHeight h (QuadraticTowerCoefficientArithmetic.added h A C) (amp b) := by
  have as' : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using ha.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift C) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using hc.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have scalar := QuadraticTowerScalarBudget.add_height _ _ _
    (height_at (Syn.shift h) (Syn.shift A) (Syn.shift b) (var 0) as'.wk hi)
    (height_at (Syn.shift h) (Syn.shift C) (Syn.shift b) (var 0) cs.wk hi)
  have eq := QuadraticTowerCoefficientArithmetic.added_lookup (Syn.shift h) (Syn.shift A) (Syn.shift C) (var 0) hi
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficientArithmetic.subst_added,QuadraticTowerScalarBudget.subst_amp] using
    height_congr eq.eqSymm (.eqRefl _) scalar

theorem right_index_bound (W i : PTm n) (hi : Γ ⊢[PRAAx] lt i (W+W)) (hw : Γ ⊢[PRAAx] le W i) :
    Γ ⊢[PRAAx] lt (monus i W) W := by
  have e := (congrSucc (eq_add_of_le hw)).eqTrans
    (by ipra_ring : Γ ⊢[PRAAx] succ (W+monus i W) ≐ succ (monus i W)+W)
  exact le_of_add_le_add_right (c := W) (le_congr e (.eqRefl _) hi)

theorem append_height_at (h A C b i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hC : Γ ⊢[PRAAx] length C ≐ width h) (hi : Γ ⊢[PRAAx] lt i (width (succ h))) :
    Γ ⊢[PRAAx] height (entry (append A C) i) b := by
  refine .orE (lt_or_le i (width h)) ?_ ?_
  · have e : ((lt i (width h)) :: Γ) ⊢[PRAAx] entry (append A C) i ≐ entry A i :=
      SequenceComposition.append_left (lt_congr (.eqRefl _) hA.wk.eqSymm Prf.hyp0)
    exact height_congr e.eqSymm (.eqRefl _) (height_at h A b i ha.wk Prf.hyp0)
  · have hj := right_index_bound (width h) i (lt_congr (.eqRefl _) (width_succ h) hi.wk) Prf.hyp0
    have e := entry_congr (Γ := le (width h) i :: Γ) (.eqRefl (append A C))
      ((eq_add_of_le Prf.hyp0).eqTrans (congrAdd hA.wk.eqSymm (.eqRefl _)))
    have eq := e.eqTrans (SequenceComposition.append_right (lt_congr (.eqRefl _) hC.wk.eqSymm hj))
    exact height_congr eq.eqSymm (.eqRefl _) (height_at h C b (monus i (width h)) hc.wk hj)

theorem append_height (h A C b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (hA : Γ ⊢[PRAAx] length A ≐ width h)
    (hC : Γ ⊢[PRAAx] length C ≐ width h) : Γ ⊢[PRAAx] arrayHeight (succ h) (append A C) b := by
  have as' : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using ha.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift C) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerArrayCodec.subst_arrayHeight,Syn.shift] using hc.shift
  have als : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift A) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hA.shift
  have cls : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ width (Syn.shift h) := by simpa only [Fm.shift,Fm.subst_eq,SequenceComposition.subst_length,QuadraticTowerCoefficients.subst_width,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,SequenceComposition.subst_append,ConciseIPRA.PTm.subst_succ] using
    append_height_at (Syn.shift h) (Syn.shift A) (Syn.shift C) (Syn.shift b) (var 0) as'.wk cs.wk als.wk cls.wk Prf.hyp0

def radicandsHeight (D h b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift h) ⟶ arrayHeight (var 0) (entry (Syn.shift D) (var 0)) (Syn.shift b))
@[simp] theorem subst_radicandsHeight {k : ℕ} (σ : Fin n → PTm k) (D h b : PTm n) :
    (radicandsHeight D h b).subst σ = radicandsHeight (Syn.subst σ D) (Syn.subst σ h) (Syn.subst σ b) := by
  simp [radicandsHeight,Syn.subst_shift,Syn.shift_subst]
theorem radicand_at (D h b j : PTm n) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (hj : Γ ⊢[PRAAx] lt j h) : Γ ⊢[PRAAx] arrayHeight j (entry D j) b := by
  have gate : Γ ⊢[PRAAx] lt j h ⟶ arrayHeight j (entry D j) b := by simpa [radicandsHeight] using hD.allE j
  exact .impE gate hj
theorem radicands_prefix (D h H b : PTm n) (hD : Γ ⊢[PRAAx] radicandsHeight D H b)
    (hh : Γ ⊢[PRAAx] le h H) : Γ ⊢[PRAAx] radicandsHeight D h b := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] radicandsHeight (Syn.shift D) (Syn.shift H) (Syn.shift b) := by
    simpa only [Fm.shift,subst_radicandsHeight,Syn.shift] using hD.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift h) (Syn.shift H) := by simpa only [Fm.shift,subst_le,Syn.shift] using hh.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift h) :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift h) := Prf.hyp0
  simpa only [Δ,Syn.shift] using radicand_at (Γ := Δ) (Syn.shift D) (Syn.shift H) (Syn.shift b) (var 0) ds.wk (le_trans hj hs.wk)
theorem radicands_mono (D h b B : PTm n) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (hb : Γ ⊢[PRAAx] le b B) : Γ ⊢[PRAAx] radicandsHeight D h B := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] radicandsHeight (Syn.shift D) (Syn.shift h) (Syn.shift b) := by
    simpa only [Fm.shift,subst_radicandsHeight,Syn.shift] using hD.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift B) := by simpa only [Fm.shift,subst_le,Syn.shift] using hb.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift] using array_mono (var 0) (entry (Syn.shift D) (var 0)) (Syn.shift b) (Syn.shift B)
    (radicand_at (Syn.shift D) (Syn.shift h) (Syn.shift b) (var 0) ds.wk Prf.hyp0) bs.wk

open BoundedSyntax (BFm formula)
open QuadraticTowerMultiplicationTable (rows lookup budget)
open QuadraticTowerGrowth (path)

def word (h B u : PTm n) : PTm n := QuadraticTowerArrayCodec.decoded (width h) (codeCap B) u
def rowIndex (h B u v : PTm n) : PTm n := u*QuadraticTowerArrayCodec.horizon h B+v
def rowLaw (h B D T b u v : PTm n) : Fm PTm n := radicandsHeight D h b ⟶
  arrayHeight h (word h B u) b ⟶ arrayHeight h (word h B v) b ⟶
    arrayHeight h (entry T (rowIndex h B u v)) (growth (path h) b)
def atWord (h B D T b u : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (QuadraticTowerArrayCodec.horizon h B)) ⟶ rowLaw (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (var 0))
def atHeight (h B D T b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (QuadraticTowerArrayCodec.horizon h B)) ⟶ atWord (Syn.shift h) (Syn.shift B)
    (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localLaw (h B D T : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ atHeight (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (var 0))

@[simp] theorem subst_word {k : ℕ} (σ : Fin n → PTm k) (h B u : PTm n) :
    Syn.subst σ (word h B u) = word (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ u) := by simp [word]
@[simp] theorem subst_rowIndex {k : ℕ} (σ : Fin n → PTm k) (h B u v : PTm n) :
    Syn.subst σ (rowIndex h B u v) = rowIndex (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ u) (Syn.subst σ v) := by simp [rowIndex]
@[simp] theorem subst_rowLaw {k : ℕ} (σ : Fin n → PTm k) (h B D T b u v : PTm n) :
    (rowLaw h B D T b u v).subst σ = rowLaw (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) (Syn.subst σ u) (Syn.subst σ v) := by simp [rowLaw]
@[simp] theorem subst_atWord {k : ℕ} (σ : Fin n → PTm k) (h B D T b u : PTm n) :
    (atWord h B D T b u).subst σ = atWord (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) (Syn.subst σ u) := by
  simp [atWord,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
@[simp] theorem subst_atHeight {k : ℕ} (σ : Fin n → PTm k) (h B D T b : PTm n) :
    (atHeight h B D T b).subst σ = atHeight (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D)
      (Syn.subst σ T) (Syn.subst σ b) := by
  simp [atHeight,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
@[simp] theorem subst_localLaw {k : ℕ} (σ : Fin n → PTm k) (h B D T : PTm n) :
    (localLaw h B D T).subst σ = localLaw (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ T) := by
  simp [localLaw,Syn.subst_shift,Syn.shift_subst]

def heightSyntax (h A b : PTm n) : BFm n := .all (width h) (.and
  (.le (Foundations.GapDecision.zabs (RationalSupMetric.numeratorOf (entry (Syn.shift A) (var 0)))) (Syn.shift b))
  (.le (RationalSupMetric.denominatorOf (entry (Syn.shift A) (var 0))) (Syn.shift b)))
def radicandsSyntax (D h b : PTm n) : BFm n := .all h
  (heightSyntax (var 0) (entry (Syn.shift D) (var 0)) (Syn.shift b))
def rowSyntax (h B D T b u v : PTm n) : BFm n := .imp (radicandsSyntax D h b)
  (.imp (heightSyntax h (word h B u) b) (.imp (heightSyntax h (word h B v) b)
    (heightSyntax h (entry T (rowIndex h B u v)) (growth (path h) b))))
def wordSyntax (h B D T b u : PTm n) : BFm n := .all (QuadraticTowerArrayCodec.horizon h B)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (Syn.shift u) (var 0))
def heightRowsSyntax (h B D T b : PTm n) : BFm n := .all (QuadraticTowerArrayCodec.horizon h B)
  (wordSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (Syn.shift b) (var 0))
def localSyntax (h B D T : PTm n) : BFm n := .all (succ B)
  (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift T) (var 0))
theorem height_formula (h A b : PTm n) : formula (heightSyntax h A b) = arrayHeight h A b := by
  simp [heightSyntax,arrayHeight,formula,height,BFm.le,le,Syn.shift]
theorem radicands_formula (D h b : PTm n) : formula (radicandsSyntax D h b) = radicandsHeight D h b := by
  simp [radicandsSyntax,radicandsHeight,formula,height_formula]
theorem row_formula (h B D T b u v : PTm n) : formula (rowSyntax h B D T b u v) = rowLaw h B D T b u v := by
  simp [rowSyntax,rowLaw,formula,radicands_formula,height_formula]
theorem word_formula (h B D T b u : PTm n) : formula (wordSyntax h B D T b u) = atWord h B D T b u := by
  simp [wordSyntax,atWord,formula,row_formula]
theorem height_rows_formula (h B D T b : PTm n) : formula (heightRowsSyntax h B D T b) = atHeight h B D T b := by
  simp [heightRowsSyntax,atHeight,formula,word_formula]
theorem local_formula (h B D T : PTm n) : formula (localSyntax h B D T) = localLaw h B D T := by
  simp [localSyntax,localLaw,formula,height_rows_formula,Syn.shift]

theorem local_at (h B D T b u v : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hu : Γ ⊢[PRAAx] lt u (QuadraticTowerArrayCodec.horizon h B))
    (hv : Γ ⊢[PRAAx] lt v (QuadraticTowerArrayCodec.horizon h B))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h B u) b)
    (hc : Γ ⊢[PRAAx] arrayHeight h (word h B v) b) :
    Γ ⊢[PRAAx] arrayHeight h (entry T (rowIndex h B u v)) (growth (path h) b) := by
  have bGate : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D T b := by simpa [localLaw] using hL.allE b
  have uGate : Γ ⊢[PRAAx] lt u (QuadraticTowerArrayCodec.horizon h B) ⟶ atWord h B D T b u := by
    simpa [atHeight] using (Prf.impE bGate ((succ_monus_succ _ _).eqTrans hb)).allE u
  have vGate : Γ ⊢[PRAAx] lt v (QuadraticTowerArrayCodec.horizon h B) ⟶ rowLaw h B D T b u v := by
    simpa [atWord] using (Prf.impE uGate hu).allE v
  exact .impE (.impE (.impE (.impE vGate hv) hD) ha) hc

theorem lookup_height (h B D T A C b : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D T)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b)
    (ha : Γ ⊢[PRAAx] arrayHeight h A b) (hc : Γ ⊢[PRAAx] arrayHeight h C b) :
    Γ ⊢[PRAAx] arrayHeight h (lookup h B T A C) (growth (path h) b) :=
  local_at h B D T b (QuadraticTowerArrayCodec.code h A B) (QuadraticTowerArrayCodec.code h C B) hL hb
    (QuadraticTowerArrayCodec.code_bound h A B (array_mono h A b B ha hb))
    (QuadraticTowerArrayCodec.code_bound h C B (array_mono h C b B hc hb)) hD
    (restored_height h A b B ha hb) (restored_height h C b B hc hb)

theorem array_congr {h h' A A' b b' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (ha : Γ ⊢[PRAAx] A ≐ A') (hb : Γ ⊢[PRAAx] b ≐ b') (hA : Γ ⊢[PRAAx] arrayHeight h A b) :
    Γ ⊢[PRAAx] arrayHeight h' A' b' := by
  have proof := Prf.eqSubst (arrayHeight (var 0) (var 1) (var 2) : Fm PTm 3)
    ![h,A,b] ![h',A',b'] (fun i => by fin_cases i; exact hh; exact ha; exact hb) (by simpa using hA)
  simpa using proof

/-- The lower object contract, rather than an external rule bundle, yields
the actual be height before it is passed to the third lower lookup. -/
theorem recipe_be_height (h B D T A C b : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight h (lookup h (budget h B D) T (rightHalf h A) (rightHalf h C)) (growth (path h) b) := by
  have bK := le_trans (QuadraticTowerGrowth.growth_inflation (path h) b)
    (QuadraticTowerGrowth.lower_path_budget h B D b hb)
  exact lookup_height h (budget h B D) D T (rightHalf h A) (rightHalf h C) b hL bK
    (radicands_prefix D h (succ h) b hD (le_succ_self h)) (right_height h A b ha) (right_height h C b hc)

theorem recipe_height (h B D T A C b : PTm n)
    (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight (succ h) (QuadraticTowerMultiplicationTable.recipe h B T D A C)
      (growth (path (succ h)) b) := by
  let K := budget h B D
  let g := growth (path h) b
  let g2 := growth (path h) g
  let ac := lookup h K T (leftHalf h A) (leftHalf h C)
  let be := lookup h K T (rightHalf h A) (rightHalf h C)
  let bed := lookup h K T be (entry D h)
  let ae := lookup h K T (leftHalf h A) (rightHalf h C)
  let bc := lookup h K T (rightHalf h A) (leftHalf h C)
  have bg : Γ ⊢[PRAAx] le b g := QuadraticTowerGrowth.growth_inflation _ _
  have gK : Γ ⊢[PRAAx] le g K := QuadraticTowerGrowth.lower_path_budget h B D b hb
  have bK := le_trans bg gK
  have rh := radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := left_height h A b ha
  have a1 := right_height h A b ha
  have c0 := left_height h C b hc
  have c1 := right_height h C b hc
  have acH : Γ ⊢[PRAAx] arrayHeight h ac g := lookup_height h K D T _ _ b hL bK rh a0 c0
  have beH : Γ ⊢[PRAAx] arrayHeight h be g := lookup_height h K D T _ _ b hL bK rh a1 c1
  have aeH : Γ ⊢[PRAAx] arrayHeight h ae g := lookup_height h K D T _ _ b hL bK rh a0 c1
  have bcH : Γ ⊢[PRAAx] arrayHeight h bc g := lookup_height h K D T _ _ b hL bK rh a1 c0
  have dH : Γ ⊢[PRAAx] arrayHeight h (entry D h) g :=
    array_mono h (entry D h) b g (radicand_at D (succ h) b h hD (le_refl _)) bg
  have bedH : Γ ⊢[PRAAx] arrayHeight h bed g2 := lookup_height h K D T _ _ g hL gK
    (radicands_mono D h b g rh bg) beH dH
  have gg : Γ ⊢[PRAAx] le g g2 := QuadraticTowerGrowth.growth_inflation _ _
  have left := added_height h ac bed g2 (array_mono h ac g g2 acH gg) bedH
  have right := added_height h ae bc g2 (array_mono h ae g g2 aeH gg) (array_mono h bc g g2 bcH gg)
  have joined := append_height h _ _ (amp g2) left right
    (QuadraticTowerCoefficientArithmetic.added_length _ _ _) (QuadraticTowerCoefficientArithmetic.added_length _ _ _)
  exact array_congr (.eqRefl _) (.eqRefl _) (QuadraticTowerGrowth.twice_then_add h b) joined

theorem row_index_bound (h B u v : PTm n)
    (hu : Γ ⊢[PRAAx] lt u (QuadraticTowerArrayCodec.horizon h B))
    (hv : Γ ⊢[PRAAx] lt v (QuadraticTowerArrayCodec.horizon h B)) :
    Γ ⊢[PRAAx] lt (rowIndex h B u v) (rows h B) :=
  lt_congr (by unfold rowIndex; ipra_ring) (.eqRefl _) (MixedRadixExpansion.append_interval hv hu)
theorem row_at_words (h B T D u v : PTm n)
    (hv : Γ ⊢[PRAAx] lt v (QuadraticTowerArrayCodec.horizon (succ h) B)) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.rowValue h B T D (rowIndex (succ h) B u v) ≐
      QuadraticTowerMultiplicationTable.recipe h B T D (word (succ h) B u) (word (succ h) B v) := by
  have parts := RuntimeWordAppend.divide_unique _ (rowIndex (succ h) B u v) u v
    (QuadraticTowerMultiplicationTable.horizon_positive (succ h) B) (by unfold rowIndex; ipra_ring) hv
  exact QuadraticTowerMultiplicationTable.recipe_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (QuadraticTowerMultiplicationTable.decoded_congr (.eqRefl _) (.eqRefl _) (Prf.andE₁ parts))
    (QuadraticTowerMultiplicationTable.decoded_congr (.eqRefl _) (.eqRefl _) (Prf.andE₂ parts))

theorem local_step (h B D T : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D T) :
    Γ ⊢[PRAAx] localLaw (succ h) B D (QuadraticTowerMultiplicationTable.step h B T D) := by
  have ls : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      localLaw (Syn.shift (Syn.shift (Syn.shift h)))
        (budget (Syn.shift (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift (Syn.shift B))) (Syn.shift (Syn.shift (Syn.shift D))))
        (Syn.shift (Syn.shift (Syn.shift D))) (Syn.shift (Syn.shift (Syn.shift T))) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift.shift
  refine .allI (.impI (.allI (.impI (.allI (.impI (.impI (.impI (.impI ?_))))))))
  let h' := Syn.shift (Syn.shift (Syn.shift h))
  let B' := Syn.shift (Syn.shift (Syn.shift B))
  let D' := Syn.shift (Syn.shift (Syn.shift D))
  let T' := Syn.shift (Syn.shift (Syn.shift T))
  let b := (var 2 : PTm (n+3))
  let u := (var 1 : PTm (n+3))
  let v := (var 0 : PTm (n+3))
  let R := QuadraticTowerArrayCodec.horizon (succ h') B'
  let Δ := arrayHeight (succ h') (word (succ h') B' v) b ::
    arrayHeight (succ h') (word (succ h') B' u) b :: radicandsHeight D' (succ h') b ::
    lt v R :: lt u R :: lt b (succ B') :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') B' u) b := .hyp (by simp [Δ])
  have hc : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') B' v) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hu : Δ ⊢[PRAAx] lt u R := .hyp (by simp [Δ])
  have hv : Δ ⊢[PRAAx] lt v R := .hyp (by simp [Δ])
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' T' :=
    ls.wk.wk.wk.wk.wk.wk
  have computed := recipe_height h' B' D' T' (word (succ h') B' u) (word (succ h') B' v) b lower hb hd ha hc
  have stored : Δ ⊢[PRAAx] entry (QuadraticTowerMultiplicationTable.step h' B' T' D') (rowIndex (succ h') B' u v) ≐
      QuadraticTowerMultiplicationTable.recipe h' B' T' D' (word (succ h') B' u) (word (succ h') B' v) :=
    (QuadraticTowerMultiplicationTable.step_lookup h' B' T' D' _ (row_index_bound _ _ _ _ hu hv)).eqTrans
      (row_at_words _ _ _ _ _ _ hv)
  have result := array_congr (.eqRefl _) stored.eqSymm (.eqRefl _) computed
  simpa [Δ,h',B',D',T',b,u,v,R,Fm.shift,Syn.shift] using result

theorem singleton_height (q b : PTm n) (hq : Γ ⊢[PRAAx] height q b) :
    Γ ⊢[PRAAx] arrayHeight zero (singleton q) b := by
  have qs : Γ.map Fm.shift ⊢[PRAAx] height (Syn.shift q) (Syn.shift b) := by
    simpa only [Fm.shift,QuadraticTowerScalarBudget.subst_height,Syn.shift] using hq.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (zero : PTm (n+1))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (zero : PTm (n+1))) := Prf.hyp0
  have iz : Δ ⊢[PRAAx] le (var 0) zero :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) width_zero hi)
  have eq : Δ ⊢[PRAAx] entry (singleton (Syn.shift q)) (var 0) ≐ Syn.shift q :=
    (entry_congr (.eqRefl _) (le_antisymm iz (zero_le _))).eqTrans (QuadraticTowerCoefficients.singleton_entry _)
  simpa [Δ,Fm.shift,Syn.shift] using height_congr eq.eqSymm (.eqRefl _) qs.wk

theorem word_zero_lookup (B u : PTm n) : Γ ⊢[PRAAx] entry (word zero B u) zero ≐
    QuadraticTowerArrayCodec.digit (codeCap B) u zero :=
  QuadraticTowerArrayCodec.decoded_lookup _ _ _ _
    (lt_congr (.eqRefl _) width_zero.eqSymm (zero_lt_succ zero))
theorem base_row_at_words (B u v : PTm n)
    (hv : Γ ⊢[PRAAx] lt v (QuadraticTowerArrayCodec.horizon zero B)) : Γ ⊢[PRAAx]
    QuadraticTowerMultiplicationTable.baseRow B (rowIndex zero B u v) ≐ singleton (RationalArithmetic.multiply
      (QuadraticTowerArrayCodec.digit (codeCap B) u zero) (QuadraticTowerArrayCodec.digit (codeCap B) v zero)) := by
  have parts := RuntimeWordAppend.divide_unique _ (rowIndex zero B u v) u v
    (QuadraticTowerMultiplicationTable.horizon_positive zero B) (by unfold rowIndex; ipra_ring) hv
  have dig (w w' : PTm n) (hw : Γ ⊢[PRAAx] w ≐ w') : Γ ⊢[PRAAx]
      QuadraticTowerArrayCodec.digit (codeCap B) w zero ≐ QuadraticTowerArrayCodec.digit (codeCap B) w' zero :=
    congrAp2 remF (congrAp2 quoF hw (.eqRefl _)) (.eqRefl _)
  have scalar := RationalAlgebra.multiply_congr (dig _ _ (Prf.andE₁ parts)) (dig _ _ (Prf.andE₂ parts))
  ipra_congr (singleton (var 0) : PTm 1) with [scalar] using [QuadraticTowerMultiplicationTable.baseRow]

theorem base_height_at (B _D b u v : PTm n)
    (hu : Γ ⊢[PRAAx] lt u (QuadraticTowerArrayCodec.horizon zero B))
    (hv : Γ ⊢[PRAAx] lt v (QuadraticTowerArrayCodec.horizon zero B))
    (ha : Γ ⊢[PRAAx] arrayHeight zero (word zero B u) b)
    (hc : Γ ⊢[PRAAx] arrayHeight zero (word zero B v) b) : Γ ⊢[PRAAx]
    arrayHeight zero (entry (QuadraticTowerMultiplicationTable.base B) (rowIndex zero B u v)) (growth (path zero) b) := by
  have hi : Γ ⊢[PRAAx] lt (zero : PTm n) (width zero) :=
    lt_congr (.eqRefl _) width_zero.eqSymm (zero_lt_succ zero)
  have aH := height_congr (word_zero_lookup B u) (.eqRefl _) (height_at zero _ b zero ha hi)
  have cH := height_congr (word_zero_lookup B v) (.eqRefl _) (height_at zero _ b zero hc hi)
  have scalar := height_mono _ (b*b) (amp b) (QuadraticTowerScalarBudget.multiply_height _ _ _ aH cH)
    (QuadraticTowerScalarBudget.square_le_amp b)
  have growthEq : Γ ⊢[PRAAx] growth (path zero) b ≐ amp b :=
    (QuadraticTowerGrowth.growth_congr QuadraticTowerGrowth.path_zero (.eqRefl _)).eqTrans
      ((QuadraticTowerScalarBudget.growth_succ zero b).eqTrans
        (QuadraticTowerGrowth.amp_congr (QuadraticTowerScalarBudget.growth_zero b)))
  have single := singleton_height _ _ (height_congr (.eqRefl _) growthEq.eqSymm scalar)
  have stored := (QuadraticTowerMultiplicationTable.base_lookup B _ (row_index_bound zero B u v hu hv)).eqTrans
    (base_row_at_words B u v hv)
  exact array_congr (.eqRefl _) stored.eqSymm (.eqRefl _) single

theorem local_base (B D : PTm n) : Γ ⊢[PRAAx] localLaw zero B D (QuadraticTowerMultiplicationTable.base B) := by
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .allI (.impI ?_)
  refine .impI (.impI (.impI ?_))
  let B' := Syn.shift (Syn.shift (Syn.shift B))
  let D' := Syn.shift (Syn.shift (Syn.shift D))
  let b := (var 2 : PTm (n+3))
  let u := (var 1 : PTm (n+3))
  let v := (var 0 : PTm (n+3))
  let R := QuadraticTowerArrayCodec.horizon zero B'
  let Δ := arrayHeight zero (word zero B' v) b :: arrayHeight zero (word zero B' u) b ::
    radicandsHeight D' zero b :: lt v R :: lt u R :: lt b (succ B') ::
      ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero B' u) b := .hyp (by simp [Δ])
  have hc : Δ ⊢[PRAAx] arrayHeight zero (word zero B' v) b := Prf.hyp0
  have hu : Δ ⊢[PRAAx] lt u R := .hyp (by simp [Δ])
  have hv : Δ ⊢[PRAAx] lt v R := .hyp (by simp [Δ])
  simpa [Δ,B',D',b,u,v,R,Fm.shift,Syn.shift] using base_height_at (Γ := Δ) B' D' b u v hu hv ha hc

theorem local_congr {h h' B B' D D' T T' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h')
    (hb : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] D ≐ D') (ht : Γ ⊢[PRAAx] T ≐ T')
    (hL : Γ ⊢[PRAAx] localLaw h B D T) : Γ ⊢[PRAAx] localLaw h' B' D' T' := by
  have proof := Prf.eqSubst (localLaw (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![h,B,D,T] ![h',B',D',T'] (fun i => by fin_cases i; exact hh; exact hb; exact hd; exact ht) (by simpa using hL)
  simpa using proof

open QuadraticTowerMultiplicationTable (demandF baseSchema stepSchema table)

def cap (H B t D : PTm n) : PTm n := BackwardDemand.horizon demandF H B t D
def state (H B t D : PTm n) : PTm n := DemandRecursion.V demandF baseSchema stepSchema H B t D
def forwardLaw (H B D t : PTm n) : Fm PTm n := le t H ⟶ localLaw t (cap H B t D) D (state H B t D)
def forwardSyntax (H B D t : PTm n) : BFm n := .imp (.le t H)
  (localSyntax t (cap H B t D) D (state H B t D))
@[simp] theorem subst_cap {k : ℕ} (σ : Fin n → PTm k) (H B t D : PTm n) :
    Syn.subst σ (cap H B t D) = cap (Syn.subst σ H) (Syn.subst σ B) (Syn.subst σ t) (Syn.subst σ D) := by
  simp [cap]
@[simp] theorem subst_state {k : ℕ} (σ : Fin n → PTm k) (H B t D : PTm n) :
    Syn.subst σ (state H B t D) = state (Syn.subst σ H) (Syn.subst σ B) (Syn.subst σ t) (Syn.subst σ D) := by
  simp [state]
@[simp] theorem subst_forwardLaw {k : ℕ} (σ : Fin n → PTm k) (H B D t : PTm n) :
    (forwardLaw H B D t).subst σ = forwardLaw (Syn.subst σ H) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ t) := by
  simp [forwardLaw]
theorem forward_formula (H B D t : PTm n) : formula (forwardSyntax H B D t) = forwardLaw H B D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem state_zero (H B D : PTm n) : Γ ⊢[PRAAx] state H B zero D ≐ QuadraticTowerMultiplicationTable.base (cap H B zero D) := by
  simpa only [state,cap,baseSchema,inst2,QuadraticTowerMultiplicationTable.subst_base,Syn.subst_var,Matrix.cons_val_zero] using
    DemandRecursion.V_zero (Γ := Γ) demandF baseSchema stepSchema H B D
theorem state_succ (H B t D : PTm n) : Γ ⊢[PRAAx] state H B (succ t) D ≐
    QuadraticTowerMultiplicationTable.step t (cap H B (succ t) D) (state H B t D) D := by
  simpa only [state,cap,DemandRecursion.appF,stepSchema,QuadraticTowerMultiplicationTable.subst_step,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    DemandRecursion.V_succ (Γ := Γ) demandF baseSchema stepSchema H B t D
theorem cap_link (H B t D : PTm n) (ht : Γ ⊢[PRAAx] lt t H) :
    Γ ⊢[PRAAx] cap H B t D ≐ budget t (cap H B (succ t) D) D :=
  BackwardDemand.horizon_step demandF H B t D ht
theorem forward_zero (H B D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (state_zero H B D).wk.eqSymm (local_base _ D))
theorem forward_step (H B D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B D t) :
    Γ ⊢[PRAAx] forwardLaw H B D (succ t) := by
  refine .impI ?_
  let Δ := le (succ t) H :: Γ
  have ht : Δ ⊢[PRAAx] lt t H := Prf.hyp0
  have previous : Δ ⊢[PRAAx] localLaw t (cap H B t D) D (state H B t D) :=
    .impE ih.wk (le_trans (le_succ_self t) ht)
  have adjusted : Δ ⊢[PRAAx] localLaw t (budget t (cap H B (succ t) D) D) D (state H B t D) :=
    local_congr (.eqRefl _) (cap_link H B t D ht) (.eqRefl _) (.eqRefl _) previous
  have next := local_step t (cap H B (succ t) D) D (state H B t D) adjusted
  exact local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (state_succ H B t D).eqSymm next

/-- Every loop invariant is the reflection of one fixed bounded syntax.
Only the forward counter is used for ordinary QF induction. -/
theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine BoundedSyntaxInduction.induction _ ?_ ?_
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      forward_zero (Γ := Γ) H B D
  · simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Γ := formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)) :: Γ.map Fm.shift)
        (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0)
        (by simpa only [forward_formula] using (Prf.hyp0 (Ax := PRAAx)))

theorem table_height_law (h B D : PTm n) : Γ ⊢[PRAAx] localLaw h B D (table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      (forward_all (Γ := Γ) h B D).allE h
  have terminal : Γ ⊢[PRAAx] localLaw h (cap h B h D) D (state h B h D) := .impE gate (le_refl h)
  exact local_congr (.eqRefl _) (BackwardDemand.horizon_final demandF h B D) (.eqRefl _) (.eqRefl _) terminal

open QuadraticTowerMultiplicationTable (query computedBe computedBed operandsF returned_be returned_bed)

theorem query_height (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) :
    Γ ⊢[PRAAx] arrayHeight h (query h B D A C) (growth (path h) b) :=
  lookup_height h B D (table h B D) A C b (table_height_law h B D) hb hD ha hc

/-- Original input heights suffice; no output-height or table law is an
assumption. In particular this binds the actual computed third operand. -/
theorem computed_be_height (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight h (computedBe h B D A C) (growth (path h) b) :=
  recipe_be_height h B D (table h (budget h B D) D) (restored (succ h) A B) (restored (succ h) C B) b
    (table_height_law h (budget h B D) D) hb hD (restored_height _ _ _ _ ha hb) (restored_height _ _ _ _ hc hb)
theorem computed_be_fits (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight h (computedBe h B D A C) (budget h B D) :=
  array_mono h _ _ _ (computed_be_height h B D A C b hb hD ha hc) (QuadraticTowerGrowth.lower_path_budget h B D b hb)
theorem third_query_address (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) : Γ ⊢[PRAAx]
    lt (QuadraticTowerMultiplicationTable.address h (budget h B D) (computedBe h B D A C) (entry D h)) (rows h (budget h B D)) := by
  have bK := le_trans (QuadraticTowerGrowth.growth_inflation (path h) b) (QuadraticTowerGrowth.lower_path_budget h B D b hb)
  exact QuadraticTowerMultiplicationTable.address_bound h (budget h B D) _ _
    (computed_be_fits h B D A C b hb hD ha hc)
    (array_mono h (entry D h) b _ (radicand_at D (succ h) b h hD (le_refl _)) bK)
theorem computed_bed_height (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight h (computedBed h B D A C) (growth (path h) (growth (path h) b)) :=
  query_height h (budget h B D) D (computedBe h B D A C) (entry D h) (growth (path h) b)
    (QuadraticTowerGrowth.lower_path_budget h B D b hb)
    (radicands_mono D h b _ (radicands_prefix D h (succ h) b hD (le_succ_self h)) (QuadraticTowerGrowth.growth_inflation _ _))
    (computed_be_height h B D A C b hb hD ha hc)
    (array_mono h (entry D h) b _ (radicand_at D (succ h) b h hD (le_refl _)) (QuadraticTowerGrowth.growth_inflation _ _))

theorem returned_be_fits (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight h (fstT (PTm.app operandsF ![h,B,D,A,C])) (budget h B D) :=
  array_congr (.eqRefl _) (returned_be h B D A C).eqSymm (.eqRefl _) (computed_be_fits h B D A C b hb hD ha hc)
theorem returned_bed_height (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hc : Γ ⊢[PRAAx] arrayHeight (succ h) C b) :
    Γ ⊢[PRAAx] arrayHeight h (sndT (PTm.app operandsF ![h,B,D,A,C])) (growth (path h) (growth (path h) b)) :=
  array_congr (.eqRefl _) (returned_bed h B D A C).eqSymm (.eqRefl _) (computed_bed_height h B D A C b hb hD ha hc)

theorem actual_bounded_table_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (table (var 0) (var 1) (var 2))) := closeUniv 3 (table_height_law _ _ _)
theorem actual_forward_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 0) ⟶ localLaw (var 3) (cap (var 0) (var 1) (var 3) (var 2)) (var 2)
      (state (var 0) (var 1) (var 3) (var 2))) := by
  have all := forward_all (Γ := ([] : List (Fm PTm 4))) (var 0) (var 1) (var 2)
  have result : ([] : List (Fm PTm 4)) ⊢[PRAAx] forwardLaw (var 0) (var 1) (var 2) (var 3) := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE (var 3)
  exact closeUniv 4 result
theorem actual_original_query_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (var 0) (var 5) ⟶ arrayHeight (var 0) (var 3) (var 5) ⟶
      arrayHeight (var 0) (var 4) (var 5) ⟶ arrayHeight (var 0) (query (var 0) (var 1) (var 2) (var 3) (var 4))
        (growth (path (var 0)) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (query_height _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_computed_be_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶ arrayHeight (succ (var 0)) (var 3) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶ arrayHeight (var 0) (computedBe (var 0) (var 1) (var 2) (var 3) (var 4))
        (growth (path (var 0)) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (computed_be_height _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_computed_be_fits_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶ arrayHeight (succ (var 0)) (var 3) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶ arrayHeight (var 0) (computedBe (var 0) (var 1) (var 2) (var 3) (var 4))
        (budget (var 0) (var 1) (var 2))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (computed_be_fits _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_third_lower_query_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶ arrayHeight (succ (var 0)) (var 3) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶ lt (QuadraticTowerMultiplicationTable.address (var 0)
        (budget (var 0) (var 1) (var 2)) (computedBe (var 0) (var 1) (var 2) (var 3) (var 4)) (entry (var 2) (var 0)))
        (rows (var 0) (budget (var 0) (var 1) (var 2)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (third_query_address _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_computed_bed_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶ arrayHeight (succ (var 0)) (var 3) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶ arrayHeight (var 0) (computedBed (var 0) (var 1) (var 2) (var 3) (var 4))
        (growth (path (var 0)) (growth (path (var 0)) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (computed_bed_height _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_returned_be_fits_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶ arrayHeight (succ (var 0)) (var 3) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶ arrayHeight (var 0) (fstT (PTm.app operandsF ![var 0,var 1,var 2,var 3,var 4]))
        (budget (var 0) (var 1) (var 2))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_be_fits _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_returned_bed_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 5) ⟶ arrayHeight (succ (var 0)) (var 3) (var 5) ⟶
      arrayHeight (succ (var 0)) (var 4) (var 5) ⟶ arrayHeight (var 0) (sndT (PTm.app operandsF ![var 0,var 1,var 2,var 3,var 4]))
        (growth (path (var 0)) (growth (path (var 0)) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (returned_bed_height _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationHeight
