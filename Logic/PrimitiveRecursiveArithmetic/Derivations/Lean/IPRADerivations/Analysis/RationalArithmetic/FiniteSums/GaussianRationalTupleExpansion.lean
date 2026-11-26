import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalBlockSums
import IPRADerivations.Foundations.RuntimeWordAppend

/-!
# Actual numerical expansion of products of Gaussian row sums

One fixed three-variable entry body supplies all original raw values.
Both sides use the SAME existing finite-sum and product folds. Little-
endian word append, actual block flattening and scalar sum transport
prove the successor law; the guarded QF induction derives positive
radix only at a nonempty successor. Zero length has one empty word,
including radix zero. All dimensions, prefix lengths, words and data
are numerical, with no distributive, selector or decoding law premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalTupleExpansion

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_index_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct (qprod product_index_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowProduct (f : PTm 3) (m d x : PTm n) : PTm n :=
  qprod (GaussianRationalFubini.rowSumBody f) d (pairT m x)
def choiceData (m w x : PTm n) : PTm n := pairT m (pairT w x)
def choiceBody (f : PTm 3) : PTm 2 := inst3 f (var 0)
  (Foundations.RuntimePermutationWords.digit (fstT (var 1)) (fstT (sndT (var 1))) (var 0)) (sndT (sndT (var 1)))
def choiceProduct (f : PTm 3) (m d w x : PTm n) : PTm n := qprod (choiceBody f) d (choiceData m w x)
def tupleData (m d x : PTm n) : PTm n := pairT m (pairT d x)
def tupleBody (f : PTm 3) : PTm 2 := choiceProduct f
  (fstT (var 1)) (fstT (sndT (var 1))) (var 0) (sndT (sndT (var 1)))
def tupleSum (f : PTm 3) (m d x : PTm n) : PTm n := sum (tupleBody f) (pw m d) (tupleData m d x)

ipra_subst rowProduct
ipra_subst choiceData
ipra_subst choiceProduct
ipra_subst tupleData
ipra_subst tupleSum

theorem digit_congr {m m' w w' i i' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hw : Γ ⊢[PRAAx] w ≐ w') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.digit m w i ≐ Foundations.RuntimePermutationWords.digit m' w' i' :=
  congrAp2 remF (congrAp2 quoF hw (congrAp2 powF hi hm)) hm

@[simp] theorem choice_entry (f : PTm 3) (i y : PTm n) :
    inst2 (choiceBody f) i y = inst3 f i
      (Foundations.RuntimePermutationWords.digit (fstT y) (fstT (sndT y)) i) (sndT (sndT y)) := by
  simp only [choiceBody,inst2,inst3,Syn.subst_subst,Foundations.RuntimePermutationWords.subst_digit,
    subst_fstT,subst_sndT,Syn.subst_var]
  congr 1
  funext j
  fin_cases j <;> simp

theorem choice_body_at (f : PTm 3) (m w x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (choiceBody f) i (choiceData m w x) ≐ inst3 f i (Foundations.RuntimePermutationWords.digit m w i) x := by
  rw [choice_entry]
  exact congrInst3 f (.eqRefl _)
    (digit_congr (fst_pair _ _) (snd_pair _ _).fstE (.eqRefl _))
    (snd_pair _ _).sndE

theorem choice_product_congr (f : PTm 3) {m m' d d' w w' x x' : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d') (hw : Γ ⊢[PRAAx] w ≐ w') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx]
    choiceProduct f m d w x ≐ choiceProduct f m' d' w' x' :=
  product_index_congr _ hd (congrPairT hm (congrPairT hw hx))

theorem tuple_body_at (f : PTm 3) (m d x w : PTm n) : Γ ⊢[PRAAx]
    inst2 (tupleBody f) w (tupleData m d x) ≐ choiceProduct f m d w x := by
  simp only [tupleBody,inst2,subst_choiceProduct,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact choice_product_congr f (fst_pair _ _) (snd_pair _ _).fstE
    (.eqRefl _) (snd_pair _ _).sndE

theorem row_product_zero (f : PTm 3) (m x : PTm n) : Γ ⊢[PRAAx] rowProduct f m zero x ≐ qone := GaussianRationalFiniteProduct.product_zero _ _
theorem row_product_succ (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx]
    rowProduct f m (succ d) x ≐ qmul (rowProduct f m d x) (GaussianRationalFubini.row f d m x) :=
  (GaussianRationalFiniteProduct.product_succ _ _ _).eqTrans
    (qmul_congr (.eqRefl _) (GaussianRationalFubini.row_sum_at _ _ _ _))

theorem choice_prefix_append (f : PTm 3) (m d w v x : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    choiceProduct f m d (Foundations.RuntimeWordAppend.append m d w v) x ≐ choiceProduct f m d w x := by
  apply GaussianRationalFiniteProduct.product_congr_bounded
  refine .allI (.impI ?_)
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
  have e := (choice_body_at (Γ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift) f (Syn.shift m)
    (Foundations.RuntimeWordAppend.append (Syn.shift m) (Syn.shift d) (Syn.shift w) (Syn.shift v)) (Syn.shift x) (var 0)).eqTrans
      ((congrInst3 f (.eqRefl _) (Foundations.RuntimeWordAppend.digit_before _ _ _ _ _ ms.wk Prf.hyp0) (.eqRefl _)).eqTrans
        (choice_body_at f (Syn.shift m) (Syn.shift w) (Syn.shift x) (var 0)).eqSymm)
  simpa only [Syn.shift,subst_choiceData,Foundations.RuntimeWordAppend.subst_append] using e

theorem choice_append (f : PTm 3) (m d w v x : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hw : Γ ⊢[PRAAx] lt w (pw m d)) (hv : Γ ⊢[PRAAx] lt v m) : Γ ⊢[PRAAx]
    choiceProduct f m (succ d) (Foundations.RuntimeWordAppend.append m d w v) x ≐
      qmul (choiceProduct f m d w x) (inst3 f d v x) :=
  (GaussianRationalFiniteProduct.product_succ _ _ _).eqTrans
    (qmul_congr (choice_prefix_append _ _ _ _ _ _ hm)
      ((choice_body_at _ _ _ _ _).eqTrans
        (congrInst3 f (.eqRefl _) (Foundations.RuntimeWordAppend.digit_new _ _ _ _ hm hw hv) (.eqRefl _))))

/-- The zero-row case really sums over ONE empty word, even when m=0. -/
theorem tuple_sum_zero (f : PTm 3) (m x : PTm n) : Γ ⊢[PRAAx] tupleSum f m zero x ≐ qone :=
  (sum_index_congr _ (pw_zero m) (.eqRefl _)).eqTrans
    ((GaussianRationalFiniteSum.sum_succ _ zero _).eqTrans
      ((qadd_congr (GaussianRationalFiniteSum.sum_zero _ _)
        ((tuple_body_at _ _ _ _ _).eqTrans (GaussianRationalFiniteProduct.product_zero _ _))).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add _ qone_canonical)))

def appendedBlock (f : PTm 3) (m d v x : PTm n) : PTm n := sum (offB (tupleBody f)) (pw m d)
  (pairT (pw m d*v) (tupleData m (succ d) x))
ipra_subst appendedBlock

theorem appended_block (f : PTm 3) (m d v x : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hv : Γ ⊢[PRAAx] lt v m) : Γ ⊢[PRAAx]
    appendedBlock f m d v x ≐ qmul (tupleSum f m d x) (inst3 f d v x) := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift v) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hv.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (offB (tupleBody f))
      (GaussianRationalFiniteSum.multiplyBody (tupleBody f)) (pw m d)
      (pairT (pw m d*v) (tupleData m (succ d) x)) (pairT (inst3 f d v x) (tupleData m d x)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (pw m d)) :: Γ.map Fm.shift
    have ii : Δ ⊢[PRAAx] lt (var 0) (pw (Syn.shift m) (Syn.shift d)) := by simpa only [Δ,pw,Syn.shift,subst_ap2] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have w : Δ ⊢[PRAAx] pw (Syn.shift m) (Syn.shift d)*Syn.shift v+var 0 ≐
        Foundations.RuntimeWordAppend.append (Syn.shift m) (Syn.shift d) (var 0) (Syn.shift v) := by unfold Foundations.RuntimeWordAppend.append; ipra_ring
    have e : Δ ⊢[PRAAx] inst2 (offB (tupleBody f)) (var 0)
        (pairT (pw (Syn.shift m) (Syn.shift d)*Syn.shift v) (tupleData (Syn.shift m) (succ (Syn.shift d)) (Syn.shift x))) ≐
        inst2 (GaussianRationalFiniteSum.multiplyBody (tupleBody f)) (var 0)
          (pairT (inst3 f (Syn.shift d) (Syn.shift v) (Syn.shift x)) (tupleData (Syn.shift m) (Syn.shift d) (Syn.shift x))) :=
      (GaussianRationalFiniteProduct.offset_at _ _ _ _).eqTrans
        ((tuple_body_at _ _ _ _ _).eqTrans
          ((choice_product_congr f (.eqRefl _) (.eqRefl _) w (.eqRefl _)).eqTrans
            ((choice_append _ _ _ _ _ _ ms.wk ii vs.wk).eqTrans
              ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
                ((GaussianRationalFiniteSum.multiply_body_at _ _ _ _).eqTrans
                  (qmul_congr (.eqRefl _) (tuple_body_at _ _ _ _ _))).eqSymm))))
    simpa only [Δ,Syn.shift,subst_tupleData,subst_pairT,PTm.subst_mul,subst_ap2,subst_inst3,
      ConciseIPRA.PTm.subst_succ] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply _ _ _ _).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))

/-- True mixed-radix block expansion at a positive successor radix. -/
theorem tuple_sum_succ (f : PTm 3) (m d x : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    tupleSum f m (succ d) x ≐ qmul (tupleSum f m d x) (GaussianRationalFubini.row f d m x) := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalBlockSums.blockBody (tupleBody f))
      (GaussianRationalFiniteSum.multiplyBody (GaussianRationalFubini.rowBody f)) m
      (pairT (pw m d) (tupleData m (succ d) x)) (pairT (tupleSum f m d x) (pairT d x)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (GaussianRationalBlockSums.blockBody (tupleBody f)) (var 0)
        (pairT (pw (Syn.shift m) (Syn.shift d)) (tupleData (Syn.shift m) (succ (Syn.shift d)) (Syn.shift x))) ≐
        inst2 (GaussianRationalFiniteSum.multiplyBody (GaussianRationalFubini.rowBody f)) (var 0)
          (pairT (tupleSum f (Syn.shift m) (Syn.shift d) (Syn.shift x)) (pairT (Syn.shift d) (Syn.shift x))) :=
      (GaussianRationalBlockSums.block_body_at _ _ _ _).eqTrans
        ((appended_block _ _ _ _ _ ms.wk Prf.hyp0).eqTrans
          ((GaussianRationalFiniteSum.multiply_body_at _ _ _ _).eqTrans
            (qmul_congr (.eqRefl _) (GaussianRationalFubini.row_entry _ _ _ _))).eqSymm)
    simpa only [Δ,Syn.shift,subst_tupleData,subst_pairT,subst_tupleSum,subst_ap2,ConciseIPRA.PTm.subst_succ] using e
  exact (sum_index_congr (tupleBody f) (pw_succ m d) (.eqRefl _)).eqTrans
    ((GaussianRationalBlockSums.sum_blocks (tupleBody f) (pw m d) m (tupleData m (succ d) x)).eqTrans
      ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ entries).eqTrans (GaussianRationalFiniteSum.sum_multiply _ _ _ _)))

def expansionLaw (f : PTm 3) (m d x : PTm n) : Fm PTm n := le d m ⟶ rowProduct f m d x ≐ tupleSum f m d x
ipra_subst expansionLaw

/-- Every length/radix/data value is internal; no positive-radix hypothesis is needed at zero length. -/
theorem expansion (f : PTm 3) (m d x : PTm n) (hd : Γ ⊢[PRAAx] le d m) : Γ ⊢[PRAAx]
    rowProduct f m d x ≐ tupleSum f m d x := by
  have all : Γ ⊢[PRAAx] .all (expansionLaw f (Syn.shift m) (var 0) (Syn.shift x)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_expansionLaw]
    · exact .impI ((row_product_zero _ _ _).eqTrans (tuple_sum_zero _ _ _).eqSymm)
    · refine .impI ?_
      have hm : le (succ (var 0)) (Syn.shift m) :: expansionLaw f (Syn.shift m) (var 0) (Syn.shift x) :: Γ.map Fm.shift ⊢[PRAAx]
          le one (Syn.shift m) := le_trans (zero_lt_succ (var 0)) Prf.hyp0
      exact (row_product_succ _ _ _ _).eqTrans
        ((qmul_congr (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)) (.eqRefl _)).eqTrans
          (tuple_sum_succ _ _ _ _ hm).eqSymm)
  have rule : Γ ⊢[PRAAx] expansionLaw f m d x := by
    simpa only [subst_expansionLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE d
  exact .impE rule hd

theorem full_expansion (f : PTm 3) (m x : PTm n) : Γ ⊢[PRAAx] rowProduct f m m x ≐ tupleSum f m m x := expansion f m m x (le_refl _)

theorem row_product_canonical (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx] canonical (rowProduct f m d x) :=
  GaussianRationalFiniteProduct.product_canonical _ _ _
theorem choice_product_canonical (f : PTm 3) (m d w x : PTm n) : Γ ⊢[PRAAx] canonical (choiceProduct f m d w x) :=
  GaussianRationalFiniteProduct.product_canonical _ _ _
theorem tuple_sum_canonical (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx] canonical (tupleSum f m d x) :=
  GaussianRationalFiniteSum.sum_canonical _ _ _
theorem choice_digit_bound (m d w i : PTm n) (hd : Γ ⊢[PRAAx] le d m) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    lt (Foundations.RuntimePermutationWords.digit m w i) m :=
  Foundations.RuntimePermutationWords.digit_bound _ _ _ (le_trans hi hd)

/-- The actual two independent folds and the numerical number of scanned tuple codes. -/
def output (f : PTm 3) (m d x : PTm n) : PTm n :=
  pairT (rowProduct f m d x) (pairT (tupleSum f m d x) (pw m d))
def outputF (f : PTm 3) : PR 3 := PTm.toPR (output f (var 0) (var 1) (var 2))
def run (f : PTm 3) (m d x : PTm n) : PTm n := ap3 (outputF f) m d x
ipra_subst output
ipra_subst run
theorem program_at (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx] run f m d x ≐ output f m d x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output f (var 0) (var 1) (var 2) : PTm 3) ![m,d,x]
theorem returned_row_product (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx]
    fstT (run f m d x) ≐ rowProduct f m d x := (program_at _ _ _ _).fstE
theorem returned_tuple_sum (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run f m d x)) ≐ tupleSum f m d x :=
  (program_at _ _ _ _).sndE.fstE
theorem returned_word_count (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run f m d x)) ≐ pw m d :=
  (program_at _ _ _ _).sndE.sndE
theorem returned_equal (f : PTm 3) (m d x : PTm n) (hd : Γ ⊢[PRAAx] le d m) : Γ ⊢[PRAAx]
    fstT (run f m d x) ≐ fstT (sndT (run f m d x)) :=
  (returned_row_product _ _ _ _).eqTrans ((expansion _ _ _ _ hd).eqTrans (returned_tuple_sum _ _ _ _).eqSymm)
theorem returned_row_canonical (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx] canonical (fstT (run f m d x)) :=
  GaussianRationalHorner.canonical_congr (returned_row_product _ _ _ _) (row_product_canonical _ _ _ _)
theorem returned_tuple_canonical (f : PTm 3) (m d x : PTm n) : Γ ⊢[PRAAx] canonical (fstT (sndT (run f m d x))) :=
  GaussianRationalHorner.canonical_congr (returned_tuple_sum _ _ _ _) (tuple_sum_canonical _ _ _ _)

theorem actual_choice_append_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ lt (var 2) (pw (var 0) (var 1)) ⟶ lt (var 3) (var 0) ⟶
      choiceProduct f (var 0) (succ (var 1)) (Foundations.RuntimeWordAppend.append (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        qmul (choiceProduct f (var 0) (var 1) (var 2) (var 4)) (inst3 f (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (choice_append _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_empty_tuple_expansion_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((rowProduct f (var 0) zero (var 1) ≐ qone) ⋏ tupleSum f (var 0) zero (var 1) ≐ qone) :=
  closeUniv 2 (.andI (row_product_zero _ _ _) (tuple_sum_zero _ _ _))
theorem actual_tuple_expansion_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 0) ⟶ rowProduct f (var 0) (var 1) (var 2) ≐ tupleSum f (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (expansion _ _ _ _ Prf.hyp0))
theorem actual_full_tuple_expansion_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rowProduct f (var 0) (var 0) (var 1) ≐ tupleSum f (var 0) (var 0) (var 1)) := closeUniv 2 (full_expansion _ _ _)
theorem actual_tuple_program_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run f (var 0) (var 1) (var 2) ≐ output f (var 0) (var 1) (var 2)) ⋏
      ((sndT (sndT (run f (var 0) (var 1) (var 2))) ≐ pw (var 0) (var 1)) ⋏
        (canonical (fstT (run f (var 0) (var 1) (var 2))) ⋏ canonical (fstT (sndT (run f (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.andI (program_at _ _ _ _) (.andI (returned_word_count _ _ _ _)
    (.andI (returned_row_canonical _ _ _ _) (returned_tuple_canonical _ _ _ _))))
theorem actual_returned_expansion_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 0) ⟶ fstT (run f (var 0) (var 1) (var 2)) ≐ fstT (sndT (run f (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (returned_equal _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalTupleExpansion
