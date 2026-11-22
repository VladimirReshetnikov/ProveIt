import IPRADerivations.Analysis.GaussianRationalRowSpan

/-!
# Actual coefficients transporting a reduced row combination backwards

The pivot coordinate receives the normalized difference between its
old weight and the actual off-pivot weighted column. All other raw
weights are retained. Masked and single-spike sums prove the column
identity for the original elimination program, without a supplied
change-of-basis or combination law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRowSpanPivotTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul canonical)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_canonical)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalRowElimination (inverse normalizedPivot eliminate)
open GaussianRationalRowSpan (columnBody columnData combinationAt membership)
open GaussianTranslatedNonconstant (recode recode_eq recode_canonical)
open GaussianRationalFiniteSum (sum sum_canonical)
open GaussianRationalMonicReconstruction (spike spike_hit spike_miss)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def maskBody (f : PTm 2) : PTm 2 := sel (eqb (var 0) (fstT (var 1))) qzero
  (inst2 f (var 0) (sndT (var 1)))
def maskSum (f : PTm 2) (R i x : PTm n) : PTm n := sum (maskBody f) R (pairT i x)
def offColumn (A R u i j : PTm n) : PTm n := maskSum columnBody R i (columnData A u j)
def correction (A R u i p : PTm n) : PTm n :=
  qmul (inverse A i p) (qsub (entry u i) (offColumn A R u i p))
def value (A R u i p r : PTm n) : PTm n := sel (eqb r i) (correction A R u i p) (entry u r)
def data (A R u i p : PTm n) : PTm n := pairT A (pairT R (pairT u (pairT i p)))
def fields (q : PTm n) : Fin 5 → PTm n :=
  ![fstT q,fstT (sndT q),fstT (sndT (sndT q)),fstT (sndT (sndT (sndT q))),sndT (sndT (sndT (sndT q)))]
def body : PTm 2 := value (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2)
  (fields (var 1) 3) (fields (var 1) 4) (var 0)
def transfer (A R u i p : PTm n) : PTm n := sequence body R (data A R u i p)

@[simp] theorem subst_maskSum {k : ℕ} (σ : Fin n → PTm k) (f : PTm 2) (R i x : PTm n) :
    Syn.subst σ (maskSum f R i x) = maskSum f (Syn.subst σ R) (Syn.subst σ i) (Syn.subst σ x) := by simp [maskSum]
@[simp] theorem subst_offColumn {k : ℕ} (σ : Fin n → PTm k) (A R u i j : PTm n) :
    Syn.subst σ (offColumn A R u i j) = offColumn (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ j) := by simp [offColumn]
@[simp] theorem subst_correction {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (correction A R u i p) = correction (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [correction]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (A R u i p r : PTm n) :
    Syn.subst σ (value A R u i p r) = value (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ r) := by simp [value,sel]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (data A R u i p) = data (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [data]
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (q : PTm n) (j : Fin 5) :
    Syn.subst σ (fields q j) = fields (Syn.subst σ q) j := by fin_cases j <;> simp [fields]
@[simp] theorem subst_transfer {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (transfer A R u i p) = transfer (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by simp [transfer]

theorem mask_body_at (f : PTm 2) (i r x : PTm n) : Γ ⊢[PRAAx]
    inst2 (maskBody f) r (pairT i x) ≐ sel (eqb r i) qzero (inst2 f r x) := by
  have read : Syn.subst ![r,pairT i x] (Syn.subst ![var 0,sndT (var 1)] f) = inst2 f r (sndT (pairT i x)) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  simp only [maskBody,inst2,sel,PTm.subst_add,PTm.subst_mul,PTm.subst_monus,subst_eqb,
    GaussianRationalHorner.subst_qzero,subst_fstT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,read,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  exact congrAdd
    (congrMul (AnalyticNumberTheory.Euler.congrEqb (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
    (congrMul (congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb (.eqRefl _) (fst_pair _ _)))
      (congrInst2 f (.eqRefl _) (snd_pair _ _)))

theorem add_zero_recode (q : PTm n) : Γ ⊢[PRAAx] qadd q qzero ≐ recode q :=
  (GaussianRationalSyntheticCoefficientValues.qadd_recode_left q qzero).eqSymm.eqTrans
    (GaussianReciprocalHorner.qadd_zero_right _ (recode_canonical _))

theorem mask_spike (i r q : PTm n) : Γ ⊢[PRAAx]
    qadd (sel (eqb r i) qzero q) (spike i (recode q) r) ≐ recode q := by
  refine .orE (eq_or_ne r i) ?_ ?_
  · exact (qadd_congr (sel_one (eqb_of_eq Prf.hyp0)) (spike_hit _ _ _ Prf.hyp0)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (recode_canonical _))
  · exact (qadd_congr (sel_zero (eqb_of_ne Prf.hyp0)) (spike_miss _ _ _ Prf.hyp0)).eqTrans (add_zero_recode _)

theorem sum_decompose (f : PTm 2) (R i x : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    sum f R x ≐ qadd (maskSum f R i x) (recode (inst2 f i x)) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual
      (GaussianRationalFiniteSum.addBody (maskBody f) (GaussianRationalPermutationSum.deltaBody f))
      (GaussianRationalPermutationSum.recodeBody f) R (pairT i x) x := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,subst_pairT,GaussianRationalFiniteSum.inst2_addBody,
      GaussianRationalPermutationSum.inst2_recodeBody] using
      (qadd_congr (mask_body_at (Γ := Δ) f (Syn.shift i) (var 0) (Syn.shift x))
        (GaussianRationalPermutationSum.delta_body_at f (Syn.shift i) (var 0) (Syn.shift x))).eqTrans
          (mask_spike (Syn.shift i) (var 0) (inst2 f (var 0) (Syn.shift x)))
  exact (GaussianRationalPermutationSum.sum_recode f R x).eqSymm.eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqSymm.eqTrans
      ((GaussianRationalFiniteSum.sum_add _ _ _ _).eqTrans
        (qadd_congr (.eqRefl _) (GaussianRationalPermutationSum.delta_selected f R i x hi))))

theorem fields_at (A R u i p : PTm n) (j : Fin 5) : Γ ⊢[PRAAx]
    fields (data A R u i p) j ≐ ![A,R,u,i,p] j := by
  have a := snd_pair (Γ := Γ) A (pairT R (pairT u (pairT i p)))
  have b := (congrSnd a).eqTrans (snd_pair R (pairT u (pairT i p)))
  have c := (congrSnd b).eqTrans (snd_pair u (pairT i p))
  fin_cases j
  · exact fst_pair _ _
  · exact (congrFst a).eqTrans (fst_pair _ _)
  · exact (congrFst b).eqTrans (fst_pair _ _)
  · exact (congrFst c).eqTrans (fst_pair _ _)
  · exact (congrSnd c).eqTrans (snd_pair _ _)
theorem body_at (A R u i p r : PTm n) : Γ ⊢[PRAAx]
    inst2 body r (data A R u i p) ≐ value A R u i p r := by
  have last1 : ![fields (data A R u i p) 0,fields (data A R u i p) 1,fields (data A R u i p) 2,
    fields (data A R u i p) 3,fields (data A R u i p) 4,r] (5 : Fin 6) = r := rfl
  have last2 : ![A,R,u,i,p,r] (5 : Fin 6) = r := rfl
  simp only [body,inst2,subst_value,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,last1,last2,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![fields (data A R u i p) 0,fields (data A R u i p) 1,fields (data A R u i p) 2,
        fields (data A R u i p) 3,fields (data A R u i p) 4,r]) (σ' := ![A,R,u,i,p,r])
      (fun j => by
        fin_cases j
        · exact fields_at _ _ _ _ _ 0
        · exact fields_at _ _ _ _ _ 1
        · exact fields_at _ _ _ _ _ 2
        · exact fields_at _ _ _ _ _ 3
        · exact fields_at _ _ _ _ _ 4
        · exact .eqRefl _)
theorem transfer_length (A R u i p : PTm n) : Γ ⊢[PRAAx] length (transfer A R u i p) ≐ R := sequence_length _ _ _
theorem transfer_lookup (A R u i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    entry (transfer A R u i p) r ≐ value A R u i p r :=
  (sequence_decode body (x := data A R u i p) hr).eqTrans (body_at _ _ _ _ _ _)
theorem transfer_pivot (A R u i p : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    entry (transfer A R u i p) i ≐ correction A R u i p :=
  (transfer_lookup _ _ _ _ _ _ hi).eqTrans (sel_one (eqb_of_eq (.eqRefl _)))
theorem transfer_other (A R u i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    entry (transfer A R u i p) r ≐ entry u r :=
  (transfer_lookup _ _ _ _ _ _ hr).eqTrans (sel_zero (eqb_of_ne hne))

theorem weighted_elimination (u a b z : PTm n) : Γ ⊢[PRAAx]
    qmul u (qsub a (qmul b z)) ≐ qadd (qmul u a) (qmul (qnegative z) (qmul u b)) := by
  have negative : Γ ⊢[PRAAx] qnegative (qmul b z) ≐ qmul (qnegative z) b :=
    (GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative b z)).eqTrans
      (GaussianInverseBinomialRows.negative_product z b)
  have product : Γ ⊢[PRAAx] qmul u (qnegative (qmul b z)) ≐ qmul (qnegative z) (qmul u b) :=
    (qmul_congr (.eqRefl _) negative).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
        ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
          (GaussianReciprocalHorner.qmul_associative _ _ _)))
  exact (GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans (qadd_congr (.eqRefl _) product)

theorem off_reduced (A R N u i p j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    offColumn (eliminate A R N i p) R u i j ≐ qadd (offColumn A R u i j)
      (qmul (qnegative (normalizedPivot A i p j)) (offColumn A R u i p)) := by
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  apply GaussianInverseBinomialRows.linear_sum (maskBody columnBody) (maskBody columnBody) (maskBody columnBody) R
    (pairT i (columnData (eliminate A R N i p) u j)) (pairT i (columnData A u j))
    (pairT i (columnData A u p)) (qnegative (normalizedPivot A i p j))
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  let As := Syn.shift A
  let Rs := Syn.shift R
  let Ns := Syn.shift N
  let us := Syn.shift u
  let is := Syn.shift i
  let ps := Syn.shift p
  let js := Syn.shift j
  have left := mask_body_at (Γ := Δ) columnBody is (var 0) (columnData (eliminate As Rs Ns is ps) us js)
  have right1 := mask_body_at (Γ := Δ) columnBody is (var 0) (columnData As us js)
  have right2 := mask_body_at (Γ := Δ) columnBody is (var 0) (columnData As us ps)
  have result : Δ ⊢[PRAAx]
      inst2 (maskBody columnBody) (var 0) (pairT is (columnData (eliminate As Rs Ns is ps) us js)) ≐
        qadd (inst2 (maskBody columnBody) (var 0) (pairT is (columnData As us js)))
          (qmul (qnegative (normalizedPivot As is ps js))
            (inst2 (maskBody columnBody) (var 0) (pairT is (columnData As us ps)))) := by
    refine .orE (eq_or_ne (var 0) is) ?_ ?_
    · have l := left.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0))
      have r := (qadd_congr (right1.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0)))
        ((qmul_congr (.eqRefl (qnegative (normalizedPivot As is ps js))) (right2.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0)))).eqTrans
          (GaussianRationalSyntheticDivision.qmul_zero_right _))).eqTrans
            (GaussianRationalSyntheticDivision.qzero_add _ qzero_canonical)
      exact l.eqTrans r.eqSymm
    · have l := left.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans
        ((GaussianRationalRowSpan.column_body_at _ _ _ _).eqTrans
          ((qmul_congr (.eqRefl _) (GaussianRationalRowElimination.eliminated_lookup _ _ _ _ _ _ _
            Prf.hyp1 hjs.wk.wk Prf.hyp0)).eqTrans (weighted_elimination _ _ _ _))))
      have r := qadd_congr
        (right1.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans (GaussianRationalRowSpan.column_body_at _ _ _ _)))
        (qmul_congr (.eqRefl (qnegative (normalizedPivot As is ps js))) (right2.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans
          (GaussianRationalRowSpan.column_body_at _ _ _ _))))
      exact l.eqTrans r.eqSymm
  simpa only [Δ,As,Rs,Ns,us,is,ps,js,Syn.shift,subst_pairT,GaussianRationalRowSpan.subst_columnData,
    GaussianRationalRowElimination.subst_eliminate,GaussianRationalMetric.subst_qnegative,
    GaussianRationalRowElimination.subst_normalizedPivot] using result

theorem negative_cross (a b : PTm n) : Γ ⊢[PRAAx] qmul (qnegative a) b ≐ qmul (qnegative b) a :=
  (GaussianInverseBinomialRows.negative_product a b).eqSymm.eqTrans
    ((GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative a b)).eqTrans
      (GaussianInverseBinomialRows.negative_product b a))

theorem collect_correction (a b s z : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd a (qmul (qnegative z) s)) (qmul b z) ≐ qadd a (qmul (qsub b s) z) :=
  (GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
    (qadd_congr (.eqRefl a) ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
      ((qadd_congr (.eqRefl _) (negative_cross z s)).eqTrans
        (GaussianRationalRowElimination.distribute_right b (qnegative s) z).eqSymm)))

theorem reduced_combination (A R N u i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (eliminate A R N i p) R u j ≐ qadd (offColumn A R u i j)
      (qmul (qsub (entry u i) (offColumn A R u i p)) (normalizedPivot A i p j)) := by
  have e : Γ ⊢[PRAAx] recode (inst2 columnBody i (columnData (eliminate A R N i p) u j)) ≐
      qmul (entry u i) (normalizedPivot A i p j) :=
    (GaussianTranslatedNonconstant.recode_congr (GaussianRationalRowSpan.column_body_at _ _ _ _)).eqTrans
      ((recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
        (qmul_congr (.eqRefl _) (GaussianRationalRowElimination.normalized_lookup _ _ _ _ _ _ hi hj)))
  exact (sum_decompose columnBody R i (columnData (eliminate A R N i p) u j) hi).eqTrans
    ((qadd_congr (off_reduced A R N u i p j hj) e).eqTrans (collect_correction _ _ _ _))

theorem off_transfer (A R u i p j : PTm n) : Γ ⊢[PRAAx]
    offColumn A R (transfer A R u i p) i j ≐ offColumn A R u i j := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have l := mask_body_at (Γ := Δ) columnBody (Syn.shift i) (var 0)
    (columnData (Syn.shift A) (transfer (Syn.shift A) (Syn.shift R) (Syn.shift u) (Syn.shift i) (Syn.shift p)) (Syn.shift j))
  have r := mask_body_at (Γ := Δ) columnBody (Syn.shift i) (var 0) (columnData (Syn.shift A) (Syn.shift u) (Syn.shift j))
  have e : Δ ⊢[PRAAx]
      inst2 (maskBody columnBody) (var 0) (pairT (Syn.shift i)
        (columnData (Syn.shift A) (transfer (Syn.shift A) (Syn.shift R) (Syn.shift u) (Syn.shift i) (Syn.shift p)) (Syn.shift j))) ≐
      inst2 (maskBody columnBody) (var 0) (pairT (Syn.shift i) (columnData (Syn.shift A) (Syn.shift u) (Syn.shift j))) := by
    refine .orE (eq_or_ne (var 0) (Syn.shift i)) ?_ ?_
    · exact (l.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0))).eqTrans
        (r.wk.eqTrans (sel_one (eqb_of_eq Prf.hyp0))).eqSymm
    · exact (l.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans
        ((GaussianRationalRowSpan.column_body_at _ _ _ _).eqTrans
          (qmul_congr (transfer_other _ _ _ _ _ _ Prf.hyp1 Prf.hyp0) (.eqRefl _))))).eqTrans
            (r.wk.eqTrans ((sel_zero (eqb_of_ne Prf.hyp0)).eqTrans (GaussianRationalRowSpan.column_body_at _ _ _ _))).eqSymm
  simpa only [Δ,Syn.shift,subst_pairT,GaussianRationalRowSpan.subst_columnData,subst_transfer] using e

theorem correction_product (A R u i p j : PTm n) : Γ ⊢[PRAAx]
    qmul (correction A R u i p) (cell A i j) ≐
      qmul (qsub (entry u i) (offColumn A R u i p)) (normalizedPivot A i p j) :=
  (qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
    (GaussianReciprocalHorner.qmul_associative _ _ _)

theorem transferred_combination (A R u i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    combinationAt A R (transfer A R u i p) j ≐ qadd (offColumn A R u i j)
      (qmul (qsub (entry u i) (offColumn A R u i p)) (normalizedPivot A i p j)) := by
  have e : Γ ⊢[PRAAx] recode (inst2 columnBody i (columnData A (transfer A R u i p) j)) ≐
      qmul (qsub (entry u i) (offColumn A R u i p)) (normalizedPivot A i p j) :=
    (GaussianTranslatedNonconstant.recode_congr (GaussianRationalRowSpan.column_body_at _ _ _ _)).eqTrans
      ((recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
        ((qmul_congr (transfer_pivot A R u i p hi) (.eqRefl _)).eqTrans (correction_product A R u i p j)))
  exact (sum_decompose columnBody R i (columnData A (transfer A R u i p) j) hi).eqTrans
    (qadd_congr (off_transfer A R u i p j) e)

theorem column_transfer (A R N u i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (eliminate A R N i p) R u j ≐ combinationAt A R (transfer A R u i p) j :=
  (reduced_combination A R N u i p j hi hj).eqTrans (transferred_combination A R u i p j hi).eqSymm

theorem column_backward (A R N u i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt A R (transfer A R u i p) j ≐ combinationAt (eliminate A R N i p) R u j :=
  (column_transfer A R N u i p j hi hj).eqSymm

theorem combination_entry_transfer (A R N u i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (GaussianRationalRowSpan.rowCombination (eliminate A R N i p) R N u) j ≐
      entry (GaussianRationalRowSpan.rowCombination A R N (transfer A R u i p)) j :=
  (GaussianRationalRowSpan.combination_lookup _ _ _ _ _ hj).eqTrans
    ((column_transfer A R N u i p j hi hj).eqTrans (GaussianRationalRowSpan.combination_lookup _ _ _ _ _ hj).eqSymm)

theorem membership_backward (A R N u i p v : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianRationalRowElimination.input A R N i p)
    (hm : Γ ⊢[PRAAx] membership (eliminate A R N i p) R N u v) : Γ ⊢[PRAAx]
    membership A R N (transfer A R u i p) v := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalRowElimination.input (Syn.shift A) (Syn.shift R)
      (Syn.shift N) (Syn.shift i) (Syn.shift p) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_input,Syn.shift] using hInput.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] membership (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N)
      (Syn.shift i) (Syn.shift p)) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift v) := by
    simpa only [Fm.shift,GaussianRationalRowSpan.subst_membership,GaussianRationalRowElimination.subst_eliminate,Syn.shift] using hm.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have old := GaussianRationalRowSpan.membership_at (Γ := Δ)
    (eliminate (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift i) (Syn.shift p)) (Syn.shift R)
      (Syn.shift N) (Syn.shift u) (Syn.shift v) (var 0) ms.wk Prf.hyp0
  have eq := combination_entry_transfer (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u)
    (Syn.shift i) (Syn.shift p) (var 0) (.andE₁ (.andE₂ hs.wk)) Prf.hyp0
  simpa only [Δ,Syn.shift,subst_transfer] using
    GaussianRationalValueEquality.value_equal_trans _ _ _ old (GaussianRationalValueEquality.value_equal_of_code eq)

def outputF : PR 5 := PTm.toPR (transfer (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R u i p : PTm n) : PTm n := app outputF ![A,R,u,i,p]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R u i p : PTm n) :
    Syn.subst σ (run A R u i p) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ u)
      (Syn.subst σ i) (Syn.subst σ p) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem program_at (A R u i p : PTm n) : Γ ⊢[PRAAx] run A R u i p ≐ transfer A R u i p := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (transfer (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,u,i,p]
theorem returned_length (A R u i p : PTm n) : Γ ⊢[PRAAx] length (run A R u i p) ≐ R :=
  (congrFst (program_at A R u i p)).eqTrans (transfer_length A R u i p)
theorem returned_pivot (A R u i p : PTm n) (hi : Γ ⊢[PRAAx] lt i R) : Γ ⊢[PRAAx]
    entry (run A R u i p) i ≐ correction A R u i p :=
  (entry_congr (program_at A R u i p) (.eqRefl _)).eqTrans (transfer_pivot A R u i p hi)
theorem returned_other (A R u i p r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) (hne : Γ ⊢[PRAAx] neg (r ≐ i)) : Γ ⊢[PRAAx]
    entry (run A R u i p) r ≐ entry u r :=
  (entry_congr (program_at A R u i p) (.eqRefl _)).eqTrans (transfer_other A R u i p r hr hne)
theorem returned_column_backward (A R N u i p j : PTm n) (hi : Γ ⊢[PRAAx] lt i R)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt A R (run A R u i p) j ≐ combinationAt (eliminate A R N i p) R u j :=
  (GaussianRationalFiniteSum.sum_index_congr columnBody (.eqRefl R)
    (congrPairT (.eqRefl A) (congrPairT (program_at A R u i p) (.eqRefl j)))).eqTrans
      (column_backward A R N u i p j hi hj)

theorem actual_transfer_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (transfer (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 1) := closeUniv 5 (transfer_length _ _ _ _ _)
theorem actual_pivot_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ entry (transfer (var 0) (var 1) (var 2) (var 3) (var 4)) (var 3) ≐
      correction (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (.impI (transfer_pivot _ _ _ _ _ Prf.hyp0))
theorem actual_other_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 1) ⟶ neg (var 5 ≐ var 3) ⟶
      entry (transfer (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐ entry (var 2) (var 5)) :=
  closeUniv 6 (.impI (.impI (transfer_other _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_column_backward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 4) (var 1) ⟶ lt (var 6) (var 2) ⟶
      combinationAt (var 0) (var 1) (transfer (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6) ≐
        combinationAt (eliminate (var 0) (var 1) (var 2) (var 4) (var 5)) (var 1) (var 3) (var 6)) :=
  closeUniv 7 (.impI (.impI (column_backward _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_membership_backward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianRationalRowElimination.input (var 0) (var 1) (var 2) (var 4) (var 5) ⟶
      membership (eliminate (var 0) (var 1) (var 2) (var 4) (var 5)) (var 1) (var 2) (var 3) (var 6) ⟶
        membership (var 0) (var 1) (var 2) (transfer (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (membership_backward _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ transfer (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_column_backward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 4) (var 1) ⟶ lt (var 6) (var 2) ⟶
      combinationAt (var 0) (var 1) (run (var 0) (var 1) (var 3) (var 4) (var 5)) (var 6) ≐
        combinationAt (eliminate (var 0) (var 1) (var 2) (var 4) (var 5)) (var 1) (var 3) (var 6)) :=
  closeUniv 7 (.impI (.impI (returned_column_backward _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalRowSpanPivotTransfer
