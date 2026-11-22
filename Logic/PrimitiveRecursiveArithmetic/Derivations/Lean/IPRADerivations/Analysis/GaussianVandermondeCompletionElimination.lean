import IPRADerivations.Analysis.GaussianScalarTriangularDeterminant

/-!
# Actual left elimination of the completed Vandermonde table

The original completion W is retained. The actual upper unitriangular
left table subtracts its upper-right block using the original standard
coordinate rows. Every bounded product entry is derived from the SAME
Gaussian finite sums. No block determinant or row-product law is an
input, and no distinctness of original raw roots is required.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianVandermondeCompletionElimination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul canonical canonical_congr qmul_canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qmul_congr qadd_congr)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open GaussianRationalReciprocal (power power_canonical)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalFiberVandermonde (delta weight W W_lookup table table_lookup)
open GaussianRationalMatrixFiniteSums (matrixProduct scalarDot scalarBody scalarData product_lookup scalar_body_at deltaBody deltaSum)
open GaussianScalarDeterminant (scalarDet)
open GaussianScalarTriangularDeterminant (belowZeros diagonalOnes)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def eliminatorWeight (R r j : PTm n) : PTm n := sel (Signum.sg (monus (length R) r))
  (sel (eqb (monus (length R) j) zero) (qnegative (power (entry R r) j)) (delta r j)) (delta r j)
def eliminatorBody : PTm 3 := eliminatorWeight (var 2) (var 0) (var 1)
def eliminator (R m : PTm n) : PTm n := table eliminatorBody m m R
def eliminated (R m : PTm n) : PTm n := matrixProduct (eliminator R m) (W R m) m
@[simp] theorem subst_eliminatorWeight {l : ℕ} (σ : Fin n → PTm l) (R r j : PTm n) :
    Syn.subst σ (eliminatorWeight R r j) = eliminatorWeight (Syn.subst σ R) (Syn.subst σ r) (Syn.subst σ j) := by
  simp [eliminatorWeight,sel,Signum.sg]
@[simp] theorem subst_eliminator {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (eliminator R m) = eliminator (Syn.subst σ R) (Syn.subst σ m) := by simp [eliminator]
@[simp] theorem subst_eliminated {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (eliminated R m) = eliminated (Syn.subst σ R) (Syn.subst σ m) := by simp [eliminated]

theorem delta_congr {a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b) (hc : Γ ⊢[PRAAx] c ≐ d) : Γ ⊢[PRAAx]
    delta a c ≐ delta b d := by
  simpa only [GaussianRationalFiberVandermonde.subst_delta,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (delta (var 0) (var 1) : PTm 2) (σ := ![a,c]) (σ' := ![b,d])
      (fun i => by fin_cases i; exact ha; exact hc)
theorem delta_symm (r j : PTm n) : Γ ⊢[PRAAx] delta r j ≐ delta j r := by
  refine .orE (eq_or_ne r j) ?_ ?_
  · exact (GaussianRationalLagrangeCardinals.delta_equal _ _ Prf.hyp0).eqTrans
      (GaussianRationalLagrangeCardinals.delta_equal _ _ Prf.hyp0.eqSymm).eqSymm
  · have reverse : neg (r ≐ j) :: Γ ⊢[PRAAx] neg (j ≐ r) := .impI (.impE Prf.hyp1 Prf.hyp0.eqSymm)
    exact (GaussianRationalLagrangeCardinals.delta_unequal _ _ Prf.hyp0).eqTrans
      (GaussianRationalLagrangeCardinals.delta_unequal _ _ reverse).eqSymm

theorem eliminator_tail (R r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    eliminatorWeight R r j ≐ qnegative (power (entry R r) j) :=
  (sel_one (AnalyticNumberTheory.Totatives.sg_lt hr)).eqTrans (sel_one (eqb_of_eq hj))
theorem eliminator_head (R r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    eliminatorWeight R r j ≐ delta r j := by
  have hn : Γ ⊢[PRAAx] neg (monus (length R) j ≐ zero) := .impI (le_lt_absurd _ Prf.hyp0 hj.wk)
  exact (sel_one (AnalyticNumberTheory.Totatives.sg_lt hr)).eqTrans (sel_zero (eqb_of_ne hn))
theorem eliminator_lower (R r j : PTm n) (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    eliminatorWeight R r j ≐ delta r j := sel_zero (AnalyticNumberTheory.Totatives.sg_le hr)
theorem eliminator_weight_canonical (R r j : PTm n) : Γ ⊢[PRAAx] canonical (eliminatorWeight R r j) := by
  refine .orE (lt_or_le r (length R)) ?_ ?_
  · refine .orE (lt_or_le j (length R)) ?_ ?_
    · exact canonical_congr (eliminator_head _ _ _ Prf.hyp1 Prf.hyp0) (GaussianRationalFiberVandermonde.delta_canonical _ _)
    · exact canonical_congr (eliminator_tail _ _ _ Prf.hyp1 Prf.hyp0) (qnegative_canonical _)
  · exact canonical_congr (eliminator_lower _ _ _ Prf.hyp0) (GaussianRationalFiberVandermonde.delta_canonical _ _)
theorem eliminator_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (eliminator R m) r j ≐ eliminatorWeight R r j := by
  simpa [eliminatorBody,eliminator] using table_lookup eliminatorBody m m R r j hr hj

theorem eliminator_upper_at (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hjr : Γ ⊢[PRAAx] lt j r) : Γ ⊢[PRAAx] recode (cell (eliminator R m) r j) ≐ qzero := by
  have value : Γ ⊢[PRAAx] eliminatorWeight R r j ≐ delta r j := by
    refine .orE (lt_or_le r (length R)) (eliminator_head _ _ _ Prf.hyp0 (lt_of_lt_of_le hjr.wk (le_of_lt Prf.hyp0)))
      (eliminator_lower _ _ _ Prf.hyp0)
  have ne : Γ ⊢[PRAAx] neg (r ≐ j) := .impI (lt_irrefl j _ (lt_congr (.eqRefl _) Prf.hyp0 hjr.wk))
  exact (recode_congr ((eliminator_lookup _ _ _ _ hr hj).eqTrans (value.eqTrans
    (GaussianRationalLagrangeCardinals.delta_unequal _ _ ne)))).eqTrans (recode_eq qzero qzero_canonical)
theorem eliminator_diagonal_at (R m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    recode (cell (eliminator R m) r r) ≐ qone := by
  have value : Γ ⊢[PRAAx] eliminatorWeight R r r ≐ delta r r :=
    .orE (lt_or_le r (length R)) (eliminator_head _ _ _ Prf.hyp0 Prf.hyp0) (eliminator_lower _ _ _ Prf.hyp0)
  exact (recode_congr ((eliminator_lookup _ _ _ _ hr hr).eqTrans (value.eqTrans
    (GaussianRationalLagrangeCardinals.delta_equal _ _ (.eqRefl _))))).eqTrans (recode_eq qone qone_canonical)

def columnWeightBody : PTm 2 := weight (fstT (var 1)) (var 0) (sndT (var 1))
def rowNegativeBody : PTm 2 := qnegative (power (entry (fstT (var 1)) (sndT (var 1))) (var 0))
theorem column_weight_at (R j k : PTm n) : Γ ⊢[PRAAx] inst2 columnWeightBody k (pairT R j) ≐ weight R k j := by
  simp only [columnWeightBody,inst2,GaussianRationalFiberVandermonde.subst_weight,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [GaussianRationalFiberVandermonde.subst_weight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (weight (var 0) (var 1) (var 2) : PTm 3) (σ := ![fstT (pairT R j),k,sndT (pairT R j)])
      (σ' := ![R,k,j]) (fun i => by fin_cases i; exact fst_pair _ _; exact .eqRefl _; exact snd_pair _ _)
theorem row_negative_at (R r k : PTm n) : Γ ⊢[PRAAx] inst2 rowNegativeBody k (pairT R r) ≐ qnegative (power (entry R r) k) := by
  simp only [rowNegativeBody,inst2,GaussianRationalMetric.subst_qnegative,GaussianRationalReciprocal.subst_power,
    Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianInverseBinomialRows.negative_congr (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _)
    (entry_congr (fst_pair _ _) (snd_pair _ _)))

def leftBody (f : PTm 2) : PTm 2 := inst2 f (var 0) (fstT (var 1))
def rightBody (f : PTm 2) : PTm 2 := inst2 f (var 0) (sndT (var 1))
def pairedAddBody (f g : PTm 2) : PTm 2 := GaussianRationalFiniteSum.addBody (leftBody f) (rightBody g)
theorem left_body_at (f : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx] inst2 (leftBody f) i (pairT x y) ≐ inst2 f i x := by
  have e : inst2 (leftBody f) i (pairT x y) = inst2 f i (fstT (pairT x y)) := by
    simp only [leftBody,inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  rw [e]
  exact congrInst2 f (.eqRefl _) (fst_pair _ _)
theorem right_body_at (f : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx] inst2 (rightBody f) i (pairT x y) ≐ inst2 f i y := by
  have e : inst2 (rightBody f) i (pairT x y) = inst2 f i (sndT (pairT x y)) := by
    simp only [rightBody,inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  rw [e]
  exact congrInst2 f (.eqRefl _) (snd_pair _ _)
theorem paired_add_at (f g : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    inst2 (pairedAddBody f g) i (pairT x y) ≐ qadd (inst2 f i x) (inst2 g i y) := by
  rw [pairedAddBody,GaussianRationalFiniteSum.inst2_addBody]
  exact qadd_congr (left_body_at _ _ _ _) (right_body_at _ _ _ _)
theorem paired_sum_add (f g : PTm 2) (N x y : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (pairedAddBody f g) N (pairT x y) ≐
      qadd (GaussianRationalFiniteSum.sum f N x) (GaussianRationalFiniteSum.sum g N y) := by
  have left : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum (leftBody f) N (pairT x y) ≐ GaussianRationalFiniteSum.sum f N x := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simpa only [Syn.shift,subst_pairT] using
      left_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) f (var 0) (Syn.shift x) (Syn.shift y)
  have right : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum (rightBody g) N (pairT x y) ≐ GaussianRationalFiniteSum.sum g N y := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simpa only [Syn.shift,subst_pairT] using
      right_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) g (var 0) (Syn.shift x) (Syn.shift y)
  exact (GaussianRationalFiniteSum.sum_add (leftBody f) (rightBody g) N (pairT x y)).eqTrans (qadd_congr left right)

theorem cut_unequal (a b t : PTm n) (ha : Γ ⊢[PRAAx] lt a t) (hb : Γ ⊢[PRAAx] le t b) : Γ ⊢[PRAAx] neg (a ≐ b) :=
  .impI (le_lt_absurd _ (le_congr (.eqRefl t) Prf.hyp0.eqSymm hb.wk) ha.wk)

def headTerm (R r j k : PTm n) : PTm n := qmul (delta r k) (weight R k j)
def tailTerm (R r j k : PTm n) : PTm n := qmul (delta j k) (qnegative (power (entry R r) k))
@[simp] theorem subst_headTerm {l : ℕ} (σ : Fin n → PTm l) (R r j k : PTm n) :
    Syn.subst σ (headTerm R r j k) = headTerm (Syn.subst σ R) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ k) := by simp [headTerm]
@[simp] theorem subst_tailTerm {l : ℕ} (σ : Fin n → PTm l) (R r j k : PTm n) :
    Syn.subst σ (tailTerm R r j k) = tailTerm (Syn.subst σ R) (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ k) := by simp [tailTerm]

theorem head_delta_at (R r j k : PTm n) : Γ ⊢[PRAAx]
    inst2 (GaussianRationalMatrixFiniteSums.deltaBody columnWeightBody) k (pairT r (pairT R j)) ≐ headTerm R r j k :=
  (GaussianRationalMatrixFiniteSums.delta_body_at _ _ _ _).eqTrans (qmul_congr (.eqRefl _) (column_weight_at _ _ _))
theorem tail_delta_at (R r j k : PTm n) : Γ ⊢[PRAAx]
    inst2 (GaussianRationalMatrixFiniteSums.deltaBody rowNegativeBody) k (pairT j (pairT R r)) ≐ tailTerm R r j k :=
  (GaussianRationalMatrixFiniteSums.delta_body_at _ _ _ _).eqTrans (qmul_congr (.eqRefl _) (row_negative_at _ _ _))

theorem elimination_term_head (R r j k : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R))
    (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    qmul (eliminatorWeight R r k) (weight R k j) ≐ headTerm R r j k := by
  refine .orE (lt_or_le k (length R)) ?_ ?_
  · exact qmul_congr (eliminator_head _ _ _ hr.wk Prf.hyp0) (.eqRefl _)
  · have zeroRight : le (length R) k :: Γ ⊢[PRAAx] weight R k j ≐ qzero :=
      (GaussianRationalFiberVandermonde.weight_lower _ _ _ Prf.hyp0).eqTrans
        ((delta_symm k j).eqTrans (GaussianRationalLagrangeCardinals.delta_unequal _ _ (cut_unequal _ _ _ hj.wk Prf.hyp0)))
    have zeroHead : le (length R) k :: Γ ⊢[PRAAx] headTerm R r j k ≐ qzero :=
      (qmul_congr (GaussianRationalLagrangeCardinals.delta_unequal _ _ (cut_unequal _ _ _ hr.wk Prf.hyp0)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _)
    exact ((qmul_congr (.eqRefl _) zeroRight).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)).eqTrans zeroHead.eqSymm

theorem elimination_term_tail (R r j k : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R))
    (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    qmul (eliminatorWeight R r k) (weight R k j) ≐ qadd (headTerm R r j k) (tailTerm R r j k) := by
  refine .orE (lt_or_le k (length R)) ?_ ?_
  · have tailZero : lt k (length R) :: Γ ⊢[PRAAx] tailTerm R r j k ≐ qzero :=
      (qmul_congr ((delta_symm j k).eqTrans (GaussianRationalLagrangeCardinals.delta_unequal _ _
        (cut_unequal _ _ _ Prf.hyp0 hj.wk))) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
    exact (qmul_congr (eliminator_head _ _ _ hr.wk Prf.hyp0) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qadd_zero_right _ (qmul_canonical _ _)).eqSymm.eqTrans
        (qadd_congr (.eqRefl _) tailZero.eqSymm))
  · have headZero : le (length R) k :: Γ ⊢[PRAAx] headTerm R r j k ≐ qzero :=
      (qmul_congr (GaussianRationalLagrangeCardinals.delta_unequal _ _ (cut_unequal _ _ _ hr.wk Prf.hyp0)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _)
    exact (qmul_congr (eliminator_tail _ _ _ hr.wk Prf.hyp0) (GaussianRationalFiberVandermonde.weight_lower _ _ _ Prf.hyp0)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        ((qmul_congr (delta_symm k j) (.eqRefl _)).eqTrans
          ((GaussianRationalSyntheticDivision.qzero_add _ (qmul_canonical _ _)).eqSymm.eqTrans
            (qadd_congr headZero.eqSymm (.eqRefl _)))))

theorem elimination_term_lower (R r j k : PTm n) (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    qmul (eliminatorWeight R r k) (weight R k j) ≐ headTerm R r j k :=
  qmul_congr (eliminator_lower _ _ _ hr) (.eqRefl _)

theorem head_sum (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    deltaSum columnWeightBody m r (pairT R j) ≐ weight R r j :=
  (GaussianRationalMatrixFiniteSums.sum_delta_canonical _ _ _ _ hr
    (canonical_congr (column_weight_at _ _ _) (GaussianRationalFiberVandermonde.weight_canonical _ _ _))).eqTrans (column_weight_at _ _ _)
theorem tail_sum (R m r j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    deltaSum rowNegativeBody m j (pairT R r) ≐ qnegative (power (entry R r) j) :=
  (GaussianRationalMatrixFiniteSums.sum_delta_canonical _ _ _ _ hj
    (canonical_congr (row_negative_at _ _ _) (qnegative_canonical _))).eqTrans (row_negative_at _ _ _)

theorem dot_upper_left (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    scalarDot (eliminator R m) (W R m) m r j ≐ power (entry R r) j := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody (GaussianRationalMatrixFiniteSums.deltaBody columnWeightBody) m
      (scalarData (eliminator R m) (W R m) r j) (pairT r (pairT R j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have rms : Δ ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hrm.shift.wk : Δ ⊢[PRAAx] (lt r m).shift)
    have jms : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hjm.shift.wk : Δ ⊢[PRAAx] (lt j m).shift)
    have rs : Δ ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa [Δ,Fm.shift,Syn.shift] using (hr.shift.wk : Δ ⊢[PRAAx] (lt r (length R)).shift)
    have js : Δ ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift R)) := by simpa [Δ,Fm.shift,Syn.shift] using (hj.shift.wk : Δ ⊢[PRAAx] (lt j (length R)).shift)
    have actual := (scalar_body_at (Γ := Δ) (eliminator (Syn.shift R) (Syn.shift m)) (W (Syn.shift R) (Syn.shift m))
        (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
      ((qmul_congr (eliminator_lookup _ _ _ _ rms Prf.hyp0) (W_lookup _ _ _ _ Prf.hyp0 jms)).eqTrans
        ((elimination_term_head _ _ _ _ rs js).eqTrans (head_delta_at _ _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,subst_eliminator,GaussianRationalFiberVandermonde.subst_W,
      GaussianRationalMatrixFiniteSums.subst_scalarData,subst_pairT] using actual
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((head_sum _ _ _ _ hrm).eqTrans (GaussianRationalFiberVandermonde.weight_upper _ _ _ hr))

theorem dot_upper_right (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    scalarDot (eliminator R m) (W R m) m r j ≐ qzero := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody
      (pairedAddBody (GaussianRationalMatrixFiniteSums.deltaBody columnWeightBody) (GaussianRationalMatrixFiniteSums.deltaBody rowNegativeBody)) m
      (scalarData (eliminator R m) (W R m) r j) (pairT (pairT r (pairT R j)) (pairT j (pairT R r))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have rms : Δ ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hrm.shift.wk : Δ ⊢[PRAAx] (lt r m).shift)
    have jms : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hjm.shift.wk : Δ ⊢[PRAAx] (lt j m).shift)
    have rs : Δ ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa [Δ,Fm.shift,Syn.shift] using (hr.shift.wk : Δ ⊢[PRAAx] (lt r (length R)).shift)
    have js : Δ ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift j) := by simpa [Δ,Fm.shift,Syn.shift] using (hj.shift.wk : Δ ⊢[PRAAx] (le (length R) j).shift)
    have actual := (scalar_body_at (Γ := Δ) (eliminator (Syn.shift R) (Syn.shift m)) (W (Syn.shift R) (Syn.shift m))
        (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
      ((qmul_congr (eliminator_lookup _ _ _ _ rms Prf.hyp0) (W_lookup _ _ _ _ Prf.hyp0 jms)).eqTrans
        ((elimination_term_tail _ _ _ _ rs js).eqTrans
          ((qadd_congr (head_delta_at _ _ _ _).eqSymm (tail_delta_at _ _ _ _).eqSymm).eqTrans
            (paired_add_at _ _ _ _ _).eqSymm)))
    simpa only [Δ,Syn.shift,subst_eliminator,GaussianRationalFiberVandermonde.subst_W,
      GaussianRationalMatrixFiniteSums.subst_scalarData,subst_pairT] using actual
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((paired_sum_add _ _ _ _ _).eqTrans
      ((qadd_congr ((head_sum _ _ _ _ hrm).eqTrans (GaussianRationalFiberVandermonde.weight_upper _ _ _ hr))
        (tail_sum _ _ _ _ hjm)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)))

theorem dot_lower (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    scalarDot (eliminator R m) (W R m) m r j ≐ delta r j := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody (GaussianRationalMatrixFiniteSums.deltaBody columnWeightBody) m
      (scalarData (eliminator R m) (W R m) r j) (pairT r (pairT R j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have rms : Δ ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hrm.shift.wk : Δ ⊢[PRAAx] (lt r m).shift)
    have jms : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hjm.shift.wk : Δ ⊢[PRAAx] (lt j m).shift)
    have rs : Δ ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift r) := by simpa [Δ,Fm.shift,Syn.shift] using (hr.shift.wk : Δ ⊢[PRAAx] (le (length R) r).shift)
    have actual := (scalar_body_at (Γ := Δ) (eliminator (Syn.shift R) (Syn.shift m)) (W (Syn.shift R) (Syn.shift m))
        (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
      ((qmul_congr (eliminator_lookup _ _ _ _ rms Prf.hyp0) (W_lookup _ _ _ _ Prf.hyp0 jms)).eqTrans
        ((elimination_term_lower _ _ _ _ rs).eqTrans (head_delta_at _ _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,subst_eliminator,GaussianRationalFiberVandermonde.subst_W,
      GaussianRationalMatrixFiniteSums.subst_scalarData,subst_pairT] using actual
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((head_sum _ _ _ _ hrm).eqTrans (GaussianRationalFiberVandermonde.weight_lower _ _ _ hr))

theorem eliminator_upper (R m : PTm n) : Γ ⊢[PRAAx] belowZeros (eliminator R m) m := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let Δ := lt (var 0) (var 1) :: lt (var 0) (Syn.shift (Syn.shift m)) ::
    (lt (var 0) (Syn.shift m)).shift :: (Γ.map Fm.shift).map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa [Δ,Fm.shift,Syn.shift] using (Prf.hyp0.wk.wk : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
  have actual := eliminator_upper_at (Γ := Δ) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m))
    (var 1) (var 0) hr Prf.hyp1 Prf.hyp0
  simpa [Δ,belowZeros,GaussianScalarTriangularDeterminant.belowRow,Fm.shift,Syn.shift] using actual

theorem eliminator_diagonal_ones (R m : PTm n) : Γ ⊢[PRAAx] diagonalOnes (eliminator R m) m := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_eliminator] using
    eliminator_diagonal_at (Syn.shift R) (Syn.shift m) (var 0) Prf.hyp0

theorem eliminator_det (R m : PTm n) : Γ ⊢[PRAAx] scalarDet (eliminator R m) m ≐ qone :=
  GaussianScalarTriangularDeterminant.unit_triangular_det _ _ (.orI₁ (eliminator_upper _ _)) (eliminator_diagonal_ones _ _)

theorem eliminated_upper_left (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    cell (eliminated R m) r j ≐ power (entry R r) j :=
  (product_lookup _ _ _ _ _ hrm hjm).eqTrans (dot_upper_left _ _ _ _ hrm hjm hr hj)
theorem eliminated_upper_right (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    cell (eliminated R m) r j ≐ qzero :=
  (product_lookup _ _ _ _ _ hrm hjm).eqTrans (dot_upper_right _ _ _ _ hrm hjm hr hj)
theorem eliminated_lower (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    cell (eliminated R m) r j ≐ delta r j :=
  (product_lookup _ _ _ _ _ hrm hjm).eqTrans (dot_lower _ _ _ _ hrm hjm hr)
theorem eliminator_shape (R m : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (eliminator R m) m := by
  refine .andI (GaussianRationalFiberVandermonde.table_length _ _ _ _) (.allI (.impI ?_))
  simpa [Syn.shift,eliminator] using GaussianRationalFiberVandermonde.table_row_length
    (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) eliminatorBody (Syn.shift m) (Syn.shift m) (Syn.shift R) (var 0) Prf.hyp0
theorem eliminated_shape (R m : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (eliminated R m) m :=
  GaussianRationalMatrixFiniteSums.product_shape _ _ _

def output (R m : PTm n) : PTm n := pairT (eliminator R m) (pairT (eliminated R m)
  (pairT (scalarDet (eliminator R m) m) (W R m)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (R m : PTm n) : PTm n := app outputF ![R,m]
def fields (p : PTm n) : Fin 4 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (output R m) = output (Syn.subst σ R) (Syn.subst σ m) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (run R m) = run (Syn.subst σ R) (Syn.subst σ m) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (R m : PTm n) : Γ ⊢[PRAAx] run R m ≐ output R m := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![R,m]
theorem returned_fields (R m : PTm n) (i : Fin 4) : Γ ⊢[PRAAx] fields (run R m) i ≐
    ![eliminator R m,eliminated R m,scalarDet (eliminator R m) m,W R m] i := by
  have e0 := program_at (Γ := Γ) R m
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem returned_unit_det (R m : PTm n) : Γ ⊢[PRAAx] fields (run R m) 2 ≐ qone :=
  (returned_fields R m 2).eqTrans (eliminator_det R m)

theorem actual_tail_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (length (var 0)) ⟶ le (length (var 0)) (var 2) ⟶ eliminatorWeight (var 0) (var 1) (var 2) ≐
      qnegative (power (entry (var 0) (var 1)) (var 2))) := closeUniv 3 (.impI (.impI (eliminator_tail _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_head_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (length (var 0)) ⟶ lt (var 2) (length (var 0)) ⟶ eliminatorWeight (var 0) (var 1) (var 2) ≐ delta (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (eliminator_head _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_lower_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (length (var 0)) (var 1) ⟶ eliminatorWeight (var 0) (var 1) (var 2) ≐ delta (var 1) (var 2)) :=
  closeUniv 3 (.impI (eliminator_lower _ _ _ Prf.hyp0))
theorem actual_eliminator_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (belowZeros (eliminator (var 0) (var 1)) (var 1)) := closeUniv 2 (eliminator_upper _ _)
theorem actual_eliminator_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (eliminator (var 0) (var 1)) (var 1) ≐ qone) := closeUniv 2 (eliminator_det _ _)
theorem actual_upper_left_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ lt (var 3) (length (var 0)) ⟶
      cell (eliminated (var 0) (var 1)) (var 2) (var 3) ≐ power (entry (var 0) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (eliminated_upper_left _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_upper_right_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ le (length (var 0)) (var 3) ⟶
      cell (eliminated (var 0) (var 1)) (var 2) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (eliminated_upper_right _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_lower_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ le (length (var 0)) (var 2) ⟶
      cell (eliminated (var 0) (var 1)) (var 2) (var 3) ≐ delta (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (eliminated_lower _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_eliminator_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalMatrixFiniteSums.squareShape (eliminator (var 0) (var 1)) (var 1)) := closeUniv 2 (eliminator_shape _ _)
theorem actual_eliminated_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalMatrixFiniteSums.squareShape (eliminated (var 0) (var 1)) (var 1)) := closeUniv 2 (eliminated_shape _ _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_unit_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fields (run (var 0) (var 1)) 2 ≐ qone) := closeUniv 2 (returned_unit_det _ _)

end LeanProofs.IPRA.Analysis.GaussianVandermondeCompletionElimination
