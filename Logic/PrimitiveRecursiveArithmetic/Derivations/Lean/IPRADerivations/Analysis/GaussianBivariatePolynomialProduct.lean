import IPRADerivations.Analysis.GaussianPolynomialConstantInjection

/-!
# Actual multiplication of rectangular bivariate coefficient lists

Outer rows are descending Y coefficients. Each contribution is the actual
X-polynomial product of two original rows. A real polynomial-row addition
fold constructs each Y coefficient before either variable is specialized.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBivariatePolynomialProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialMonicCompanion (values values_length values_lookup rowShape row_shape_at evaluation_congr)
open GaussianPolynomialMultiplicationMatrix (stored)
open GaussianRationalHorner (evaluate hornerF qzero qadd qmul)
open GaussianRationalSyntheticDivision (canonicalCoefficients qadd_congr qmul_congr qmul_zero_right)
open GaussianRationalPolynomialBuffers (zeros zeros_length zeros_evaluation added added_length added_evaluation)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (monus pred)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def paddedRow (B q b i : PTm n) : PTm n :=
  sel (Signum.sg (monus (succ q) i)) (entry B i) (zeros (succ b))
def contribution (A B q a b k i : PTm n) : PTm n :=
  sel (Signum.sg (monus (succ k) i))
    (GaussianRationalPolynomialProduct.run (entry A i) (paddedRow B q b (monus k i)) a b) (zeros (succ (a+b)))
def data (A B q a b k : PTm n) : PTm n := pairT (GaussianPolynomialMonicCompanion.data A B q a b) k
def fields (p : PTm n) : Fin 6 → PTm n :=
  ![GaussianPolynomialConstantInjection.fields (fstT p) 0,GaussianPolynomialConstantInjection.fields (fstT p) 1,
    GaussianPolynomialConstantInjection.fields (fstT p) 2,GaussianPolynomialConstantInjection.fields (fstT p) 3,
    GaussianPolynomialConstantInjection.fields (fstT p) 4,sndT p]
def sumStep (A B q a b k i S : PTm n) : PTm n := added S (contribution A B q a b k i) (succ (a+b))
def initial : PTm 1 := zeros (succ (fields (var 0) 3+fields (var 0) 4))
def sumStepF : PR 8 := PTm.toPR (sumStep (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def stepBody : PTm 3 := app sumStepF ![fields (var 2) 0,fields (var 2) 1,fields (var 2) 2,
  fields (var 2) 3,fields (var 2) 4,fields (var 2) 5,var 0,var 1]
def rowSumF : PR 2 := rec2 initial stepBody
def rowSum (A B q a b k t : PTm n) : PTm n := ap2 rowSumF t (data A B q a b k)
def stageData (A B q a b t : PTm n) : PTm n := pairT (data A B q a b zero) t
def rowBody : PTm 2 := ap2 rowSumF (sndT (var 1)) (data (fields (fstT (var 1)) 0)
  (fields (fstT (var 1)) 1) (fields (fstT (var 1)) 2) (fields (fstT (var 1)) 3) (fields (fstT (var 1)) 4) (var 0))

def stage (A B q a b t : PTm n) : PTm n := sequence rowBody (q+t) (stageData A B q a b t)
def product (A B p q a b : PTm n) : PTm n := stage A B q a b (succ p)


@[simp] theorem subst_paddedRow {l : ℕ} (σ : Fin n → PTm l) (B q b i : PTm n) :
    Syn.subst σ (paddedRow B q b i) = paddedRow (Syn.subst σ B) (Syn.subst σ q) (Syn.subst σ b) (Syn.subst σ i) := by simp [paddedRow,sel,Signum.sg]
@[simp] theorem subst_contribution {l : ℕ} (σ : Fin n → PTm l) (A B q a b k i : PTm n) :
    Syn.subst σ (contribution A B q a b k i) = contribution (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ i) := by simp [contribution,sel,Signum.sg]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (A B q a b k : PTm n) :
    Syn.subst σ (data A B q a b k) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) := by simp [data]
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 6) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_sumStep {l : ℕ} (σ : Fin n → PTm l) (A B q a b k i S : PTm n) :
    Syn.subst σ (sumStep A B q a b k i S) = sumStep (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ i) (Syn.subst σ S) := by simp [sumStep]
@[simp] theorem subst_rowSum {l : ℕ} (σ : Fin n → PTm l) (A B q a b k t : PTm n) :
    Syn.subst σ (rowSum A B q a b k t) = rowSum (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ t) := by simp [rowSum]

theorem data_fields (A B q a b k : PTm n) (i : Fin 6) : Γ ⊢[PRAAx] fields (data A B q a b k) i ≐ ![A,B,q,a,b,k] i := by
  have base := fst_pair (Γ := Γ) (GaussianPolynomialMonicCompanion.data A B q a b) k
  have e (j : Fin 5) : Γ ⊢[PRAAx] GaussianPolynomialConstantInjection.fields (fstT (data A B q a b k)) j ≐ ![A,B,q,a,b] j := by
    have cong : Γ ⊢[PRAAx] GaussianPolynomialConstantInjection.fields (fstT (data A B q a b k)) j ≐
        GaussianPolynomialConstantInjection.fields (GaussianPolynomialMonicCompanion.data A B q a b) j := by
      simpa using Prf.eqCongr (Γ := Γ) (GaussianPolynomialConstantInjection.fields (var 0) j : PTm 1)
        (σ := ![fstT (data A B q a b k)]) (σ' := ![GaussianPolynomialMonicCompanion.data A B q a b]) (fun r => by fin_cases r; exact base)
    exact cong.eqTrans (GaussianPolynomialConstantInjection.fields_at _ _ _ _ _ j)
  fin_cases i
  · exact e 0
  · exact e 1
  · exact e 2
  · exact e 3
  · exact e 4
  · exact snd_pair _ _

theorem sel_congr {b b' u u' v v' : PTm n} (hb : Γ ⊢[PRAAx] b ≐ b') (hu : Γ ⊢[PRAAx] u ≐ u')
    (hv : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx] sel b u v ≐ sel b' u' v' := by
  simpa using Prf.eqCongr (Γ := Γ) (sel (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![b,u,v]) (σ' := ![b',u',v']) (fun i => by fin_cases i; exact hb; exact hu; exact hv)
theorem product_congr {A A' B B' a a' b b' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    GaussianRationalPolynomialProduct.product A B a b ≐ GaussianRationalPolynomialProduct.product A' B' a' b' :=
  (GaussianRationalPolynomialProduct.program_at A B a b).eqSymm.eqTrans
    ((congrApp GaussianRationalPolynomialProduct.productF (ts := ![A,B,a,b]) (us := ![A',B',a',b'])
      (fun i => by fin_cases i; exact hA; exact hB; exact ha; exact hb)).eqTrans (GaussianRationalPolynomialProduct.program_at A' B' a' b'))
theorem sg_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] Signum.sg a ≐ Signum.sg b :=
  congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)
theorem padded_row_congr {B B' q q' b b' i i' : PTm n} (hB : Γ ⊢[PRAAx] B ≐ B') (hq : Γ ⊢[PRAAx] q ≐ q')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] paddedRow B q b i ≐ paddedRow B' q' b' i' :=
  sel_congr (sg_congr (congrMonus (congrSucc hq) hi)) (entry_congr hB hi)
    (GaussianRationalMonicReduction.zeros_congr (congrSucc hb))
theorem contribution_congr {A A' B B' q q' a a' b b' k k' i i' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hq : Γ ⊢[PRAAx] q ≐ q')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hk : Γ ⊢[PRAAx] k ≐ k') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    contribution A B q a b k i ≐ contribution A' B' q' a' b' k' i' :=
  sel_congr (sg_congr (congrMonus (congrSucc hk) hi))
    (congrApp GaussianRationalPolynomialProduct.productF
      (ts := ![entry A i,paddedRow B q b (monus k i),a,b])
      (us := ![entry A' i',paddedRow B' q' b' (monus k' i'),a',b'])
      (fun j => by fin_cases j; exact entry_congr hA hi; exact padded_row_congr hB hq hb (congrMonus hk hi); exact ha; exact hb))
    (GaussianRationalMonicReduction.zeros_congr (congrSucc (congrAdd ha hb)))
theorem sum_step_parameters (p : PTm n) (A B q a b k i S : PTm n)
    (h : ∀ j : Fin 6, Γ ⊢[PRAAx] fields p j ≐ ![A,B,q,a,b,k] j) : Γ ⊢[PRAAx]
    sumStep (fields p 0) (fields p 1) (fields p 2) (fields p 3) (fields p 4) (fields p 5) i S ≐ sumStep A B q a b k i S := by
  have hc : Γ ⊢[PRAAx] contribution (fields p 0) (fields p 1) (fields p 2) (fields p 3) (fields p 4) (fields p 5) i ≐
      contribution A B q a b k i := contribution_congr (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (.eqRefl i)
  have hw : Γ ⊢[PRAAx] succ (fields p 3+fields p 4) ≐ succ (a+b) := congrSucc (congrAdd (h 3) (h 4))
  exact congrPairT hw (congrAp2 (LeanProofs.IPRA.Foundations.MasterCertificate.stackF GaussianRationalPolynomialBuffers.addBody)
    hw (congrPairT (.eqRefl S) hc))
theorem row_sum_zero (A B q a b k : PTm n) : Γ ⊢[PRAAx] rowSum A B q a b k zero ≐ zeros (succ (a+b)) := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data A B q a b k)
  simp only [initial,GaussianRationalPolynomialBuffers.subst_zeros,ConciseIPRA.PTm.subst_succ,subst_fields,
    Syn.subst_var,Syn.inst_zero,LeanProofs.IPRA.PTm.subst_add] at e
  exact e.eqTrans (GaussianRationalMonicReduction.zeros_congr (congrSucc (congrAdd (data_fields A B q a b k 3) (data_fields A B q a b k 4))))
theorem sum_step_program (A B q a b k i S : PTm n) : Γ ⊢[PRAAx]
    app sumStepF ![A,B,q,a,b,k,i,S] ≐ sumStep A B q a b k i S := by
  simpa [sumStepF] using toPR_eq (Γ := Γ) (sumStep (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![A,B,q,a,b,k,i,S]
theorem row_sum_succ (A B q a b k t : PTm n) : Γ ⊢[PRAAx] rowSum A B q a b k (succ t) ≐
    added (rowSum A B q a b k t) (contribution A B q a b k t) (succ (a+b)) := by
  let d := data A B q a b k
  let S := rowSum A B q a b k t
  have vector : (fun i => Syn.subst ![t,S,d]
      ((![fields (var 2) 0,fields (var 2) 1,fields (var 2) 2,fields (var 2) 3,fields (var 2) 4,fields (var 2) 5,var 0,var 1] : Fin 8 → PTm 3) i)) =
      ![fields d 0,fields d 1,fields d 2,fields d 3,fields d 4,fields d 5,t,S] := by
    funext i
    fin_cases i <;> simp
  have e := rec2_succ (Γ := Γ) initial stepBody t d
  change Γ ⊢[PRAAx] ap2 (rec2 initial stepBody) (succ t) d ≐ app sumStepF (fun i => Syn.subst ![t,S,d]
    ((![fields (var 2) 0,fields (var 2) 1,fields (var 2) 2,fields (var 2) 3,fields (var 2) 4,fields (var 2) 5,var 0,var 1] : Fin 8 → PTm 3) i)) at e
  rw [vector] at e
  exact e.eqTrans ((sum_step_program _ _ _ _ _ _ _ _).eqTrans
    (sum_step_parameters d A B q a b k t S (data_fields A B q a b k)))
theorem row_sum_index {A B q a b k t u : PTm n} (h : Γ ⊢[PRAAx] t ≐ u) : Γ ⊢[PRAAx]
    rowSum A B q a b k t ≐ rowSum A B q a b k u := congrAp2 rowSumF h (.eqRefl _)
theorem row_sum_length (A B q a b k t : PTm n) : Γ ⊢[PRAAx] length (rowSum A B q a b k t) ≐ succ (a+b) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact (congrFst ((row_sum_index (A := A) (B := B) (q := q) (a := a) (b := b) (k := k) Prf.hyp0).eqTrans (row_sum_zero A B q a b k))).eqTrans (zeros_length _)
  · exact (congrFst ((row_sum_index (A := A) (B := B) (q := q) (a := a) (b := b) (k := k) Prf.hyp0).eqTrans (row_sum_succ A B q a b k (pred t)))).eqTrans (added_length _ _ _)
theorem row_sum_canonical (A B q a b k t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (rowSum A B q a b k t) := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr
      ((row_sum_index (A := A) (B := B) (q := q) (a := a) (b := b) (k := k) Prf.hyp0).eqTrans (row_sum_zero A B q a b k)) (GaussianRationalMonicReduction.zeros_canonical _)
  · exact GaussianRationalMonicReduction.canonical_coefficients_congr
      ((row_sum_index (A := A) (B := B) (q := q) (a := a) (b := b) (k := k) Prf.hyp0).eqTrans (row_sum_succ A B q a b k (pred t))) (GaussianRationalMonicReduction.added_canonical _ _ _)

theorem padded_row_inside (B q b i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ q)) : Γ ⊢[PRAAx]
    paddedRow B q b i ≐ entry B i := sel_one (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem padded_row_outside (B q b i : PTm n) (hi : Γ ⊢[PRAAx] le (succ q) i) : Γ ⊢[PRAAx]
    paddedRow B q b i ≐ zeros (succ b) := sel_zero (AnalyticNumberTheory.Totatives.sg_le hi)
theorem padded_row_length (B q b i : PTm n) (hB : Γ ⊢[PRAAx] rowShape B (succ q) b) : Γ ⊢[PRAAx]
    length (paddedRow B q b i) ≐ succ b := by
  refine .orE (lt_or_le i (succ q)) ?_ ?_
  · exact (congrFst (padded_row_inside _ _ _ _ Prf.hyp0)).eqTrans (row_shape_at _ _ _ _ hB.wk Prf.hyp0)
  · exact (congrFst (padded_row_outside _ _ _ _ Prf.hyp0)).eqTrans (zeros_length _)
theorem contribution_inside (A B q a b k i : PTm n) (hi : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx]
    contribution A B q a b k i ≐ GaussianRationalPolynomialProduct.product (entry A i) (paddedRow B q b (monus k i)) a b :=
  (sel_one (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans hi))).eqTrans
    (GaussianRationalPolynomialProduct.program_at _ _ _ _)
theorem contribution_outside (A B q a b k i : PTm n) (hi : Γ ⊢[PRAAx] lt k i) : Γ ⊢[PRAAx]
    contribution A B q a b k i ≐ zeros (succ (a+b)) := sel_zero (AnalyticNumberTheory.Totatives.sg_le hi)
theorem contribution_length (A B q a b k i : PTm n) : Γ ⊢[PRAAx] length (contribution A B q a b k i) ≐ succ (a+b) := by
  refine .orE (GaussianRationalMonicReconstruction.le_or_lt i k) ?_ ?_
  · exact (congrFst (contribution_inside _ _ _ _ _ _ _ Prf.hyp0)).eqTrans (GaussianRationalPolynomialProduct.product_length _ _ _ _)
  · exact (congrFst (contribution_outside _ _ _ _ _ _ _ Prf.hyp0)).eqTrans (zeros_length _)

theorem padded_row_evaluation (B q b i x : PTm n) : Γ ⊢[PRAAx] evaluate (paddedRow B q b i) x ≐
    GaussianRationalLinearProduct.padded (values B (succ q) x) (succ q) i := by
  refine .orE (lt_or_le i (succ q)) ?_ ?_
  · exact (evaluation_congr (padded_row_inside _ _ _ _ Prf.hyp0) (.eqRefl x)).eqTrans
      ((values_lookup B (succ q) x i Prf.hyp0).eqSymm.eqTrans (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0).eqSymm)
  · exact (evaluation_congr (padded_row_outside _ _ _ _ Prf.hyp0) (.eqRefl x)).eqTrans
      ((zeros_evaluation _ _).eqTrans (GaussianRationalLinearProduct.padded_outside _ _ _ Prf.hyp0).eqSymm)
theorem contribution_evaluation (A B P q a b k i x : PTm n) (hA : Γ ⊢[PRAAx] rowShape A P a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ q) b) (hi : Γ ⊢[PRAAx] lt i P) : Γ ⊢[PRAAx]
    evaluate (contribution A B q a b k i) x ≐
      GaussianRationalPolynomialProduct.contribution (values A P x) (values B (succ q) x) q k i := by
  refine .orE (GaussianRationalMonicReconstruction.le_or_lt i k) ?_ ?_
  · exact (evaluation_congr (contribution_inside _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl x)).eqTrans
      ((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (row_shape_at _ _ _ _ hA.wk hi.wk)
        (padded_row_length _ _ _ _ hB.wk)).eqTrans
          ((qmul_congr (values_lookup A P x i hi.wk).eqSymm (padded_row_evaluation _ _ _ _ _)).eqTrans
            (GaussianRationalPolynomialProduct.contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm))
  · exact (evaluation_congr (contribution_outside _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl x)).eqTrans
      ((zeros_evaluation _ _).eqTrans (GaussianRationalPolynomialProduct.contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm)

def rowEvaluationLaw (A B P q a b k x t : PTm n) : Fm PTm n := le t P ⟶
  evaluate (rowSum A B q a b k t) x ≐ GaussianRationalPolynomialProduct.coefficient (values A P x) (values B (succ q) x) q t k
@[simp] theorem subst_rowEvaluationLaw {l : ℕ} (σ : Fin n → PTm l) (A B P q a b k x t : PTm n) :
    (rowEvaluationLaw A B P q a b k x t).subst σ = rowEvaluationLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ P)
      (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ t) := by simp [rowEvaluationLaw]
theorem row_sum_evaluation (A B P q a b k x t : PTm n) (hA : Γ ⊢[PRAAx] rowShape A P a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ q) b) (ht : Γ ⊢[PRAAx] le t P) : Γ ⊢[PRAAx]
    evaluate (rowSum A B q a b k t) x ≐ GaussianRationalPolynomialProduct.coefficient (values A P x) (values B (succ q) x) q t k := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift A) (Syn.shift P) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have hBs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift B) (succ (Syn.shift q)) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (rowEvaluationLaw (Syn.shift A) (Syn.shift B) (Syn.shift P) (Syn.shift q) (Syn.shift a)
      (Syn.shift b) (Syn.shift k) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_rowEvaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((evaluation_congr (row_sum_zero A B q a b k) (.eqRefl _)).eqTrans
        ((zeros_evaluation _ _).eqTrans (GaussianRationalPolynomialProduct.coefficient_zero _ _ _ _).eqSymm)).wk
    · simp only [subst_rowEvaluationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift P) :: rowEvaluationLaw (Syn.shift A) (Syn.shift B) (Syn.shift P)
        (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (Syn.shift x) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] evaluate (rowSum (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0))
          (Syn.shift x) ≐ GaussianRationalPolynomialProduct.coefficient (values (Syn.shift A) (Syn.shift P) (Syn.shift x))
            (values (Syn.shift B) (succ (Syn.shift q)) (Syn.shift x)) (Syn.shift q) (var 0) (Syn.shift k) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have next := (evaluation_congr (row_sum_succ (Γ := Δ) (Syn.shift A) (Syn.shift B) (Syn.shift q)
        (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0)) (.eqRefl (Syn.shift x))).eqTrans
        (added_evaluation _ _ _ (Syn.shift x)
          (row_sum_length (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0))
          (contribution_length (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0)))
      exact next.eqTrans ((qadd_congr ih (contribution_evaluation _ _ _ _ _ _ _ _ _ hAs.wk.wk hBs.wk.wk Prf.hyp0)).eqTrans
        (GaussianRationalPolynomialProduct.coefficient_succ _ _ _ _ _).eqSymm)
  have atT : Γ ⊢[PRAAx] rowEvaluationLaw A B P q a b k x t := by
    simpa only [subst_rowEvaluationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE atT ht

@[simp] theorem subst_stageData {l : ℕ} (σ : Fin n → PTm l) (A B q a b t : PTm n) :
    Syn.subst σ (stageData A B q a b t) = stageData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ t) := by simp [stageData]
@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (A B q a b t : PTm n) :
    Syn.subst σ (stage A B q a b t) = stage (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ t) := by simp [stage]
@[simp] theorem subst_product {l : ℕ} (σ : Fin n → PTm l) (A B p q a b : PTm n) :
    Syn.subst σ (product A B p q a b) = product (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p)
      (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) := by simp [product]
theorem stage_data_field (A B q a b t : PTm n) (j : Fin 6) : Γ ⊢[PRAAx]
    fields (fstT (stageData A B q a b t)) j ≐ ![A,B,q,a,b,zero] j := by
  have e : Γ ⊢[PRAAx] fields (fstT (stageData A B q a b t)) j ≐ fields (data A B q a b zero) j := by
    simpa using Prf.eqCongr (Γ := Γ) (fields (var 0) j : PTm 1)
      (σ := ![fstT (stageData A B q a b t)]) (σ' := ![data A B q a b zero]) (fun i => by fin_cases i; exact fst_pair _ _)
  exact e.eqTrans (data_fields _ _ _ _ _ _ j)
theorem data_congr {A A' B B' q q' a a' b b' k k' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hB : Γ ⊢[PRAAx] B ≐ B') (hq : Γ ⊢[PRAAx] q ≐ q') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] data A B q a b k ≐ data A' B' q' a' b' k' :=
  congrPairT (congrPairT hA (congrPairT hB (congrPairT hq (congrPairT ha hb)))) hk
theorem row_body_at (A B q a b t k : PTm n) : Γ ⊢[PRAAx] inst2 rowBody k (stageData A B q a b t) ≐ rowSum A B q a b k t := by
  simp only [rowBody,inst2,subst_ap2,subst_data,subst_fields,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp2 rowSumF (snd_pair _ _) (data_congr (stage_data_field A B q a b t 0) (stage_data_field A B q a b t 1)
    (stage_data_field A B q a b t 2) (stage_data_field A B q a b t 3) (stage_data_field A B q a b t 4) (.eqRefl k))
theorem stage_length (A B q a b t : PTm n) : Γ ⊢[PRAAx] length (stage A B q a b t) ≐ q+t := sequence_length _ _ _
theorem stage_lookup (A B q a b t k : PTm n) (hk : Γ ⊢[PRAAx] lt k (q+t)) : Γ ⊢[PRAAx]
    entry (stage A B q a b t) k ≐ rowSum A B q a b k t := (sequence_decode rowBody hk).eqTrans (row_body_at _ _ _ _ _ _ _)
theorem stage_stored (A B q a b t : PTm n) : Γ ⊢[PRAAx] stored (stage A B q a b t) (q+t) (a+b) := by
  refine .andI (stage_length _ _ _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa only [Syn.shift,subst_stage,length,PTm.subst_add] using (congrFst (stage_lookup (Syn.shift A) (Syn.shift B) (Syn.shift q)
      (Syn.shift a) (Syn.shift b) (Syn.shift t) (var 0) Prf.hyp0)).eqTrans (row_sum_length _ _ _ _ _ _ _)
  · simpa only [Syn.shift,subst_stage,PTm.subst_add] using GaussianRationalMonicReduction.canonical_coefficients_congr
      (stage_lookup (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift t) (var 0) Prf.hyp0)
      (row_sum_canonical _ _ _ _ _ _ _)
theorem product_length (A B p q a b : PTm n) : Γ ⊢[PRAAx] length (product A B p q a b) ≐ succ (p+q) :=
  (stage_length _ _ _ _ _ _).eqTrans (by ipra_ring)
theorem product_lookup (A B p q a b k : PTm n) (hk : Γ ⊢[PRAAx] le k (p+q)) : Γ ⊢[PRAAx]
    entry (product A B p q a b) k ≐ rowSum A B q a b k (succ p) :=
  stage_lookup _ _ _ _ _ _ _ (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ (p+q) ≐ q+succ p) ((succ_monus_succ _ _).eqTrans hk))
theorem product_stored (A B p q a b : PTm n) : Γ ⊢[PRAAx] stored (product A B p q a b) (succ (p+q)) (a+b) :=
  GaussianPolynomialMultiplicationMatrix.stored_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) (stage_stored _ _ _ _ _ _)
theorem specialized_lookup (A B p q a b x k : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ p) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ q) b) (hk : Γ ⊢[PRAAx] le k (p+q)) : Γ ⊢[PRAAx]
    entry (values (product A B p q a b) (succ (p+q)) x) k ≐
      entry (GaussianRationalPolynomialProduct.product (values A (succ p) x) (values B (succ q) x) p q) k :=
  (values_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hk)).eqTrans
    ((evaluation_congr (product_lookup _ _ _ _ _ _ _ hk) (.eqRefl _)).eqTrans
      ((row_sum_evaluation A B (succ p) q a b k x (succ p) hA hB (le_refl _)).eqTrans
        (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _ hk).eqSymm))
theorem product_evaluation (A B p q a b x y : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ p) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ q) b) : Γ ⊢[PRAAx]
    evaluate (values (product A B p q a b) (succ (p+q)) x) y ≐
      qmul (evaluate (values A (succ p) x) y) (evaluate (values B (succ q) x) y) := by
  let C := values (product A B p q a b) (succ (p+q)) x
  let D := GaussianRationalPolynomialProduct.product (values A (succ p) x) (values B (succ q) x) p q
  have hAs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift A) (succ (Syn.shift p)) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have hBs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift B) (succ (Syn.shift q)) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ (p+q))) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift p+Syn.shift q)) :: Γ.map Fm.shift
    have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift p+Syn.shift q) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have e := specialized_lookup (Γ := Δ) (Syn.shift A) (Syn.shift B) (Syn.shift p) (Syn.shift q)
      (Syn.shift a) (Syn.shift b) (Syn.shift x) (var 0) hAs.wk hBs.wk bound
    simpa only [C,D,Δ,Syn.shift,subst_product,GaussianPolynomialMonicCompanion.subst_values,
      GaussianRationalPolynomialProduct.subst_product,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using e
  exact (congrAp3 hornerF (values_length _ _ _) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext C D y (succ (p+q)) (succ (p+q)) entries (le_refl _)).eqTrans
      ((congrAp3 hornerF (GaussianRationalPolynomialProduct.product_length _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
        (GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (values_length _ _ _) (values_length _ _ _))))

def coefficientData (A B q a b k s : PTm n) : PTm n := pairT (data A B q a b k) s
def coefficientBody : PTm 2 := entry (contribution (fields (fstT (var 1)) 0) (fields (fstT (var 1)) 1)
  (fields (fstT (var 1)) 2) (fields (fstT (var 1)) 3) (fields (fstT (var 1)) 4) (fields (fstT (var 1)) 5) (var 0)) (sndT (var 1))
def coefficient (A B q a b k s t : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum coefficientBody t (coefficientData A B q a b k s)
@[simp] theorem subst_coefficientData {l : ℕ} (σ : Fin n → PTm l) (A B q a b k s : PTm n) :
    Syn.subst σ (coefficientData A B q a b k s) = coefficientData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ s) := by simp [coefficientData]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (A B q a b k s t : PTm n) :
    Syn.subst σ (coefficient A B q a b k s t) = coefficient (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ t) := by simp [coefficient]
theorem pair_fields (p s : PTm n) (j : Fin 6) : Γ ⊢[PRAAx] fields (fstT (pairT p s)) j ≐ fields p j := by
  simpa using Prf.eqCongr (Γ := Γ) (fields (var 0) j : PTm 1)
    (σ := ![fstT (pairT p s)]) (σ' := ![p]) (fun i => by fin_cases i; exact fst_pair _ _)
theorem coefficient_body_at (A B q a b k s i : PTm n) : Γ ⊢[PRAAx]
    inst2 coefficientBody i (coefficientData A B q a b k s) ≐ entry (contribution A B q a b k i) s := by
  simp only [coefficientBody,inst2,Foundations.MasterCertificate.subst_entry,subst_contribution,subst_fields,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have f (j : Fin 6) : Γ ⊢[PRAAx] fields (fstT (coefficientData A B q a b k s)) j ≐ ![A,B,q,a,b,k] j :=
    (pair_fields (data A B q a b k) s j).eqTrans (data_fields _ _ _ _ _ _ j)
  exact entry_congr (contribution_congr (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (.eqRefl _)) (snd_pair _ _)
theorem row_sum_coefficient (A B q a b k s t : PTm n) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    entry (rowSum A B q a b k t) s ≐ coefficient A B q a b k s t := by
  have hss : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift s) (Syn.shift a+Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (entry (rowSum (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0))
      (Syn.shift s) ≐ coefficient (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (Syn.shift s) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,Foundations.MasterCertificate.subst_entry,subst_rowSum,subst_coefficient,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (entry_congr (row_sum_zero A B q a b k) (.eqRefl _)).eqTrans
        ((GaussianRationalPolynomialBuffers.zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs)).eqTrans
          (GaussianRationalFiniteSum.sum_zero coefficientBody (coefficientData A B q a b k s)).eqSymm)
    · simp only [Fm.subst_eq,Foundations.MasterCertificate.subst_entry,subst_rowSum,subst_coefficient,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := (entry (rowSum (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0))
        (Syn.shift s) ≐ coefficient (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (Syn.shift s) (var 0)) :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (Syn.shift s) (Syn.shift a+Syn.shift b) := hss.wk
      have step := (entry_congr (row_sum_succ (Γ := Δ) (Syn.shift A) (Syn.shift B) (Syn.shift q)
        (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0)) (.eqRefl (Syn.shift s))).eqTrans
        (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans bound))

      exact step.eqTrans ((qadd_congr Prf.hyp0 (coefficient_body_at _ _ _ _ _ _ _ _).eqSymm).eqTrans
        (GaussianRationalFiniteSum.sum_succ _ _ _).eqSymm)
  simpa only [Fm.subst_eq,Foundations.MasterCertificate.subst_entry,subst_rowSum,subst_coefficient,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem product_coefficient (A B p q a b k s : PTm n) (hk : Γ ⊢[PRAAx] le k (p+q)) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    entry (entry (product A B p q a b) k) s ≐ coefficient A B q a b k s (succ p) :=
  (entry_congr (product_lookup _ _ _ _ _ _ _ hk) (.eqRefl _)).eqTrans (row_sum_coefficient _ _ _ _ _ _ _ _ hs)

def input (A B p q a b : PTm n) : Fm PTm n := (length A ≐ succ p) ⋏
  (rowShape A (succ p) a ⋏ ((length B ≐ succ q) ⋏ rowShape B (succ q) b))
def productF : PR 6 := PTm.toPR (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (A B p q a b : PTm n) : PTm n := app productF ![A,B,p,q,a,b]
theorem program_at (A B p q a b : PTm n) : Γ ⊢[PRAAx] run A B p q a b ≐ product A B p q a b := by
  simpa [run,productF] using toPR_eq (Γ := Γ) (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![A,B,p,q,a,b]
theorem returned_stored (A B p q a b : PTm n) : Γ ⊢[PRAAx] stored (run A B p q a b) (succ (p+q)) (a+b) :=
  GaussianPolynomialMultiplicationMatrix.stored_congr (program_at _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (product_stored _ _ _ _ _ _)
theorem original_product_evaluation (A B p q a b x y : PTm n) (h : Γ ⊢[PRAAx] input A B p q a b) : Γ ⊢[PRAAx]
    evaluate (values (product A B p q a b) (succ (p+q)) x) y ≐
      qmul (evaluate (values A (length A) x) y) (evaluate (values B (length B) x) y) :=
  (product_evaluation _ _ _ _ _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ (.andE₂ h)))).eqTrans
    (qmul_congr (evaluation_congr (GaussianPolynomialMonicCompanion.values_congr (.eqRefl _) (Prf.andE₁ h).eqSymm (.eqRefl _)) (.eqRefl _))
      (evaluation_congr (GaussianPolynomialMonicCompanion.values_congr (.eqRefl _) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).eqSymm (.eqRefl _)) (.eqRefl _)))
theorem returned_evaluation (A B p q a b x y : PTm n) (h : Γ ⊢[PRAAx] input A B p q a b) : Γ ⊢[PRAAx]
    evaluate (values (run A B p q a b) (succ (p+q)) x) y ≐
      qmul (evaluate (values A (length A) x) y) (evaluate (values B (length B) x) y) :=
  (evaluation_congr (GaussianPolynomialMonicCompanion.values_congr (program_at _ _ _ _ _ _) (.eqRefl _) (.eqRefl _)) (.eqRefl _)).eqTrans
    (original_product_evaluation _ _ _ _ _ _ _ _ h)

theorem actual_bivariate_product_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (stored (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 4+var 5)) :=
  closeUniv 6 (product_stored _ _ _ _ _ _)
theorem actual_bivariate_convolution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 6) (var 2+var 3) ⟶ le (var 7) (var 4+var 5) ⟶
      entry (entry (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7) ≐
        coefficient (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (succ (var 2))) :=
  closeUniv 8 (.impI (.impI (product_coefficient _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_bivariate_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (rowShape (var 0) (succ (var 2)) (var 4) ⟶ rowShape (var 1) (succ (var 3)) (var 5) ⟶
      le (var 7) (var 2+var 3) ⟶ entry (values (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (succ (var 2+var 3)) (var 6)) (var 7) ≐
        entry (GaussianRationalPolynomialProduct.product (values (var 0) (succ (var 2)) (var 6))
          (values (var 1) (succ (var 3)) (var 6)) (var 2) (var 3)) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (specialized_lookup _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_bivariate_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      evaluate (values (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 6)) (var 7) ≐
        qmul (evaluate (values (var 0) (length (var 0)) (var 6)) (var 7)) (evaluate (values (var 1) (length (var 1)) (var 6)) (var 7))) :=
  closeUniv 8 (.impI (original_product_evaluation _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_bivariate_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_bivariate_stored_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (stored (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 4+var 5)) := closeUniv 6 (returned_stored _ _ _ _ _ _)
theorem actual_returned_bivariate_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      evaluate (values (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 6)) (var 7) ≐
        qmul (evaluate (values (var 0) (length (var 0)) (var 6)) (var 7)) (evaluate (values (var 1) (length (var 1)) (var 6)) (var 7))) :=
  closeUniv 8 (.impI (returned_evaluation _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBivariatePolynomialProduct
