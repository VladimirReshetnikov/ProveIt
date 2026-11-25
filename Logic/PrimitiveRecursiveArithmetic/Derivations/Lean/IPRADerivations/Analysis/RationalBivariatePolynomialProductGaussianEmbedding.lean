import IPRADerivations.Analysis.RationalBivariatePolynomialBuffersGaussianEmbedding
import IPRADerivations.Analysis.GaussianBivariatePolynomialProduct
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Actual original rational bivariate convolution

Each Y-row contribution is an actual original rational X-polynomial product.
A genuine original coefficient-buffer addition recursor accumulates the row
before either variable is specialized. Original bounded row coefficients
transport the true fold to the existing Gaussian convolution.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalBivariatePolynomialProductGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (zeros zeros_length added added_length added_lookup embeddedEntries)
open RationalPolynomialMonicCompanionGaussianEmbedding (rowsEmbedded row_embedded_at embedded_at)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (monus pred)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zeros_congr {A B : PTm n} (h : Γ ⊢[PRAAx] A ≐ B) : Γ ⊢[PRAAx] zeros A ≐ zeros B :=
  (RationalPolynomialBuffersGaussianEmbedding.zeros_at A).eqSymm.eqTrans
    ((congrAp1 RationalPolynomialBuffersGaussianEmbedding.zerosF h).eqTrans (RationalPolynomialBuffersGaussianEmbedding.zeros_at B))

def paddedRow (B q b i : PTm n) : PTm n :=
  sel (Signum.sg (monus (succ q) i)) (entry B i) (zeros (succ b))
def contribution (A B q a b k i : PTm n) : PTm n :=
  sel (Signum.sg (monus (succ k) i))
    (RationalPolynomialProductGaussianEmbedding.run (entry A i) (paddedRow B q b (monus k i)) a b) (zeros (succ (a+b)))
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
      ipra_congr (GaussianPolynomialConstantInjection.fields (var 0) j : PTm 1) with
        [(show _ ⊢[PRAAx] fstT (data A B q a b k) ≐ GaussianPolynomialMonicCompanion.data A B q a b from base)]
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
  ipra_congr (sel (var 0) (var 1) (var 2) : PTm 3) with [hb, hu, hv]
theorem product_congr {A A' B B' a a' b b' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    RationalPolynomialProductGaussianEmbedding.product A B a b ≐ RationalPolynomialProductGaussianEmbedding.product A' B' a' b' :=
  (RationalPolynomialProductGaussianEmbedding.program_at A B a b).eqSymm.eqTrans
    ((congrApp RationalPolynomialProductGaussianEmbedding.productF (ts := ![A,B,a,b]) (us := ![A',B',a',b'])
      (fun i => by fin_cases i; exact hA; exact hB; exact ha; exact hb)).eqTrans (RationalPolynomialProductGaussianEmbedding.program_at A' B' a' b'))
alias sg_congr := Common.congrSg
theorem padded_row_congr {B B' q q' b b' i i' : PTm n} (hB : Γ ⊢[PRAAx] B ≐ B') (hq : Γ ⊢[PRAAx] q ≐ q')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] paddedRow B q b i ≐ paddedRow B' q' b' i' :=
  sel_congr (sg_congr (congrMonus (congrSucc hq) hi)) (entry_congr hB hi)
    (zeros_congr (congrSucc hb))
theorem contribution_congr {A A' B B' q q' a a' b b' k k' i i' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hq : Γ ⊢[PRAAx] q ≐ q')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hk : Γ ⊢[PRAAx] k ≐ k') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    contribution A B q a b k i ≐ contribution A' B' q' a' b' k' i' :=
  sel_congr (sg_congr (congrMonus (congrSucc hk) hi))
    (congrApp RationalPolynomialProductGaussianEmbedding.productF
      (ts := ![entry A i,paddedRow B q b (monus k i),a,b])
      (us := ![entry A' i',paddedRow B' q' b' (monus k' i'),a',b'])
      (fun j => by fin_cases j; exact entry_congr hA hi; exact padded_row_congr hB hq hb (congrMonus hk hi); exact ha; exact hb))
    (zeros_congr (congrSucc (congrAdd ha hb)))
theorem sum_step_parameters (p : PTm n) (A B q a b k i S : PTm n)
    (h : ∀ j : Fin 6, Γ ⊢[PRAAx] fields p j ≐ ![A,B,q,a,b,k] j) : Γ ⊢[PRAAx]
    sumStep (fields p 0) (fields p 1) (fields p 2) (fields p 3) (fields p 4) (fields p 5) i S ≐ sumStep A B q a b k i S := by
  have hc : Γ ⊢[PRAAx] contribution (fields p 0) (fields p 1) (fields p 2) (fields p 3) (fields p 4) (fields p 5) i ≐
      contribution A B q a b k i := contribution_congr (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (.eqRefl i)
  have hw : Γ ⊢[PRAAx] succ (fields p 3+fields p 4) ≐ succ (a+b) := congrSucc (congrAdd (h 3) (h 4))
  exact congrPairT hw (congrAp2 (LeanProofs.IPRA.Foundations.MasterCertificate.stackF RationalPolynomialBuffersGaussianEmbedding.addBody)
    hw (congrPairT (.eqRefl S) hc))
theorem row_sum_zero (A B q a b k : PTm n) : Γ ⊢[PRAAx] rowSum A B q a b k zero ≐ zeros (succ (a+b)) := by
  have e := rec2_zero (Γ := Γ) initial stepBody (data A B q a b k)
  simp only [initial,RationalPolynomialBuffersGaussianEmbedding.subst_zeros,ConciseIPRA.PTm.subst_succ,subst_fields,
    Syn.subst_var,LeanProofs.IPRA.PTm.subst_add] at e
  exact e.eqTrans (zeros_congr (congrSucc (congrAdd (data_fields A B q a b k 3) (data_fields A B q a b k 4))))
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
    contribution A B q a b k i ≐ RationalPolynomialProductGaussianEmbedding.product (entry A i) (paddedRow B q b (monus k i)) a b :=
  (sel_one (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans hi))).eqTrans
    (RationalPolynomialProductGaussianEmbedding.program_at _ _ _ _)
theorem contribution_outside (A B q a b k i : PTm n) (hi : Γ ⊢[PRAAx] lt k i) : Γ ⊢[PRAAx]
    contribution A B q a b k i ≐ zeros (succ (a+b)) := sel_zero (AnalyticNumberTheory.Totatives.sg_le hi)
theorem contribution_length (A B q a b k i : PTm n) : Γ ⊢[PRAAx] length (contribution A B q a b k i) ≐ succ (a+b) := by
  refine .orE (GaussianRationalMonicReconstruction.le_or_lt i k) ?_ ?_
  · exact (congrFst (contribution_inside _ _ _ _ _ _ _ Prf.hyp0)).eqTrans (RationalPolynomialProductGaussianEmbedding.product_length _ _ _ _)
  · exact (congrFst (contribution_outside _ _ _ _ _ _ _ Prf.hyp0)).eqTrans (zeros_length _)

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
    ipra_congr (fields (var 0) j : PTm 1) with
      [(show _ ⊢[PRAAx] fstT (stageData A B q a b t) ≐ data A B q a b zero from fst_pair _ _)]
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


theorem stage_shape (A B q a b t : PTm n) : Γ ⊢[PRAAx] rowShape (stage A B q a b t) (q+t) (a+b) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_stage,length,PTm.subst_add] using
    (congrFst (stage_lookup (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift t) (var 0) Prf.hyp0)).eqTrans
      (row_sum_length _ _ _ _ _ _ _)
theorem product_length (A B p q a b : PTm n) : Γ ⊢[PRAAx] length (product A B p q a b) ≐ succ (p+q) :=
  (stage_length _ _ _ _ _ _).eqTrans (by ipra_ring)
theorem product_lookup (A B p q a b k : PTm n) (hk : Γ ⊢[PRAAx] le k (p+q)) : Γ ⊢[PRAAx]
    entry (product A B p q a b) k ≐ rowSum A B q a b k (succ p) :=
  stage_lookup _ _ _ _ _ _ _ (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ (p+q) ≐ q+succ p) ((succ_monus_succ _ _).eqTrans hk))
theorem product_shape (A B p q a b : PTm n) : Γ ⊢[PRAAx] rowShape (product A B p q a b) (succ (p+q)) (a+b) := by
  have out := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (rowShape (var 0) (var 1) (var 2) : Fm PTm 3)
    ![stage A B q a b (succ p),q+succ p,a+b] ![product A B p q a b,succ (p+q),a+b]
    (fun i => by
      fin_cases i
      · exact .eqRefl _
      · simpa using (show Γ ⊢[PRAAx] q+succ p ≐ succ (p+q) by ipra_ring)
      · exact .eqRefl _) (by simpa using stage_shape A B q a b (succ p))
  simpa using out

theorem padded_row_entries (B B' q b i : PTm n) (he : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b) : Γ ⊢[PRAAx]
    embeddedEntries (paddedRow B q b i) (GaussianBivariatePolynomialProduct.paddedRow B' q b i) (succ b) := by
  refine .orE (lt_or_le i (succ q)) ?_ ?_
  · exact RationalPolynomialMonicCompanionGaussianEmbedding.embedded_congr
      (padded_row_inside _ _ _ _ Prf.hyp0).eqSymm (GaussianBivariatePolynomialProduct.padded_row_inside _ _ _ _ Prf.hyp0).eqSymm
      (row_embedded_at _ _ _ _ _ he.wk Prf.hyp0)
  · exact RationalPolynomialMonicCompanionGaussianEmbedding.embedded_congr
      (padded_row_outside _ _ _ _ Prf.hyp0).eqSymm (GaussianBivariatePolynomialProduct.padded_row_outside _ _ _ _ Prf.hyp0).eqSymm
      (RationalPolynomialBuffersGaussianEmbedding.zeros_embedded_entries _)

theorem contribution_entry_transport (A A' B B' P q a b k i s : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' P a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b)
    (hi : Γ ⊢[PRAAx] lt i P) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    embed (entry (contribution A B q a b k i) s) ≐ entry (GaussianBivariatePolynomialProduct.contribution A' B' q a b k i) s := by
  refine .orE (GaussianRationalMonicReconstruction.le_or_lt i k) ?_ ?_
  · exact (embed_congr (entry_congr (contribution_inside _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl _))).eqTrans
      ((RationalPolynomialMonicCompanionGaussianEmbedding.product_transport _ _ _ _ a b s
        (row_embedded_at _ _ _ _ _ hA.wk hi.wk) (padded_row_entries _ _ _ _ _ hB.wk) hs.wk).eqTrans
          (entry_congr (GaussianBivariatePolynomialProduct.contribution_inside _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl _)).eqSymm)
  · exact (embed_congr (entry_congr (contribution_outside _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl _))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ _ ((succ_monus_succ _ _).eqTrans hs.wk)).eqTrans
        (entry_congr (GaussianBivariatePolynomialProduct.contribution_outside _ _ _ _ _ _ _ Prf.hyp0) (.eqRefl _)).eqSymm)

def coefficientLaw (A A' B B' P q a b k s t : PTm n) : Fm PTm n := le t P ⟶
  embed (entry (rowSum A B q a b k t) s) ≐ entry (GaussianBivariatePolynomialProduct.rowSum A' B' q a b k t) s
@[simp] theorem subst_coefficientLaw {l : ℕ} (σ : Fin n → PTm l) (A A' B B' P q a b k s t : PTm n) :
    (coefficientLaw A A' B B' P q a b k s t).subst σ = coefficientLaw (Syn.subst σ A) (Syn.subst σ A') (Syn.subst σ B)
      (Syn.subst σ B') (Syn.subst σ P) (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ t) := by simp [coefficientLaw]

theorem coefficient_step (A A' B B' P q a b k s t : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' P a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b)
    (hs : Γ ⊢[PRAAx] le s (a+b)) (ht : Γ ⊢[PRAAx] lt t P)
    (ih : Γ ⊢[PRAAx] embed (entry (rowSum A B q a b k t) s) ≐ entry (GaussianBivariatePolynomialProduct.rowSum A' B' q a b k t) s) : Γ ⊢[PRAAx]
    embed (entry (rowSum A B q a b k (succ t)) s) ≐ entry (GaussianBivariatePolynomialProduct.rowSum A' B' q a b k (succ t)) s :=
  (embed_congr ((entry_congr (row_sum_succ _ _ _ _ _ _ _) (.eqRefl _)).eqTrans
    (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs)))).eqTrans
      ((RationalGaussianEmbedding.embed_add _ _).eqTrans
        ((GaussianRationalSyntheticDivision.qadd_congr ih (contribution_entry_transport _ _ _ _ _ _ _ _ _ _ _ hA hB ht hs)).eqTrans
          ((GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs)).eqSymm.eqTrans
            (entry_congr (GaussianBivariatePolynomialProduct.row_sum_succ _ _ _ _ _ _ _) (.eqRefl _)).eqSymm)))

theorem row_sum_transport (A A' B B' P q a b k s t : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' P a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b)
    (hs : Γ ⊢[PRAAx] le s (a+b)) (ht : Γ ⊢[PRAAx] le t P) : Γ ⊢[PRAAx]
    embed (entry (rowSum A B q a b k t) s) ≐ entry (GaussianBivariatePolynomialProduct.rowSum A' B' q a b k t) s := by
  have as : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift A) (Syn.shift A') (Syn.shift P) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift B) (Syn.shift B') (succ (Syn.shift q)) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ss : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift s) (Syn.shift a+Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (coefficientLaw (Syn.shift A) (Syn.shift A') (Syn.shift B) (Syn.shift B')
      (Syn.shift P) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (Syn.shift s) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_coefficientLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((embed_congr (entry_congr (row_sum_zero _ _ _ _ _ _) (.eqRefl _))).eqTrans
        ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ _ ((succ_monus_succ _ _).eqTrans hs)).eqTrans
          (entry_congr (GaussianBivariatePolynomialProduct.row_sum_zero _ _ _ _ _ _) (.eqRefl _)).eqSymm)).wk
    · simp only [subst_coefficientLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (coefficient_step _ _ _ _ _ _ _ _ _ _ _ as.wk.wk bs.wk.wk ss.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have actual : Γ ⊢[PRAAx] coefficientLaw A A' B B' P q a b k s t := by
    simpa only [subst_coefficientLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE actual ht

def coefficientData (A B q a b k s : PTm n) : PTm n := pairT (data A B q a b k) s
def coefficientBody : PTm 2 := entry (contribution (fields (fstT (var 1)) 0) (fields (fstT (var 1)) 1)
  (fields (fstT (var 1)) 2) (fields (fstT (var 1)) 3) (fields (fstT (var 1)) 4) (fields (fstT (var 1)) 5) (var 0)) (sndT (var 1))
def coefficient (A B q a b k s t : PTm n) : PTm n :=
  RationalFiniteSum.sum coefficientBody t (coefficientData A B q a b k s)
@[simp] theorem subst_coefficientData {l : ℕ} (σ : Fin n → PTm l) (A B q a b k s : PTm n) :
    Syn.subst σ (coefficientData A B q a b k s) = coefficientData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ s) := by simp [coefficientData]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (A B q a b k s t : PTm n) :
    Syn.subst σ (coefficient A B q a b k s t) = coefficient (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ q)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ t) := by simp [coefficient]
theorem pair_fields (p s : PTm n) (j : Fin 6) : Γ ⊢[PRAAx] fields (fstT (pairT p s)) j ≐ fields p j := by
  ipra_congr (fields (var 0) j : PTm 1) with [fst_pair _ _]
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
        ((RationalPolynomialBuffersGaussianEmbedding.zeros_lookup _ _ ((succ_monus_succ _ _).eqTrans hs)).eqTrans
          (RationalGaussianRealPart.rational_sum_zero coefficientBody (coefficientData A B q a b k s)).eqSymm)
    · simp only [Fm.subst_eq,Foundations.MasterCertificate.subst_entry,subst_rowSum,subst_coefficient,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := (entry (rowSum (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0))
        (Syn.shift s) ≐ coefficient (Syn.shift A) (Syn.shift B) (Syn.shift q) (Syn.shift a) (Syn.shift b) (Syn.shift k) (Syn.shift s) (var 0)) :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (Syn.shift s) (Syn.shift a+Syn.shift b) := hss.wk
      have step := (entry_congr (row_sum_succ (Γ := Δ) (Syn.shift A) (Syn.shift B) (Syn.shift q)
        (Syn.shift a) (Syn.shift b) (Syn.shift k) (var 0)) (.eqRefl (Syn.shift s))).eqTrans
        (RationalPolynomialBuffersGaussianEmbedding.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans bound))

      exact step.eqTrans ((RationalAlgebra.add_congr Prf.hyp0 (coefficient_body_at _ _ _ _ _ _ _ _).eqSymm).eqTrans
        (RationalFiniteSum.sum_succ _ _ _).eqSymm)
  simpa only [Fm.subst_eq,Foundations.MasterCertificate.subst_entry,subst_rowSum,subst_coefficient,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem product_coefficient (A B p q a b k s : PTm n) (hk : Γ ⊢[PRAAx] le k (p+q)) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    entry (entry (product A B p q a b) k) s ≐ coefficient A B q a b k s (succ p) :=
  (entry_congr (product_lookup _ _ _ _ _ _ _ hk) (.eqRefl _)).eqTrans (row_sum_coefficient _ _ _ _ _ _ _ _ hs)



theorem product_entry_transport (A A' B B' p q a b r s : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' (succ p) a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b)
    (hr : Γ ⊢[PRAAx] le r (p+q)) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    embed (entry (entry (product A B p q a b) r) s) ≐ entry (entry (GaussianBivariatePolynomialProduct.product A' B' p q a b) r) s :=
  (embed_congr (entry_congr (product_lookup _ _ _ _ _ _ _ hr) (.eqRefl _))).eqTrans
    ((row_sum_transport _ _ _ _ _ _ _ _ _ _ _ hA hB hs (le_refl _)).eqTrans
      (entry_congr (GaussianBivariatePolynomialProduct.product_lookup _ _ _ _ _ _ _ hr) (.eqRefl _)).eqSymm)

theorem product_row_entries (A A' B B' p q a b r : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' (succ p) a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b)
    (hr : Γ ⊢[PRAAx] le r (p+q)) : Γ ⊢[PRAAx]
    embeddedEntries (entry (product A B p q a b) r) (entry (GaussianBivariatePolynomialProduct.product A' B' p q a b) r) (succ (a+b)) := by
  have as : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift A) (Syn.shift A') (succ (Syn.shift p)) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift B) (Syn.shift B') (succ (Syn.shift q)) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift r) (Syn.shift p+Syn.shift q) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift a+Syn.shift b)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift a+Syn.shift b) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift a+Syn.shift b)))
  simpa only [Δ,Syn.shift,subst_product,GaussianBivariatePolynomialProduct.subst_product,subst_entry,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    product_entry_transport (Syn.shift A) (Syn.shift A') (Syn.shift B) (Syn.shift B') (Syn.shift p) (Syn.shift q)
      (Syn.shift a) (Syn.shift b) (Syn.shift r) (var 0) as.wk bs.wk rs.wk bound

theorem product_rows_embedded (A A' B B' p q a b : PTm n)
    (hA : Γ ⊢[PRAAx] rowsEmbedded A A' (succ p) a) (hB : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b) : Γ ⊢[PRAAx]
    rowsEmbedded (product A B p q a b) (GaussianBivariatePolynomialProduct.product A' B' p q a b) (succ (p+q)) (a+b) := by
  have as : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift A) (Syn.shift A') (succ (Syn.shift p)) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift B) (Syn.shift B') (succ (Syn.shift q)) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hB.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift p+Syn.shift q)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift p+Syn.shift q) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift p+Syn.shift q)))
  simpa only [Δ,Syn.shift,subst_product,GaussianBivariatePolynomialProduct.subst_product,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    product_row_entries (Syn.shift A) (Syn.shift A') (Syn.shift B) (Syn.shift B') (Syn.shift p) (Syn.shift q)
      (Syn.shift a) (Syn.shift b) (var 0) as.wk bs.wk bound

theorem product_evaluation (A B p q a b x y : PTm n) (hA : Γ ⊢[PRAAx] rowShape A (succ p) a)
    (hB : Γ ⊢[PRAAx] rowShape B (succ q) b) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (product A B p q a b) (succ (p+q)) x y ≐ RationalArithmetic.multiply
      (RationalBivariateGaussianEmbedding.bivariate A (succ p) x y) (RationalBivariateGaussianEmbedding.bivariate B (succ q) x y) := by
  let A' := RationalRowSpanGaussianEmbedding.matrix A (succ p) (succ a)
  let B' := RationalRowSpanGaussianEmbedding.matrix B (succ q) (succ b)
  have as : Γ ⊢[PRAAx] rowShape A' (succ p) a := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have bs : Γ ⊢[PRAAx] rowShape B' (succ q) b := RationalBivariateGaussianEmbedding.embedded_row_shape _ _ _
  have ae : Γ ⊢[PRAAx] rowsEmbedded A A' (succ p) a := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have be : Γ ⊢[PRAAx] rowsEmbedded B B' (succ q) b := RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _
  have e := (RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport
    (product A B p q a b) (GaussianBivariatePolynomialProduct.product A' B' p q a b) (succ (p+q)) (a+b) x y
    (product_shape _ _ _ _ _ _) (.andE₁ (.andE₂ (GaussianBivariatePolynomialProduct.product_stored _ _ _ _ _ _)))
    (product_rows_embedded _ _ _ _ _ _ _ _ ae be)).eqTrans
      ((GaussianBivariatePolynomialProduct.product_evaluation _ _ _ _ _ _ _ _ as bs).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr
          (RationalBivariateGaussianEmbedding.bivariate_conjugacy A (succ p) a x y hA).eqSymm
          (RationalBivariateGaussianEmbedding.bivariate_conjugacy B (succ q) b x y hB).eqSymm).eqTrans
            (RationalGaussianEmbedding.embed_multiply _ _).eqSymm))
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.multiply_guard _ _) e

theorem product_coefficient_well_formed (A B p q a b r s : PTm n)
    (hr : Γ ⊢[PRAAx] le r (p+q)) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (entry (product A B p q a b) r) s) :=
  RationalArithmetic.guard_congr (product_coefficient _ _ _ _ _ _ _ _ hr hs) (RationalFiniteSum.sum_well_formed _ _ _)


def input (A B p q a b : PTm n) : Fm PTm n := length A ≐ succ p ⋏
  (rowShape A (succ p) a ⋏ (length B ≐ succ q ⋏ rowShape B (succ q) b))
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (A B p q a b : PTm n) :
    (input A B p q a b).subst σ = input (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) := by simp [input]

theorem bivariate_congr {P P' R R' x x' y y' : PTm n} (hP : Γ ⊢[PRAAx] P ≐ P')
    (hR : Γ ⊢[PRAAx] R ≐ R') (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate P R x y ≐ RationalBivariateGaussianEmbedding.bivariate P' R' x' y' :=
  (RationalBivariateGaussianEmbedding.bivariate_at _ _ _ _).eqSymm.eqTrans
    ((congrApp RationalBivariateGaussianEmbedding.bivariateF (ts := ![P,R,x,y]) (us := ![P',R',x',y'])
      (fun i => by fin_cases i; exact hP; exact hR; exact hx; exact hy)).eqTrans
        (RationalBivariateGaussianEmbedding.bivariate_at _ _ _ _))

theorem original_product_evaluation (A B p q a b x y : PTm n) (h : Γ ⊢[PRAAx] input A B p q a b) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (product A B p q a b) (succ (p+q)) x y ≐ RationalArithmetic.multiply
      (RationalBivariateGaussianEmbedding.bivariate A (length A) x y) (RationalBivariateGaussianEmbedding.bivariate B (length B) x y) :=
  (product_evaluation _ _ _ _ _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ (.andE₂ h)))).eqTrans
    (RationalAlgebra.multiply_congr (bivariate_congr (.eqRefl _) (Prf.andE₁ h).eqSymm (.eqRefl _) (.eqRefl _))
      (bivariate_congr (.eqRefl _) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).eqSymm (.eqRefl _) (.eqRefl _)))

theorem original_coefficient_embedding (A B p q a b r s : PTm n)
    (hr : Γ ⊢[PRAAx] le r (p+q)) (hs : Γ ⊢[PRAAx] le s (a+b)) : Γ ⊢[PRAAx]
    embed (entry (entry (product A B p q a b) r) s) ≐
      entry (entry (GaussianBivariatePolynomialProduct.product
        (RationalRowSpanGaussianEmbedding.matrix A (succ p) (succ a))
        (RationalRowSpanGaussianEmbedding.matrix B (succ q) (succ b)) p q a b) r) s :=
  product_entry_transport _ _ _ _ _ _ _ _ _ _
    (RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _)
    (RationalPolynomialMonicCompanionGaussianEmbedding.original_rows_embedded _ _ _) hr hs

def productF : PR 6 := PTm.toPR (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (A B p q a b : PTm n) : PTm n := app productF ![A,B,p,q,a,b]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (A B p q a b : PTm n) :
    Syn.subst σ (run A B p q a b) = run (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (A B p q a b : PTm n) : Γ ⊢[PRAAx] run A B p q a b ≐ product A B p q a b := by
  simpa [run,productF] using toPR_eq (Γ := Γ) (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![A,B,p,q,a,b]
theorem returned_evaluation (A B p q a b x y : PTm n) (h : Γ ⊢[PRAAx] input A B p q a b) : Γ ⊢[PRAAx]
    RationalBivariateGaussianEmbedding.bivariate (run A B p q a b) (succ (p+q)) x y ≐ RationalArithmetic.multiply
      (RationalBivariateGaussianEmbedding.bivariate A (length A) x y) (RationalBivariateGaussianEmbedding.bivariate B (length B) x y) :=
  (bivariate_congr (program_at _ _ _ _ _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _)).eqTrans (original_product_evaluation _ _ _ _ _ _ _ _ h)

theorem actual_rational_bivariate_product_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ succ (var 2+var 3) ⋏
      rowShape (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 4+var 5)) :=
  closeUniv 6 (.andI (product_length _ _ _ _ _ _) (product_shape _ _ _ _ _ _))
theorem actual_rational_bivariate_product_convolution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 6) (var 2+var 3) ⟶ le (var 7) (var 4+var 5) ⟶
      entry (entry (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7) ≐
        coefficient (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (succ (var 2))) :=
  closeUniv 8 (.impI (.impI (product_coefficient _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_bivariate_product_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 6) (var 2+var 3) ⟶ le (var 7) (var 4+var 5) ⟶
      embed (entry (entry (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7)) ≐
        entry (entry (GaussianBivariatePolynomialProduct.product
          (RationalRowSpanGaussianEmbedding.matrix (var 0) (succ (var 2)) (succ (var 4)))
          (RationalRowSpanGaussianEmbedding.matrix (var 1) (succ (var 3)) (succ (var 5))) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7)) :=
  closeUniv 8 (.impI (.impI (original_coefficient_embedding _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_bivariate_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalBivariateGaussianEmbedding.bivariate (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 6) (var 7) ≐ RationalArithmetic.multiply
        (RationalBivariateGaussianEmbedding.bivariate (var 0) (length (var 0)) (var 6) (var 7))
        (RationalBivariateGaussianEmbedding.bivariate (var 1) (length (var 1)) (var 6) (var 7))) :=
  closeUniv 8 (.impI (original_product_evaluation _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_bivariate_product_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 6) (var 2+var 3) ⟶ le (var 7) (var 4+var 5) ⟶
      RationalNormalForm.wellFormed (entry (entry (product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) (var 7))) :=
  closeUniv 8 (.impI (.impI (product_coefficient_well_formed _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_bivariate_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ product (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_rational_returned_bivariate_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      RationalBivariateGaussianEmbedding.bivariate (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (succ (var 2+var 3)) (var 6) (var 7) ≐ RationalArithmetic.multiply
        (RationalBivariateGaussianEmbedding.bivariate (var 0) (length (var 0)) (var 6) (var 7))
        (RationalBivariateGaussianEmbedding.bivariate (var 1) (length (var 1)) (var 6) (var 7))) :=
  closeUniv 8 (.impI (returned_evaluation _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalBivariatePolynomialProductGaussianEmbedding
