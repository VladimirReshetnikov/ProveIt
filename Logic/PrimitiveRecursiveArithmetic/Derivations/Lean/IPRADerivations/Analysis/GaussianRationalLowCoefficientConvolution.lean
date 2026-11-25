import IPRADerivations.Analysis.GaussianRationalPolynomialProduct
import IPRADerivations.Analysis.GaussianRationalMatrixFiniteSums
import IPRADerivations.Core.LinearCombination

/-!
# Low-exponent coefficients of the actual polynomial product

The original product stores descending coefficients. A bounded numerical
reflection of its SAME actual convolution gives the low-exponent Cauchy
sum. The reflected tail vanishes by the original entry-or-zero guard.
All degrees, coefficient indices and raw buffers are numerical; no
convolution, representation, evaluation or output law is an input.
This supplies the actual coefficient algebra needed by the literal finite
logarithmic exponential, without identifying its Bell coefficients yet.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalLowCoefficientConvolution

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right)
open GaussianRationalPolynomialProduct (product coefficient contribution contribution_inside contribution_body_at)
open GaussianRationalLinearProduct (padded_inside padded_outside)
open GaussianRationalMonicReconstruction (monus_le_left complement)
open GaussianRationalFiniteSum (sum)
open GaussianRationalPermutationSum (mappedBody inst2_mappedBody)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def exponentCoefficient (C N e : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus (succ N) e)) qzero (entry C (monus N e))
def term (P Q N M e i : PTm n) : PTm n :=
  qmul (entry P (monus N i)) (entry Q (monus M (monus e i)))
def data (P Q N M e : PTm n) : PTm n := pairT P (pairT Q (pairT N (pairT M e)))
def getP (x : PTm n) : PTm n := fstT x
def getQ (x : PTm n) : PTm n := fstT (sndT x)
def getN (x : PTm n) : PTm n := fstT (sndT (sndT x))
def getM (x : PTm n) : PTm n := fstT (sndT (sndT (sndT x)))
def getE (x : PTm n) : PTm n := sndT (sndT (sndT (sndT x)))
def sourceBody : PTm 2 := contribution (getP (var 1)) (getQ (var 1)) (getM (var 1))
  (monus (getN (var 1)+getM (var 1)) (getE (var 1))) (var 0)
def reverseBody : PTm 2 := monus (getN (var 1)) (var 0)
def termBody : PTm 2 := term (getP (var 1)) (getQ (var 1)) (getN (var 1)) (getM (var 1)) (getE (var 1)) (var 0)
def cauchySum (P Q N M e : PTm n) : PTm n := sum termBody (succ e) (data P Q N M e)

@[simp] theorem subst_exponentCoefficient {l : ℕ} (σ : Fin n → PTm l) (C N e : PTm n) :
    Syn.subst σ (exponentCoefficient C N e) = exponentCoefficient (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) := by
  simp [exponentCoefficient,Signum.sg]
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (P Q N M e i : PTm n) :
    Syn.subst σ (term P Q N M e i) = term (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N)
      (Syn.subst σ M) (Syn.subst σ e) (Syn.subst σ i) := by simp [term]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (P Q N M e : PTm n) :
    Syn.subst σ (data P Q N M e) = data (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [data]
@[simp] theorem subst_cauchySum {l : ℕ} (σ : Fin n → PTm l) (P Q N M e : PTm n) :
    Syn.subst σ (cauchySum P Q N M e) = cauchySum (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [cauchySum]

theorem exponent_inside (C N e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient C N e ≐ entry C (monus N e) :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans he))
theorem exponent_outside (C N e : PTm n) (he : Γ ⊢[PRAAx] lt N e) : Γ ⊢[PRAAx]
    exponentCoefficient C N e ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le he)

theorem get_p (P Q N M e : PTm n) : Γ ⊢[PRAAx] getP (data P Q N M e) ≐ P := fst_pair _ _
theorem get_q (P Q N M e : PTm n) : Γ ⊢[PRAAx] getQ (data P Q N M e) ≐ Q :=
  (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
theorem get_n (P Q N M e : PTm n) : Γ ⊢[PRAAx] getN (data P Q N M e) ≐ N :=
  (congrFst ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem get_m (P Q N M e : PTm n) : Γ ⊢[PRAAx] getM (data P Q N M e) ≐ M :=
  (congrFst ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem get_e (P Q N M e : PTm n) : Γ ⊢[PRAAx] getE (data P Q N M e) ≐ e :=
  (congrSnd ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem source_at (P Q N M e i : PTm n) : Γ ⊢[PRAAx]
    inst2 sourceBody i (data P Q N M e) ≐ contribution P Q M (monus (N+M) e) i := by
  simp only [sourceBody,inst2,GaussianRationalPolynomialProduct.subst_contribution,
    getP,getQ,getN,getM,getE,subst_fstT,subst_sndT,PTm.subst_monus,PTm.subst_add,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalPolynomialProduct.contribution_congr (get_p _ _ _ _ _) (get_q _ _ _ _ _)
    (get_m _ _ _ _ _) (congrMonus (congrAdd (get_n _ _ _ _ _) (get_m _ _ _ _ _)) (get_e _ _ _ _ _)) (.eqRefl _)
theorem reverse_at (P Q N M e i : PTm n) : Γ ⊢[PRAAx]
    inst2 reverseBody i (data P Q N M e) ≐ monus N i := by
  simp only [reverseBody,inst2,getN,PTm.subst_monus,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrMonus (get_n _ _ _ _ _) (.eqRefl _)
theorem term_at (P Q N M e i : PTm n) : Γ ⊢[PRAAx]
    inst2 termBody i (data P Q N M e) ≐ term P Q N M e i := by
  simp only [termBody,inst2,subst_term,getP,getQ,getN,getM,getE,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (entry_congr (get_p _ _ _ _ _) (congrMonus (get_n _ _ _ _ _) (.eqRefl _)))
    (entry_congr (get_q _ _ _ _ _) (congrMonus (get_m _ _ _ _ _) (congrMonus (get_e _ _ _ _ _) (.eqRefl _))))
theorem reflected_at (P Q N M e i : PTm n) : Γ ⊢[PRAAx]
    inst2 (mappedBody sourceBody reverseBody) i (data P Q N M e) ≐
      contribution P Q M (monus (N+M) e) (monus N i) := by
  rw [inst2_mappedBody]
  exact (source_at P Q N M e _).eqTrans
    (GaussianRationalPolynomialProduct.contribution_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (reverse_at P Q N M e i))

theorem index_decompose (N M e : PTm n) (he : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    monus (N+M) e ≐ N+monus M e := by
  have he' : Γ ⊢[PRAAx] le e (N+M) := le_trans he (le_congr (.eqRefl _) (add_comm _ _) (le_add_right M N))
  ipra_lc natEq (eq_add_of_le he)-natEq (eq_add_of_le he')

theorem reversed_inside (N M e i : PTm n) (he : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    le (monus N i) (monus (N+M) e) :=
  le_trans (monus_le_left N i) (le_congr (.eqRefl _) (index_decompose N M e he).eqSymm (le_add_right N _))

theorem difference_low (N M e i : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    monus (monus (N+M) e) (monus N i) ≐ monus M (monus e i) := by
  have e' : Γ ⊢[PRAAx] le e (N+M) := le_trans hM (le_congr (.eqRefl _) (add_comm _ _) (le_add_right M N))
  ipra_lc natEq (eq_add_of_le (le_trans hi hN))+natEq (eq_add_of_le (le_trans (monus_le_left e i) hM))-
    natEq (eq_add_of_le hi)-natEq (eq_add_of_le e')-natEq (eq_add_of_le (reversed_inside N M e i hM))

theorem difference_high (N M e i : PTm n) (hM : Γ ⊢[PRAAx] le e M)
    (hi : Γ ⊢[PRAAx] le i N) (hei : Γ ⊢[PRAAx] lt e i) : Γ ⊢[PRAAx]
    lt M (monus (monus (N+M) e) (monus N i)) := by
  have e' : Γ ⊢[PRAAx] le e (N+M) := le_trans hM (le_congr (.eqRefl _) (add_comm _ _) (le_add_right M N))
  have d := natEq (eq_add_of_le (reversed_inside N M e i hM))
  apply le_of_eq_add (d := monus i (succ e))
  ipra_lc natEq (eq_add_of_le hi)+natEq (eq_add_of_le hei)-natEq (eq_add_of_le e')-d

theorem contribution_low (P Q N M e i : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) (hi : Γ ⊢[PRAAx] le i e) : Γ ⊢[PRAAx]
    contribution P Q M (monus (N+M) e) (monus N i) ≐ term P Q N M e i := by
  have hd := difference_low N M e i hN hM hi
  have hr : Γ ⊢[PRAAx] lt (monus (monus (N+M) e) (monus N i)) (succ M) :=
    (succ_monus_succ _ _).eqTrans (le_congr hd.eqSymm (.eqRefl _) (monus_le_left M _))
  exact (contribution_inside _ _ _ _ _ (reversed_inside N M e i hM)).eqTrans
    (qmul_congr (.eqRefl _) ((padded_inside _ _ _ hr).eqTrans (entry_congr (.eqRefl _) hd)))
theorem contribution_high (P Q N M e i : PTm n) (hM : Γ ⊢[PRAAx] le e M)
    (hi : Γ ⊢[PRAAx] le i N) (hei : Γ ⊢[PRAAx] lt e i) : Γ ⊢[PRAAx]
    contribution P Q M (monus (N+M) e) (monus N i) ≐ qzero :=
  (contribution_inside _ _ _ _ _ (reversed_inside N M e i hM)).eqTrans
    ((qmul_congr (.eqRefl _) (padded_outside _ _ _ (difference_high N M e i hM hi hei))).eqTrans
      (qmul_zero_right _))

theorem reverse_range (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalPermutationSum.boundedRange reverseBody (succ N) (data P Q N M e) := by
  refine .allI (.impI ?_)
  have hr : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (monus (Syn.shift N) (var 0)) (succ (Syn.shift N)) :=
    (succ_monus_succ _ _).eqTrans (monus_le_left _ _)
  simpa only [Syn.shift,subst_data,ConciseIPRA.PTm.subst_succ] using
    lt_congr (reverse_at (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqSymm (.eqRefl _) hr

theorem reverse_inverse (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalPermutationSum.inverseLaw reverseBody reverseBody (succ N) (data P Q N M e) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have h := (reverse_at (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e)
      (inst2 reverseBody (var 0) (data (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e)))).eqTrans
    ((congrMonus (.eqRefl _) (reverse_at (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0))).eqTrans
      (complement (Syn.shift N) (var 0) hi))
  simpa only [Δ,Syn.shift,subst_data,ConciseIPRA.PTm.subst_succ] using h

theorem original_sum (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    sum sourceBody (succ N) (data P Q N M e) ≐ coefficient P Q M (succ N) (monus (N+M) e) := by
  refine GaussianRationalFiniteSum.sum_congr_bounded sourceBody GaussianRationalPolynomialProduct.contributionBody (succ N)
    (data P Q N M e) (GaussianRationalPolynomialProduct.data P Q M (monus (N+M) e)) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_data,GaussianRationalPolynomialProduct.subst_data,PTm.subst_monus,PTm.subst_add,ConciseIPRA.PTm.subst_succ] using
    (source_at (Γ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift)
      (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqTrans
      (contribution_body_at (Syn.shift P) (Syn.shift Q) (Syn.shift M) (monus (Syn.shift N+Syn.shift M) (Syn.shift e)) (var 0)).eqSymm

theorem reflected_sum (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    sum (mappedBody sourceBody reverseBody) (succ N) (data P Q N M e) ≐
      coefficient P Q M (succ N) (monus (N+M) e) :=
  (GaussianRationalPermutationSum.involution_sum sourceBody reverseBody (succ N) (data P Q N M e)
    (reverse_range P Q N M e) (reverse_inverse P Q N M e)).eqTrans (original_sum P Q N M e)

theorem prefix_cauchy (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    sum (mappedBody sourceBody reverseBody) (succ e) (data P Q N M e) ≐ cauchySum P Q N M e := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,Syn.shift,subst_le] using hN.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift M) := by
    simpa only [Fm.shift,Syn.shift,subst_le] using hM.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded (mappedBody sourceBody reverseBody) termBody (succ e) (data P Q N M e) (data P Q N M e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,subst_data,ConciseIPRA.PTm.subst_succ] using
    (reflected_at (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqTrans
      ((contribution_low _ _ _ _ _ _ hn.wk hm.wk hi).eqTrans
        (term_at (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqSymm)

theorem cutoff_sum (N e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    succ e+monus N e ≐ succ N := by
  ipra_lc -natEq (eq_add_of_le he)

theorem reflected_tail_zero (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    sum (LeanProofs.IPRA.offB (mappedBody sourceBody reverseBody)) (monus N e) (pairT (succ e) (data P Q N M e)) ≐ qzero := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,Syn.shift,subst_le] using hN.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift M) := by
    simpa only [Fm.shift,Syn.shift,subst_le] using hM.shift
  refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms _ _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (monus (Syn.shift N) (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (monus (Syn.shift N) (Syn.shift e)) := Prf.hyp0
  have hcut := cutoff_sum (Γ := Δ) (Syn.shift N) (Syn.shift e) hn.wk
  have hpos : Δ ⊢[PRAAx] lt (succ (Syn.shift e)+var 0) (succ (Syn.shift N)) :=
    lt_congr (.eqRefl _) hcut (Foundations.SequenceComposition.add_lt_left _ hi)
  have hle : Δ ⊢[PRAAx] le (succ (Syn.shift e)+var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans hpos
  have hgt : Δ ⊢[PRAAx] lt (Syn.shift e) (succ (Syn.shift e)+var 0) := le_add_right _ _
  have h := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) (mappedBody sourceBody reverseBody)
      (succ (Syn.shift e)) (var 0) (data (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e))).eqTrans
    ((reflected_at _ _ _ _ _ _).eqTrans (contribution_high _ _ _ _ _ _ hm.wk hle hgt))
  simpa only [Δ,Syn.shift,PTm.subst_monus,subst_pairT,ConciseIPRA.PTm.subst_succ,subst_data] using h

theorem coefficient_cauchy (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    entry (product P Q N M) (monus (N+M) e) ≐ cauchySum P Q N M e := by
  have hsplit := GaussianRationalMatrixFiniteSums.sum_split (Γ := Γ) (mappedBody sourceBody reverseBody)
    (succ e) (monus N e) (data P Q N M e)
  have hcut : Γ ⊢[PRAAx] sum (mappedBody sourceBody reverseBody) (succ N) (data P Q N M e) ≐
      sum (mappedBody sourceBody reverseBody) (succ e) (data P Q N M e) :=
    (GaussianRationalFiniteSum.sum_index_congr (mappedBody sourceBody reverseBody) (cutoff_sum N e hN).eqSymm (.eqRefl _)).eqTrans
      (hsplit.eqTrans ((qadd_congr (.eqRefl _) (reflected_tail_zero P Q N M e hN hM)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _))))
  exact (GaussianRationalPolynomialProduct.product_lookup P Q N M (monus (N+M) e) (monus_le_left _ _)).eqTrans
    ((reflected_sum P Q N M e).eqSymm.eqTrans (hcut.eqTrans (prefix_cauchy P Q N M e hN hM)))

theorem product_exponent (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    exponentCoefficient (product P Q N M) (N+M) e ≐ cauchySum P Q N M e :=
  (exponent_inside _ _ _ (le_trans hN (le_add_right N M))).eqTrans (coefficient_cauchy P Q N M e hN hM)

def output (P Q N M e : PTm n) : PTm n :=
  pairT (entry (product P Q N M) (monus (N+M) e)) (cauchySum P Q N M e)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (P Q N M e : PTm n) : PTm n := PTm.app outputF ![P,Q,N,M,e]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (P Q N M e : PTm n) :
    Syn.subst σ (output P Q N M e) = output (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ e) := by
  simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (P Q N M e : PTm n) :
    Syn.subst σ (run P Q N M e) = run (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ e) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (P Q N M e : PTm n) : Γ ⊢[PRAAx] run P Q N M e ≐ output P Q N M e := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,Q,N,M,e]
theorem returned_coefficient (P Q N M e : PTm n) : Γ ⊢[PRAAx]
    fstT (run P Q N M e) ≐ entry (product P Q N M) (monus (N+M) e) :=
  (congrFst (program_at P Q N M e)).eqTrans (fst_pair _ _)
theorem returned_sum (P Q N M e : PTm n) : Γ ⊢[PRAAx] sndT (run P Q N M e) ≐ cauchySum P Q N M e :=
  (congrSnd (program_at P Q N M e)).eqTrans (snd_pair _ _)
theorem returned_agreement (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx] fstT (run P Q N M e) ≐ sndT (run P Q N M e) :=
  (returned_coefficient P Q N M e).eqTrans ((coefficient_cauchy P Q N M e hN hM).eqTrans (returned_sum P Q N M e).eqSymm)

theorem actual_exponent_reader_inside_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ exponentCoefficient (var 0) (var 1) (var 2) ≐ entry (var 0) (monus (var 1) (var 2))) :=
  closeUniv 3 (.impI (exponent_inside _ _ _ Prf.hyp0))
theorem actual_exponent_reader_outside_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 2) ⟶ exponentCoefficient (var 0) (var 1) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (exponent_outside _ _ _ Prf.hyp0))
theorem actual_low_coefficient_cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      entry (product (var 0) (var 1) (var 2) (var 3)) (monus (var 2+var 3) (var 4)) ≐
        cauchySum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (coefficient_cauchy _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_product_exponent_cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      exponentCoefficient (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) (var 4) ≐
        cauchySum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (product_exponent _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cauchy_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_cauchy_agreement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_agreement _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalLowCoefficientConvolution
