import IPRADerivations.Analysis.GaussianReconstructionRoots
import IPRADerivations.Analysis.GaussianBivariatePowerExpansion
import IPRADerivations.Analysis.GaussianRationalMatrixFiniteSums

/-!
# Actual Newton coefficient lists and forward products

The j-th Newton polynomial is the SAME existing reconstruction of the
first j numerical roots. Its coefficient at X^k is read from the real
descending slot j-k, with a genuine zero guard above degree j. The real
reverse reconstruction fold is connected to the existing forward product
by a guarded prefix-times-tail induction, rather than a product-order
assumption. Original raw root codes and j=0 are included.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianVandermondeNewtonPolynomials

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul canonical canonical_congr evaluate)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qmul_congr canonicalCoefficients)
open GaussianRationalReconstruction (reconstruct factors factorsF factorData)
open GaussianRationalFiniteProduct (qprod product_zero product_succ product_canonical)
open GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (R j : PTm n) : PTm n := reconstruct R j j
def coefficient (R j k : PTm n) : PTm n := sel (eqb (monus k j) zero)
  (entry (polynomial R j) (monus j k)) qzero
def differenceData (R z : PTm n) : PTm n := pairT R z
def differenceBody : PTm 2 := qsub (sndT (var 1)) (entry (fstT (var 1)) (var 0))
def differenceProduct (R z k : PTm n) : PTm n := qprod differenceBody k (differenceData R z)

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (R j : PTm n) :
    Syn.subst σ (polynomial R j) = polynomial (Syn.subst σ R) (Syn.subst σ j) := by simp [polynomial]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (R j k : PTm n) :
    Syn.subst σ (coefficient R j k) = coefficient (Syn.subst σ R) (Syn.subst σ j) (Syn.subst σ k) := by simp [coefficient,sel]
@[simp] theorem subst_differenceData {l : ℕ} (σ : Fin n → PTm l) (R z : PTm n) :
    Syn.subst σ (differenceData R z) = differenceData (Syn.subst σ R) (Syn.subst σ z) := by simp [differenceData]
@[simp] theorem subst_differenceProduct {l : ℕ} (σ : Fin n → PTm l) (R z k : PTm n) :
    Syn.subst σ (differenceProduct R z k) = differenceProduct (Syn.subst σ R) (Syn.subst σ z) (Syn.subst σ k) := by simp [differenceProduct]

theorem polynomial_length (R j : PTm n) : Γ ⊢[PRAAx] length (polynomial R j) ≐ succ j := GaussianRationalReconstruction.reconstruct_length _ _ _
theorem polynomial_monic (R j : PTm n) : Γ ⊢[PRAAx] entry (polynomial R j) zero ≐ qone := GaussianRationalReconstruction.reconstruct_monic _ _ _
theorem polynomial_canonical (R j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial R j) := GaussianRationalReconstruction.reconstruct_canonical _ _ _
theorem polynomial_entry_canonical (R j i : PTm n) (hi : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] canonical (entry (polynomial R j) i) := by
  have bound := lt_congr (.eqRefl i) (polynomial_length R j).eqSymm ((succ_monus_succ i j).eqTrans hi)
  have rule : Γ ⊢[PRAAx] lt i (length (polynomial R j)) ⟶ canonical (entry (polynomial R j) i) := by
    simpa [canonicalCoefficients] using (polynomial_canonical (Γ := Γ) R j).allE i
  exact .impE rule bound
theorem coefficient_inside (R j k : PTm n) (hk : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    coefficient R j k ≐ entry (polynomial R j) (monus j k) := sel_one (eqb_of_eq hk)
theorem coefficient_above (R j k : PTm n) (hk : Γ ⊢[PRAAx] lt j k) : Γ ⊢[PRAAx] coefficient R j k ≐ qzero := by
  have notLe : Γ ⊢[PRAAx] neg (monus k j ≐ zero) := .impI (le_lt_absurd _ Prf.hyp0 hk.wk)
  exact sel_zero (eqb_of_ne notLe)
theorem coefficient_diagonal (R j : PTm n) : Γ ⊢[PRAAx] coefficient R j j ≐ qone :=
  (coefficient_inside R j j (le_refl j)).eqTrans
    ((entry_congr (.eqRefl _) (monus_self j)).eqTrans (polynomial_monic R j))
theorem coefficient_canonical (R j k : PTm n) : Γ ⊢[PRAAx] canonical (coefficient R j k) := by
  refine .orE (GaussianRationalMonicReconstruction.le_or_lt k j) ?_ ?_
  · exact canonical_congr (coefficient_inside _ _ _ Prf.hyp0)
      (polynomial_entry_canonical _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _))
  · exact canonical_congr (coefficient_above _ _ _ Prf.hyp0) qzero_canonical

theorem difference_body_at (R z k : PTm n) : Γ ⊢[PRAAx]
    inst2 differenceBody k (differenceData R z) ≐ qsub z (entry R k) := by
  simp only [differenceBody,inst2,GaussianRationalMetric.subst_qsub,Foundations.MasterCertificate.subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalSyntheticDivision.qsub_congr (snd_pair _ _) (entry_congr (fst_pair _ _) (.eqRefl _))
theorem difference_zero (R z : PTm n) : Γ ⊢[PRAAx] differenceProduct R z zero ≐ qone := product_zero _ _
theorem difference_succ (R z k : PTm n) : Γ ⊢[PRAAx]
    differenceProduct R z (succ k) ≐ qmul (differenceProduct R z k) (qsub z (entry R k)) :=
  (product_succ _ _ _).eqTrans (qmul_congr (.eqRefl _) (difference_body_at _ _ _))
theorem factors_canonical (R N z k : PTm n) : Γ ⊢[PRAAx] canonical (factors R N z k) :=
  canonical_congr (GaussianRationalReconstruction.reconstruction_evaluation R N z k).eqSymm
    (GaussianRationalHorner.horner_canonical _ _ _)

def prefixLaw (R N z i : PTm n) : Fm PTm n := le i N ⟶
  qmul (differenceProduct R z i) (factors R N z (monus N i)) ≐ factors R N z N
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (R N z i : PTm n) :
    (prefixLaw R N z i).subst σ = prefixLaw (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ i) := by simp [prefixLaw]

theorem prefix_step (R N z i : PTm n) (hOld : Γ ⊢[PRAAx] prefixLaw R N z i) :
    Γ ⊢[PRAAx] prefixLaw R N z (succ i) := by
  refine .impI ?_
  have tail : le (succ i) N :: Γ ⊢[PRAAx] factors R N z (monus N i) ≐
      qmul (qsub z (entry R i)) (factors R N z (monus N (succ i))) := by
    simpa only [GaussianRationalDeflation.remaining] using
      GaussianRationalReconstruction.factors_suffix_step (Γ := le (succ i) N :: Γ) R N z i Prf.hyp0
  exact (qmul_congr (difference_succ _ _ _) (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      ((qmul_congr (.eqRefl _) tail.eqSymm).eqTrans (.impE hOld.wk (le_trans (le_succ_self i) Prf.hyp0))))

theorem factors_forward_product (R N z : PTm n) : Γ ⊢[PRAAx] factors R N z N ≐ differenceProduct R z N := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift R) (Syn.shift N) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((qmul_congr (difference_zero R z) (congrAp2 factorsF (monus_zero N) (.eqRefl (factorData R N z)))).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          (GaussianReciprocalHorner.qmul_one_right _ (factors_canonical _ _ _ _))))
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_step _ _ _ _ Prf.hyp0
  have queried : Γ ⊢[PRAAx] prefixLaw R N z N := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  have final := Prf.impE queried (le_refl N)
  have tail : Γ ⊢[PRAAx] factors R N z (monus N N) ≐ qone :=
    (congrAp2 factorsF (monus_self N) (.eqRefl (factorData R N z))).eqTrans
    (GaussianRationalReconstruction.factors_zero R N z)
  exact final.eqSymm.eqTrans ((qmul_congr (.eqRefl _) tail).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (product_canonical _ _ _)))

theorem evaluation_product (R j z : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial R j) z ≐ differenceProduct R z j :=
  (GaussianRationalReconstruction.reconstruction_evaluation R j z j).eqTrans (factors_forward_product R j z)
theorem prior_root_zero (R j r : PTm n) (hr : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx]
    evaluate (polynomial R j) (entry R r) ≐ qzero := GaussianReconstructionRoots.listed_root_zero R j r hr
theorem diagonal_evaluation (R j : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial R j) (entry R j) ≐ differenceProduct R (entry R j) j := evaluation_product _ _ _

/-- This factor order is exactly the scalar matrix-product row order. -/
def term (R j z k : PTm n) : PTm n := qmul (power z k) (coefficient R j k)
def powerData (R j z : PTm n) : PTm n := pairT R (pairT j z)
def powerBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def powerSum (R j z K : PTm n) : PTm n := GaussianRationalFiniteSum.sum powerBody K (powerData R j z)
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (R j z k : PTm n) :
    Syn.subst σ (term R j z k) = term (Syn.subst σ R) (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ k) := by simp [term]
@[simp] theorem subst_powerData {l : ℕ} (σ : Fin n → PTm l) (R j z : PTm n) :
    Syn.subst σ (powerData R j z) = powerData (Syn.subst σ R) (Syn.subst σ j) (Syn.subst σ z) := by simp [powerData]
@[simp] theorem subst_powerSum {l : ℕ} (σ : Fin n → PTm l) (R j z K : PTm n) :
    Syn.subst σ (powerSum R j z K) = powerSum (Syn.subst σ R) (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ K) := by simp [powerSum]
theorem term_congr {R S j d z y k i : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S) (hj : Γ ⊢[PRAAx] j ≐ d)
    (hz : Γ ⊢[PRAAx] z ≐ y) (hk : Γ ⊢[PRAAx] k ≐ i) : Γ ⊢[PRAAx] term R j z k ≐ term S d y i := by
  simpa only [subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ)
      (term (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![R,j,z,k]) (σ' := ![S,d,y,i])
      (fun a => by fin_cases a; exact hR; exact hj; exact hz; exact hk)
theorem power_body_at (R j z k : PTm n) : Γ ⊢[PRAAx] inst2 powerBody k (powerData R j z) ≐ term R j z k := by
  simp only [powerBody,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact term_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem power_term_inside (R j z k : PTm n) (hk : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    inst2 GaussianRationalPowerExpansion.termBody k (GaussianRationalPowerExpansion.data (polynomial R j) j z) ≐ term R j z k :=
  (GaussianRationalPowerExpansion.term_body_at _ _ _ _).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (qmul_congr (.eqRefl _) (coefficient_inside R j k hk).eqSymm))

theorem evaluation_power_sum (R j z : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial R j) z ≐ powerSum R j z (succ j) := by
  refine (GaussianBivariatePowerExpansion.evaluate_power_sum (polynomial R j) j z (polynomial_length R j)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalPowerExpansion.termBody powerBody (succ j)
      (GaussianRationalPowerExpansion.data (polynomial R j) j z) (powerData R j z) (.allI (.impI ?_)))
  let Δ := lt (var 0) (succ (Syn.shift j)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift j) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,subst_polynomial,subst_powerData,GaussianRationalPowerExpansion.subst_data,
    ConciseIPRA.PTm.subst_succ] using
    (power_term_inside (Syn.shift R) (Syn.shift j) (Syn.shift z) (var 0) bound).eqTrans
      (power_body_at (Syn.shift R) (Syn.shift j) (Syn.shift z) (var 0)).eqSymm

theorem power_term_above (R j z k : PTm n) (hk : Γ ⊢[PRAAx] lt j k) : Γ ⊢[PRAAx]
    inst2 powerBody k (powerData R j z) ≐ qzero :=
  (power_body_at R j z k).eqTrans ((qmul_congr (.eqRefl _) (coefficient_above R j k hk)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem power_sum_evaluation (R j z K : PTm n) (hK : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx]
    powerSum R j z K ≐ evaluate (polynomial R j) z := by
  have tail : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum (offB powerBody) (monus K (succ j))
      (pairT (succ j) (powerData R j z)) ≐ qzero := by
    refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms (offB powerBody) (monus K (succ j))
      (pairT (succ j) (powerData R j z)) (.allI (.impI ?_))
    let Δ := lt (var 0) (Syn.shift (monus K (succ j))) :: Γ.map Fm.shift
    have actual := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) powerBody (succ (Syn.shift j)) (var 0)
      (powerData (Syn.shift R) (Syn.shift j) (Syn.shift z))).eqTrans
      (power_term_above _ _ _ _ (le_add_right (succ (Syn.shift j)) (var 0)))
    simpa only [Δ,Syn.shift,subst_pairT,subst_powerData,ConciseIPRA.PTm.subst_succ,GaussianRationalHorner.subst_qzero] using actual
  have split := (GaussianRationalFiniteSum.sum_index_congr powerBody (eq_add_of_le hK) (.eqRefl (powerData R j z))).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_split powerBody (succ j) (monus K (succ j)) (powerData R j z)).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) tail).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _))))
  exact split.eqTrans (evaluation_power_sum R j z).eqSymm

/-- A literal nested forward product over all pairs i<j<t. -/
def pairBody : PTm 2 := differenceProduct (var 1) (entry (var 1) (var 0)) (var 0)
def pairProduct (R t : PTm n) : PTm n := qprod pairBody t R
@[simp] theorem subst_pairProduct {l : ℕ} (σ : Fin n → PTm l) (R t : PTm n) :
    Syn.subst σ (pairProduct R t) = pairProduct (Syn.subst σ R) (Syn.subst σ t) := by simp [pairProduct]
@[simp] theorem pair_body_at (R j : PTm n) : inst2 pairBody j R = differenceProduct R (entry R j) j := by simp [pairBody,inst2]
theorem pair_zero (R : PTm n) : Γ ⊢[PRAAx] pairProduct R zero ≐ qone := product_zero _ _
theorem pair_succ (R t : PTm n) : Γ ⊢[PRAAx]
    pairProduct R (succ t) ≐ qmul (pairProduct R t) (differenceProduct R (entry R t) t) := by
  simpa only [pairProduct,pair_body_at] using product_succ (Γ := Γ) pairBody t R
theorem pair_canonical (R t : PTm n) : Γ ⊢[PRAAx] canonical (pairProduct R t) := product_canonical _ _ _

def polynomialF : PR 2 := PTm.toPR (polynomial (var 0) (var 1))
def output (R j z : PTm n) : PTm n := pairT (polynomial R j)
  (pairT (evaluate (polynomial R j) z) (pairT (differenceProduct R z j) (pairProduct R j)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (R j z : PTm n) : PTm n := app outputF ![R,j,z]
def fields (p : PTm n) : Fin 4 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (R j z : PTm n) :
    Syn.subst σ (output R j z) = output (Syn.subst σ R) (Syn.subst σ j) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (R j z : PTm n) :
    Syn.subst σ (run R j z) = run (Syn.subst σ R) (Syn.subst σ j) (Syn.subst σ z) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem polynomial_program_at (R j : PTm n) : Γ ⊢[PRAAx] app polynomialF ![R,j] ≐ polynomial R j := by
  simpa [polynomialF] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) : PTm 2) ![R,j]
theorem program_at (R j z : PTm n) : Γ ⊢[PRAAx] run R j z ≐ output R j z := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![R,j,z]
theorem returned_fields (R j z : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    fields (run R j z) i ≐ ![polynomial R j,evaluate (polynomial R j) z,differenceProduct R z j,pairProduct R j] i := by
  have e0 := program_at (Γ := Γ) R j z
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem returned_evaluation (R j z : PTm n) : Γ ⊢[PRAAx] fields (run R j z) 1 ≐ fields (run R j z) 2 :=
  (returned_fields R j z 1).eqTrans ((evaluation_product R j z).eqTrans (returned_fields R j z 2).eqSymm)
theorem returned_head (R j z : PTm n) : Γ ⊢[PRAAx] entry (fields (run R j z) 0) zero ≐ qone :=
  (entry_congr (returned_fields R j z 0) (.eqRefl zero)).eqTrans (polynomial_monic R j)

theorem actual_newton_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (polynomial (var 0) (var 1)) ≐ succ (var 1)) ⋏
      ((entry (polynomial (var 0) (var 1)) zero ≐ qone) ⋏ canonicalCoefficients (polynomial (var 0) (var 1)))) :=
  closeUniv 2 (.andI (polynomial_length _ _) (.andI (polynomial_monic _ _) (polynomial_canonical _ _)))
theorem actual_ascending_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ coefficient (var 0) (var 1) (var 2) ≐ entry (polynomial (var 0) (var 1)) (monus (var 1) (var 2))) :=
  closeUniv 3 (.impI (coefficient_inside _ _ _ Prf.hyp0))
theorem actual_above_degree_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 2) ⟶ coefficient (var 0) (var 1) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (coefficient_above _ _ _ Prf.hyp0))
theorem actual_diagonal_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coefficient (var 0) (var 1) (var 1) ≐ qone) := closeUniv 2 (coefficient_diagonal _ _)
theorem actual_forward_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (polynomial (var 0) (var 1)) (var 2) ≐ differenceProduct (var 0) (var 2) (var 1)) :=
  closeUniv 3 (evaluation_product _ _ _)
theorem actual_prior_root_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ evaluate (polynomial (var 0) (var 1)) (entry (var 0) (var 2)) ≐ qzero) :=
  closeUniv 3 (.impI (prior_root_zero _ _ _ Prf.hyp0))
theorem actual_diagonal_pair_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evaluate (polynomial (var 0) (var 1)) (entry (var 0) (var 1)) ≐ differenceProduct (var 0) (entry (var 0) (var 1)) (var 1)) :=
  closeUniv 2 (diagonal_evaluation _ _)
theorem actual_matrix_power_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 1) (var 3) ⟶ powerSum (var 0) (var 1) (var 2) (var 3) ≐ evaluate (polynomial (var 0) (var 1)) (var 2)) :=
  closeUniv 4 (.impI (power_sum_evaluation _ _ _ _ Prf.hyp0))
theorem actual_pair_product_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pairProduct (var 0) (succ (var 1)) ≐ qmul (pairProduct (var 0) (var 1)) (differenceProduct (var 0) (entry (var 0) (var 1)) (var 1))) :=
  closeUniv 2 (pair_succ _ _)
theorem actual_polynomial_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app polynomialF ![var 0,var 1] ≐ polynomial (var 0) (var 1)) := closeUniv 2 (polynomial_program_at _ _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (fields (run (var 0) (var 1) (var 2)) 1 ≐ fields (run (var 0) (var 1) (var 2)) 2) := closeUniv 3 (returned_evaluation _ _ _)
theorem actual_returned_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (fields (run (var 0) (var 1) (var 2)) 0) zero ≐ qone) := closeUniv 3 (returned_head _ _ _)

end LeanProofs.IPRA.Analysis.GaussianVandermondeNewtonPolynomials
