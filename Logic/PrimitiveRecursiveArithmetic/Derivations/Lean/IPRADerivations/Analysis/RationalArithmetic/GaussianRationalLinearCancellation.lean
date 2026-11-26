import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianRationalGridCoefficientEquality
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProductDegree

/-!
# Actual monic linear cancellation and padding of the computed degree

The two actual linear products are compared only on the constructed finite
grid. Its proved coefficient reflection and the actual synthetic-division
inverse recover their original canonical input coefficients. No scalar is
cancelled at the common root, and no polynomial cancellation law is assumed.

Actual zero padding shifts the computed least nonzero coefficient index
by the numerical padding count. Its computed degree is therefore unchanged.
All buffers, roots, widths, padding counts and coefficient queries are
numerical; zero degree and arbitrary raw root codes are included.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalLinearCancellation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero evaluate horner)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (quotient canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct (linear linear_length linear_canonical horner_ext)
open LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality (gridEqual coefficientsEqual)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (first degree nonzeroCoefficients)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr zeroPrefix zero_prefix_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem coefficients_at (C D N i : PTm n) (h : Γ ⊢[PRAAx] coefficientsEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] entry C i ≐ entry D i := by
  have rule : Γ ⊢[PRAAx] le i N ⟶ entry C i ≐ entry D i := by
    simpa [GaussianRationalGridCoefficientEquality.coefficientsEqual] using h.allE i
  exact .impE rule hi
theorem entries_below (C D N : PTm n) (h : Γ ⊢[PRAAx] coefficientsEqual C D N) : Γ ⊢[PRAAx]
    .all (lt (var 0) (Syn.shift N) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] coefficientsEqual (Syn.shift C) (Syn.shift D) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,Syn.shift] using h.shift
  exact .allI (.impI (coefficients_at _ _ _ _ hs.wk (le_of_lt Prf.hyp0)))
theorem inverse_entry (C x N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (quotient (linear C x N) x N) i ≐ entry C i := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ entry (quotient (linear C x N) x N) i ≐ entry C i := by
    simpa using (GaussianRationalLinearProduct.inverse_entries C x N hC hCan).allE i
  exact .impE rule hi

theorem linear_grid_coefficient (C D x B i : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ B) (hD : Γ ⊢[PRAAx] length D ≐ succ B)
    (hCanC : Γ ⊢[PRAAx] canonicalCoefficients C) (hCanD : Γ ⊢[PRAAx] canonicalCoefficients D)
    (hGrid : Γ ⊢[PRAAx] gridEqual (linear C x (succ B)) (linear D x (succ B)) (succ B))
    (hi : Γ ⊢[PRAAx] le i B) : Γ ⊢[PRAAx] entry C i ≐ entry D i := by
  have reflected : Γ ⊢[PRAAx] coefficientsEqual (linear C x (succ B)) (linear D x (succ B)) (succ B) :=
    GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _ (linear_length _ _ _) (linear_length _ _ _)
      (linear_canonical _ _ _) (linear_canonical _ _ _) hGrid
  have hi' : Γ ⊢[PRAAx] lt i (succ B) := (succ_monus_succ _ _).eqTrans hi
  have prefixes := horner_ext (linear C x (succ B)) (linear D x (succ B)) x (succ B) (succ i)
    (entries_below _ _ _ reflected) hi'
  have quotients := (GaussianRationalSyntheticDivision.quotient_lookup (linear C x (succ B)) x (succ B) i hi').eqTrans
    (prefixes.eqTrans (GaussianRationalSyntheticDivision.quotient_lookup (linear D x (succ B)) x (succ B) i hi').eqSymm)
  exact (inverse_entry C x (succ B) i hC hCanC hi').eqSymm.eqTrans
    (quotients.eqTrans (inverse_entry D x (succ B) i hD hCanD hi'))

theorem linear_grid_cancel (C D x B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ B) (hD : Γ ⊢[PRAAx] length D ≐ succ B)
    (hCanC : Γ ⊢[PRAAx] canonicalCoefficients C) (hCanD : Γ ⊢[PRAAx] canonicalCoefficients D)
    (hGrid : Γ ⊢[PRAAx] gridEqual (linear C x (succ B)) (linear D x (succ B)) (succ B)) : Γ ⊢[PRAAx]
    coefficientsEqual C D B := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift B) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift D) ≐ succ (Syn.shift B) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hD.shift
  have ccs : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCanC.shift
  have dcs : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift D) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCanD.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] gridEqual (linear (Syn.shift C) (Syn.shift x) (succ (Syn.shift B)))
      (linear (Syn.shift D) (Syn.shift x) (succ (Syn.shift B))) (succ (Syn.shift B)) := by
    simpa only [Fm.shift,GaussianRationalGridCoefficientEquality.subst_gridEqual,
      GaussianRationalLinearProduct.subst_linear,ConciseIPRA.PTm.subst_succ,Syn.shift] using hGrid.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift] using linear_grid_coefficient (Syn.shift C) (Syn.shift D) (Syn.shift x) (Syn.shift B) (var 0)
    cs.wk ds.wk ccs.wk dcs.wk gs.wk Prf.hyp0

theorem coefficient_evaluation (C D B z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ B)
    (hD : Γ ⊢[PRAAx] length D ≐ succ B) (h : Γ ⊢[PRAAx] coefficientsEqual C D B) : Γ ⊢[PRAAx]
    evaluate C z ≐ evaluate D z := by
  have entries : Γ ⊢[PRAAx] .all (lt (var 0) (succ (Syn.shift B)) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)) := by
    have hs : Γ.map Fm.shift ⊢[PRAAx] coefficientsEqual (Syn.shift C) (Syn.shift D) (Syn.shift B) := by
      simpa only [Fm.shift,GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,Syn.shift] using h.shift
    refine .allI (.impI ?_)
    exact coefficients_at _ _ _ _ hs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  exact (congrAp3 GaussianRationalHorner.hornerF hC (.eqRefl _) (.eqRefl _)).eqTrans
    ((horner_ext _ _ _ _ _ entries (le_refl _)).eqTrans
      (congrAp3 GaussianRationalHorner.hornerF hD.eqSymm (.eqRefl _) (.eqRefl _)))
theorem linear_grid_evaluation (C D x B z : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ B) (hD : Γ ⊢[PRAAx] length D ≐ succ B)
    (hCanC : Γ ⊢[PRAAx] canonicalCoefficients C) (hCanD : Γ ⊢[PRAAx] canonicalCoefficients D)
    (hGrid : Γ ⊢[PRAAx] gridEqual (linear C x (succ B)) (linear D x (succ B)) (succ B)) : Γ ⊢[PRAAx]
    evaluate C z ≐ evaluate D z := coefficient_evaluation _ _ _ _ hC hD (linear_grid_cancel _ _ _ _ hC hD hCanC hCanD hGrid)

theorem pad_zero_before (C t e i : PTm n) (he : Γ ⊢[PRAAx] le e (length C))
    (hPrefix : Γ ⊢[PRAAx] zeroPrefix C e) (hi : Γ ⊢[PRAAx] lt i (t+e)) : Γ ⊢[PRAAx]
    recode (entry (leftPad C t) i) ≐ qzero := by
  refine .orE (lt_or_le i t) ?_ ?_
  · exact (recode_congr (GaussianRationalPolynomialBuffers.pad_leading _ _ _ Prf.hyp0)).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ GaussianRationalSyntheticDivision.qzero_canonical)
  · have range : (le t i) :: Γ ⊢[PRAAx] lt i (t+length C) := le_trans hi.wk (add_le_add₂ (le_refl t) he.wk)
    exact (recode_congr ((GaussianRationalPolynomialBuffers.pad_lookup _ _ _ range).eqTrans
      (GaussianRationalPolynomialBuffers.pad_coefficient_after _ _ _ Prf.hyp0))).eqTrans
        (zero_prefix_at _ _ _ hPrefix.wk (GaussianRationalMonicReconstruction.subtract_bound _ _ _ Prf.hyp0 hi.wk))
theorem pad_zero_prefix (C t e : PTm n) (he : Γ ⊢[PRAAx] le e (length C))
    (hPrefix : Γ ⊢[PRAAx] zeroPrefix C e) : Γ ⊢[PRAAx] zeroPrefix (leftPad C t) (t+e) := by
  have es : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (length (Syn.shift C)) := by
    simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using he.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift C) (Syn.shift e) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hPrefix.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_leftPad,PTm.subst_add] using
    pad_zero_before (Syn.shift C) (Syn.shift t) (Syn.shift e) (var 0) es.wk ps.wk Prf.hyp0
theorem pad_first (C N t : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNonzero : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    first (leftPad C t) (t+N) ≐ t+first C N := by
  have found := GaussianRationalPolynomialDegree.found_of_flag_one C N
    (GaussianRationalPolynomialDegree.flag_one_of_nonzero C N hNonzero)
  have bound := GaussianRationalPolynomialDegree.success_index C N
    (GaussianRationalPolynomialDegree.flag_one_of_nonzero C N hNonzero)
  have originalRange : Γ ⊢[PRAAx] lt (first C N) (length C) := lt_congr (.eqRefl _) hC.eqSymm found
  have paddedEntry := GaussianRationalPolynomialBuffers.pad_tail C t (first C N) originalRange
  have nonzero : Γ ⊢[PRAAx] neg (recode (entry (leftPad C t) (t+first C N)) ≐ qzero) :=
    .impI (.impE (GaussianRationalPolynomialDegree.first_nonzero C N found).wk
      ((recode_congr paddedEntry).wk.eqSymm.eqTrans Prf.hyp0))
  exact GaussianRationalPolynomialProductDegree.first_exact _ _ _ (add_le_add₂ (le_refl t) bound)
    (pad_zero_prefix _ _ _ (le_of_lt originalRange) (GaussianRationalPolynomialDegree.first_zero_prefix _ _)) nonzero
theorem pad_degree (C N t : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hNonzero : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    degree (leftPad C t) (t+N) ≐ degree C N :=
  (congrMonus (.eqRefl _) (pad_first _ _ _ hC hNonzero)).eqTrans
    ((congrMonus (add_comm t N) (add_comm t (first C N))).eqTrans (monus_add_add _ _ _))

def input (C D x B : PTm n) : Fm PTm n := (length C ≐ succ B) ⋏
  ((length D ≐ succ B) ⋏ (canonicalCoefficients C ⋏ (canonicalCoefficients D ⋏
    gridEqual (linear C x (succ B)) (linear D x (succ B)) (succ B))))
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (C D x B : PTm n) :
    (input C D x B).subst σ = input (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) (Syn.subst σ B) := by simp [input]
theorem cancel_from_input (C D x B : PTm n) (h : Γ ⊢[PRAAx] input C D x B) : Γ ⊢[PRAAx] coefficientsEqual C D B :=
  linear_grid_cancel _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h)))
    (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))) (.andE₂ (.andE₂ (.andE₂ (.andE₂ h))))
theorem coefficient_from_input (C D x B i : PTm n) (h : Γ ⊢[PRAAx] input C D x B)
    (hi : Γ ⊢[PRAAx] le i B) : Γ ⊢[PRAAx] entry C i ≐ entry D i :=
  coefficients_at _ _ _ _ (cancel_from_input _ _ _ _ h) hi
theorem evaluation_from_input (C D x B z : PTm n) (h : Γ ⊢[PRAAx] input C D x B) : Γ ⊢[PRAAx] evaluate C z ≐ evaluate D z :=
  coefficient_evaluation _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (cancel_from_input _ _ _ _ h)

/-! The actual PR5 returns the two linear products, their actual synthetic
quotients, and the two selected ORIGINAL coefficient codes. -/
def output (C D x B i : PTm n) : PTm n := pairT (linear C x (succ B))
  (pairT (linear D x (succ B)) (pairT (quotient (linear C x (succ B)) x (succ B))
    (pairT (quotient (linear D x (succ B)) x (succ B)) (pairT (entry C i) (entry D i)))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C D x B i : PTm n) : PTm n := app outputF ![C,D,x,B,i]
def fields (p : PTm n) (i : Fin 6) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),
    fstT (sndT (sndT (sndT (sndT p)))),sndT (sndT (sndT (sndT (sndT p))))] i
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C D x B i : PTm n) :
    Syn.subst σ (output C D x B i) = output (Syn.subst σ C) (Syn.subst σ D)
      (Syn.subst σ x) (Syn.subst σ B) (Syn.subst σ i) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C D x B i : PTm n) :
    Syn.subst σ (run C D x B i) = run (Syn.subst σ C) (Syn.subst σ D)
      (Syn.subst σ x) (Syn.subst σ B) (Syn.subst σ i) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 6) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (C D x B i : PTm n) : Γ ⊢[PRAAx] run C D x B i ≐ output C D x B i := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,D,x,B,i]
theorem returned_fields (C D x B i : PTm n) (j : Fin 6) : Γ ⊢[PRAAx]
    fields (run C D x B i) j ≐ ![linear C x (succ B),linear D x (succ B),
      quotient (linear C x (succ B)) x (succ B),quotient (linear D x (succ B)) x (succ B),entry C i,entry D i] j := by
  have e0 := program_at (Γ := Γ) C D x B i
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  have e4 := (congrSnd e3).eqTrans (snd_pair _ _)
  have e5 := (congrSnd e4).eqTrans (snd_pair _ _)
  fin_cases j
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrFst e4).eqTrans (fst_pair _ _)
  · exact e5
theorem returned_equal (C D x B i : PTm n) (h : Γ ⊢[PRAAx] input C D x B)
    (hi : Γ ⊢[PRAAx] le i B) : Γ ⊢[PRAAx] fields (run C D x B i) 4 ≐ fields (run C D x B i) 5 :=
  (returned_fields _ _ _ _ _ 4).eqTrans ((coefficient_from_input _ _ _ _ _ h hi).eqTrans (returned_fields _ _ _ _ _ 5).eqSymm)
theorem returned_left_inverse (C D x B i : PTm n) (h : Γ ⊢[PRAAx] input C D x B)
    (hi : Γ ⊢[PRAAx] le i B) : Γ ⊢[PRAAx] entry (fields (run C D x B i) 2) i ≐ fields (run C D x B i) 4 :=
  (Foundations.SequenceComposition.entry_congr (returned_fields _ _ _ _ _ 2) (.eqRefl _)).eqTrans
    ((inverse_entry _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ (.andE₂ h))) ((succ_monus_succ _ _).eqTrans hi)).eqTrans
      (returned_fields _ _ _ _ _ 4).eqSymm)
theorem returned_right_inverse (C D x B i : PTm n) (h : Γ ⊢[PRAAx] input C D x B)
    (hi : Γ ⊢[PRAAx] le i B) : Γ ⊢[PRAAx] entry (fields (run C D x B i) 3) i ≐ fields (run C D x B i) 5 :=
  (Foundations.SequenceComposition.entry_congr (returned_fields _ _ _ _ _ 3) (.eqRefl _)).eqTrans
    ((inverse_entry _ _ _ _ (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))) ((succ_monus_succ _ _).eqTrans hi)).eqTrans
      (returned_fields _ _ _ _ _ 5).eqSymm)

/-! Every buffer/root/width/padding/query is internally bound. Original
finite comparisons and canonical inputs are the cancellation guards. -/
theorem actual_linear_grid_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 3) ⟶ entry (var 0) (var 4) ≐ entry (var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (coefficient_from_input _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_linear_grid_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ coefficientsEqual (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (cancel_from_input _ _ _ _ Prf.hyp0))
theorem actual_canceled_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ evaluate (var 0) (var 4) ≐ evaluate (var 1) (var 4)) :=
  closeUniv 5 (.impI (evaluation_from_input _ _ _ _ _ Prf.hyp0))
theorem actual_padded_zero_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (length (var 0)) ⟶ zeroPrefix (var 0) (var 2) ⟶ zeroPrefix (leftPad (var 0) (var 1)) (var 1+var 2)) :=
  closeUniv 3 (.impI (.impI (pad_zero_prefix _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_padding_first_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ nonzeroCoefficients (var 0) (var 1) ⟶
      first (leftPad (var 0) (var 2)) (var 2+var 1) ≐ var 2+first (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (pad_first _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_padding_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ nonzeroCoefficients (var 0) (var 1) ⟶
      degree (leftPad (var 0) (var 2)) (var 2+var 1) ≐ degree (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (pad_degree _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cancellation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_original_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 3) ⟶
      fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 4 ≐ fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 5) :=
  closeUniv 5 (.impI (.impI (returned_equal _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_quotient_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 3) ⟶
      ((entry (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 2) (var 4) ≐
        fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 4) ⋏
          (entry (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 3) (var 4) ≐
            fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 5))) :=
  closeUniv 5 (.impI (.impI (.andI (returned_left_inverse _ _ _ _ _ Prf.hyp1 Prf.hyp0)
    (returned_right_inverse _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalLinearCancellation
