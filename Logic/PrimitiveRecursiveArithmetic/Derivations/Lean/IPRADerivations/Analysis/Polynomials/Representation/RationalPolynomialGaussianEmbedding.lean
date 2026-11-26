import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianEmbedding

/-!
# Actual rational coefficient lists and Horner evaluation in the real axis

The scalar fold uses the original RationalArithmetic operations. An actual
sequence embeds the first numerical N original coefficients. A guarded QF
prefix induction proves exact conjugacy with the existing Gaussian Horner
program. Empty lists and arbitrary raw coefficient and point codes are valid.
No polynomial evaluator, coefficient representation or output law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed embedF embed_at scalarZero axis embed_axis embed_zero)
open GaussianRationalHorner (qzero qadd qmul canonical canonical_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientBody : PTm 2 := embed (entry (var 1) (var 0))
def coefficients (C N : PTm n) : PTm n := sequence coefficientBody N C
def hornerStep : PTm 4 := RationalArithmetic.add
  (RationalArithmetic.multiply (var 1) (var 3)) (entry (var 2) (var 0))
def hornerF : PR 3 := recDef (scalarZero : PTm 2) hornerStep
def horner (C z j : PTm n) : PTm n := ap3 hornerF j C z
def evaluate (C z : PTm n) : PTm n := horner C z (length C)

ipra_subst coefficients
ipra_subst horner
ipra_subst evaluate

theorem embed_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] embed a ≐ embed b :=
  (embed_at a).eqSymm.eqTrans ((congrAp1 embedF h).eqTrans (embed_at b))

theorem coefficients_length (C N : PTm n) : Γ ⊢[PRAAx] length (coefficients C N) ≐ N :=
  sequence_length _ _ _
theorem coefficient_lookup (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (coefficients C N) i ≐ embed (entry C i) := by
  simpa only [coefficientBody,coefficients,inst2,RationalGaussianEmbedding.subst_embed,
    Foundations.MasterCertificate.subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      sequence_decode (Γ := Γ) coefficientBody (N := N) (x := C) hi

theorem coefficient_canonical (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] canonical (entry (coefficients C N) i) :=
  canonical_congr (coefficient_lookup C N i hi) (RationalGaussianEmbedding.embed_canonical _)
theorem coefficient_axis (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] axis (entry (coefficients C N) i) :=
  RationalGaussianEmbedding.axis_congr (coefficient_lookup C N i hi).eqSymm (embed_axis _)

theorem coefficients_canonical (C N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (coefficients C N) := by
  refine .allI (.impI ?_)
  have hN : lt (var 0) (length (Syn.shift (coefficients C N))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (Syn.shift N) := lt_congr (.eqRefl _)
        (by simpa only [Syn.shift,subst_coefficients] using coefficients_length (Syn.shift C) (Syn.shift N)) Prf.hyp0
  simpa only [Syn.shift,subst_coefficients] using coefficient_canonical (Syn.shift C) (Syn.shift N) (var 0) hN

theorem horner_zero (C z : PTm n) : Γ ⊢[PRAAx] horner C z zero ≐ scalarZero := by
  have h := rec_zero (Γ := Γ) (scalarZero : PTm 2) hornerStep ![C,z]
  have e : (Fin.cases zero ![C,z] : Fin 3 → PTm n) = ![zero,C,z] := by funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa only [horner,hornerF,ap3,RationalGaussianEmbedding.subst_scalarZero] using h

theorem horner_succ (C z j : PTm n) : Γ ⊢[PRAAx]
    horner C z (succ j) ≐ RationalArithmetic.add (RationalArithmetic.multiply (horner C z j) z) (entry C j) := by
  have h := rec_succ (Γ := Γ) (scalarZero : PTm 2) hornerStep j ![C,z]
  have e₁ : (Fin.cases (succ j) ![C,z] : Fin 3 → PTm n) = ![succ j,C,z] := by funext i; fin_cases i <;> rfl
  have e₂ : (Fin.cases j (Fin.cases (PTm.app (recDef (scalarZero : PTm 2) hornerStep) (Fin.cases j ![C,z])) ![C,z]) :
      Fin 4 → PTm n) = ![j,horner C z j,C,z] := by funext i; fin_cases i <;> rfl
  rw [e₁,e₂] at h
  simpa [horner,hornerF,ap3,hornerStep] using h

theorem horner_canonical (C z j : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (horner C z j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact RationalArithmetic.guard_congr
      ((congrAp3 hornerF Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (horner_zero C z))
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  · exact RationalArithmetic.guard_congr
      ((congrAp3 hornerF Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (horner_succ C z _))
      (RationalArithmetic.add_guard _ _)

def prefixLaw (C z N j : PTm n) : Fm PTm n := le j N ⟶
  embed (horner C z j) ≐ GaussianRationalHorner.horner (coefficients C N) (embed z) j
ipra_subst prefixLaw

theorem prefix_step (C z N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ih : Γ ⊢[PRAAx] embed (horner C z j) ≐ GaussianRationalHorner.horner (coefficients C N) (embed z) j) :
    Γ ⊢[PRAAx] embed (horner C z (succ j)) ≐
      GaussianRationalHorner.horner (coefficients C N) (embed z) (succ j) :=
  (embed_congr (horner_succ C z j)).eqTrans
    ((RationalGaussianEmbedding.embed_add _ _).eqTrans
      ((qadd_congr (RationalGaussianEmbedding.embed_multiply _ _) (.eqRefl _)).eqTrans
        ((qadd_congr (qmul_congr ih (.eqRefl _)) (coefficient_lookup C N j hj).eqSymm).eqTrans
          (GaussianRationalHorner.horner_succ _ _ _).eqSymm)))

theorem horner_conjugacy (C z N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] embed (horner C z j) ≐ GaussianRationalHorner.horner (coefficients C N) (embed z) j := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI ((embed_congr (horner_zero C z)).eqTrans
        (embed_zero.eqTrans (GaussianRationalHorner.horner_zero _ _).eqSymm))
    · refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) :: prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] embed (horner (Syn.shift C) (Syn.shift z) (var 0)) ≐
          GaussianRationalHorner.horner (coefficients (Syn.shift C) (Syn.shift N)) (embed (Syn.shift z)) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact prefix_step _ _ _ _ Prf.hyp0 ih
  have atJ : Γ ⊢[PRAAx] prefixLaw C z N j := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE atJ hj

theorem evaluation_conjugacy (C z : PTm n) : Γ ⊢[PRAAx]
    embed (evaluate C z) ≐ GaussianRationalHorner.evaluate (coefficients C (length C)) (embed z) :=
  (horner_conjugacy C z (length C) (length C) (le_refl _)).eqTrans
    (congrAp3 GaussianRationalHorner.hornerF (coefficients_length C (length C)).eqSymm (.eqRefl _) (.eqRefl _))

theorem evaluation_axis (C z : PTm n) : Γ ⊢[PRAAx]
    axis (GaussianRationalHorner.evaluate (coefficients C (length C)) (embed z)) :=
  RationalGaussianEmbedding.axis_congr (evaluation_conjugacy C z) (embed_axis _)

theorem evaluation_zero_iff (C z : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (GaussianRationalHorner.evaluate (coefficients C (length C)) (embed z) ≐ qzero)
    (RationalArgmin.rationalEq (evaluate C z) scalarZero) :=
  .andI (.impI (.impE (Prf.andE₁ (RationalGaussianEmbedding.zero_iff _))
      ((evaluation_conjugacy C z).eqTrans Prf.hyp0)))
    (.impI ((evaluation_conjugacy C z).eqSymm.eqTrans
      (.impE (Prf.andE₂ (RationalGaussianEmbedding.zero_iff _)) Prf.hyp0)))

theorem axis_point_conjugacy (C q N j : PTm n) (hq : Γ ⊢[PRAAx] axis q) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] GaussianRationalHorner.horner (coefficients C N) q j ≐ embed (horner C (fstT q) j) :=
  (GaussianRationalValueEquality.horner_query_proper _ _ _ _
    ((RationalGaussianEmbedding.axis_roundtrip q hq).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical _)).eqSymm)).eqTrans
    (horner_conjugacy C (fstT q) N j hj).eqSymm

theorem axis_evaluation_conjugacy (C q : PTm n) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] GaussianRationalHorner.evaluate (coefficients C (length C)) q ≐ embed (evaluate C (fstT q)) :=
  (congrAp3 GaussianRationalHorner.hornerF (coefficients_length C (length C)) (.eqRefl _) (.eqRefl _)).eqTrans
    (axis_point_conjugacy C q (length C) (length C) hq (le_refl _))

theorem real_axis_evaluation (C q : PTm n) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] axis (GaussianRationalHorner.evaluate (coefficients C (length C)) q) :=
  RationalGaussianEmbedding.axis_congr (axis_evaluation_conjugacy C q hq).eqSymm (embed_axis _)

def coefficientsF : PR 2 := PTm.toPR (coefficients (var 0) (var 1))
def evaluateF : PR 2 := PTm.toPR (evaluate (var 0) (var 1))
theorem coefficients_at (C N : PTm n) : Γ ⊢[PRAAx] ap2 coefficientsF C N ≐ coefficients C N := by
  simpa [coefficientsF,ap2] using toPR_eq (Γ := Γ) (coefficients (var 0) (var 1) : PTm 2) ![C,N]
theorem evaluate_at (C z : PTm n) : Γ ⊢[PRAAx] ap2 evaluateF C z ≐ evaluate C z := by
  simpa [evaluateF,ap2] using toPR_eq (Γ := Γ) (evaluate (var 0) (var 1) : PTm 2) ![C,z]

theorem coefficient_program_lookup (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] entry (ap2 coefficientsF C N) i ≐ ap1 embedF (entry C i) :=
  (entry_congr (coefficients_at C N) (.eqRefl _)).eqTrans
    ((coefficient_lookup C N i hi).eqTrans (embed_at _).eqSymm)

theorem program_evaluation_conjugacy (C z : PTm n) : Γ ⊢[PRAAx]
    ap1 embedF (ap2 evaluateF C z) ≐
      GaussianRationalHorner.evaluate (ap2 coefficientsF C (length C)) (ap1 embedF z) :=
  (embed_at _).eqTrans ((embed_congr (evaluate_at C z)).eqTrans
    ((evaluation_conjugacy C z).eqTrans
      (congrAp3 GaussianRationalHorner.hornerF (congrFst (coefficients_at C (length C))).eqSymm
        (coefficients_at C (length C)).eqSymm (embed_at z).eqSymm)))

theorem actual_coefficients_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (coefficients (var 0) (var 1)) ≐ var 1) := closeUniv 2 (coefficients_length _ _)
theorem actual_coefficients_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ entry (coefficients (var 0) (var 1)) (var 2) ≐ embed (entry (var 0) (var 2))) :=
  closeUniv 3 (.impI (coefficient_lookup _ _ _ Prf.hyp0))
theorem actual_coefficients_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonicalCoefficients (coefficients (var 0) (var 1))) := closeUniv 2 (coefficients_canonical _ _)
theorem actual_rational_horner_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (horner (var 0) (var 1) (succ (var 2)) ≐ RationalArithmetic.add
      (RationalArithmetic.multiply (horner (var 0) (var 1) (var 2)) (var 1)) (entry (var 0) (var 2))) :=
  closeUniv 3 (horner_succ _ _ _)
theorem actual_horner_conjugacy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 2) ⟶ embed (horner (var 0) (var 1) (var 3)) ≐
      GaussianRationalHorner.horner (coefficients (var 0) (var 2)) (embed (var 1)) (var 3)) :=
  closeUniv 4 (.impI (horner_conjugacy _ _ _ _ Prf.hyp0))
theorem actual_evaluation_conjugacy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (evaluate (var 0) (var 1)) ≐
      GaussianRationalHorner.evaluate (coefficients (var 0) (length (var 0))) (embed (var 1))) :=
  closeUniv 2 (evaluation_conjugacy _ _)
theorem actual_evaluation_axis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (axis (GaussianRationalHorner.evaluate (coefficients (var 0) (length (var 0))) (embed (var 1)))) :=
  closeUniv 2 (evaluation_axis _ _)
theorem actual_raw_axis_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (axis (var 1) ⟶ axis (GaussianRationalHorner.evaluate (coefficients (var 0) (length (var 0))) (var 1))) :=
  closeUniv 2 (.impI (real_axis_evaluation _ _ Prf.hyp0))
theorem actual_evaluation_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (GaussianRationalHorner.evaluate (coefficients (var 0) (length (var 0))) (embed (var 1)) ≐ qzero)
      (RationalArgmin.rationalEq (evaluate (var 0) (var 1)) scalarZero)) := closeUniv 2 (evaluation_zero_iff _ _)
theorem actual_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ entry (ap2 coefficientsF (var 0) (var 1)) (var 2) ≐ ap1 embedF (entry (var 0) (var 2))) :=
  closeUniv 3 (.impI (coefficient_program_lookup _ _ _ Prf.hyp0))
theorem actual_evaluation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 evaluateF (var 0) (var 1) ≐ evaluate (var 0) (var 1)) := closeUniv 2 (evaluate_at _ _)
theorem actual_program_conjugacy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap1 embedF (ap2 evaluateF (var 0) (var 1)) ≐ GaussianRationalHorner.evaluate
      (ap2 coefficientsF (var 0) (length (var 0))) (ap1 embedF (var 1))) :=
  closeUniv 2 (program_evaluation_conjugacy _ _)

end LeanProofs.IPRA.Analysis.RationalPolynomialGaussianEmbedding
