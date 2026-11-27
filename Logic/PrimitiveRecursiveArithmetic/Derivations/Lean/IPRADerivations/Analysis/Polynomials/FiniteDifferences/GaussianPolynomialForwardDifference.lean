import IPRADerivations.Analysis.Polynomials.Translation.GaussianTranslationCoefficientValues
import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDegree
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.MonicReduction.GaussianRationalMonicCompanion
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality

/-!
# One Gaussian polynomial forward difference at encoded degree

Subtract the original descending coefficient buffer from its translation,
and drop the certified leading zero. The resulting polynomial evaluates
to the forward difference. Two quotient-stage invariants compute its
leading coefficient for every positive encoded source degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifference

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open GaussianCoefficientL1 (subCoefficients sub_lookup subF zip_length)
open GaussianRationalHorner (qadd qmul qzero evaluate horner hornerF)
open GaussianRationalMetric (qsub)
open GaussianRationalNaturalScale (natScale natScale_congr natScale_canonical)
open GaussianRationalPolynomialDegree (canonicalTail tail_length tail_lookup tail_evaluation)
open GaussianRationalSyntheticCoefficientValues
  (qmul_recode_left qadd_recode_left qadd_recode_right singleton_evaluation)
open GaussianRationalSyntheticDivision
  (quotient quotient_lookup first_prefix qadd_congr qmul_congr qsub_congr)
open GaussianRationalTranslation (translated translated_lookup translated_length translation_evaluation)
open GaussianRationalTranslationStages (stage remaining stage_zero stage_succ stage_length remaining_step remaining_positive)
open GaussianTranslatedNonconstant (recode recode_congr recode_canonical recode_eq zeroPrefix)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def padded (C N h : PTm n) : PTm n := subCoefficients (translated C N h) C (succ N)

def difference (C N h : PTm n) : PTm n := canonicalTail (padded C N h) one N

@[simp] theorem subst_padded {l : ℕ} (σ : Fin n → PTm l) (C N h : PTm n) :
    Syn.subst σ (padded C N h) = padded (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) := by simp [padded]

@[simp] theorem subst_difference {l : ℕ} (σ : Fin n → PTm l) (C N h : PTm n) :
    Syn.subst σ (difference C N h) = difference (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) := by simp [difference]

theorem difference_length (C N h : PTm n) : Γ ⊢[PRAAx] length (difference C N h) ≐ N := tail_length _ _ _

private def headLaw (C N h j : PTm n) : Fm PTm n := le j N ⟶
  recode (entry (stage C N h j) zero) ≐ recode (entry C zero)

@[simp] private theorem subst_headLaw {l : ℕ} (σ : Fin n → PTm l) (C N h j : PTm n) :
    (headLaw C N h j).subst σ = headLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ j) := by
  simp [headLaw]

theorem quotient_stage_head (C N h j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] recode (entry (stage C N h j) zero) ≐ recode (entry C zero) := by
  have all : Γ ⊢[PRAAx] .all (headLaw (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_headLaw]
    · exact .impI (recode_congr (entry_congr (stage_zero C N h) (.eqRefl _))).wk
    · refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) ::
        headLaw (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0) :: Γ.map Fm.shift
      let P := stage (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0)
      have next : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] headLaw _ _ _ _) (le_trans (le_succ_self _) next)
      have raw := GaussianRationalSyntheticCoefficientValues.leading_coefficient P (Syn.shift h)
        (remaining (Syn.shift N) (var 0)) (remaining_positive _ _ next)
      exact (recode_congr (entry_congr (stage_succ _ _ _ _) (.eqRefl _))).eqTrans (raw.eqSymm.eqTrans ih)
  have rule : Γ ⊢[PRAAx] headLaw C N h j := by
    simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

private theorem two_prefix (C h : PTm n) : Γ ⊢[PRAAx] horner C h two ≐
    qadd (recode (entry C one)) (qmul (recode (entry C zero)) h) := by
  refine (GaussianRationalHorner.horner_succ C h one).eqTrans ?_
  refine (qadd_congr (qmul_congr (first_prefix C h) (.eqRefl _)) (.eqRefl _)).eqTrans ?_
  exact (GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (qadd_recode_left _ _).eqSymm

private theorem add_scaled_step (a b j : PTm n) (ha : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a) :
    Γ ⊢[PRAAx] qadd (qadd b (natScale j a)) a ≐ qadd b (natScale (succ j) a) := by
  have scaled : Γ ⊢[PRAAx] natScale (succ j) a ≐ qadd (natScale j a) a :=
    (natScale_congr (by ipra_ring) (.eqRefl _)).eqTrans
      ((GaussianRationalNaturalScale.natScale_add j one a).eqTrans
        (qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_one_canonical a ha)))
  exact (GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans (qadd_congr (.eqRefl _) scaled.eqSymm)

private def secondLaw (C N h j : PTm n) : Fm PTm n := lt j N ⟶
  recode (entry (stage C N h j) one) ≐
    qadd (recode (entry C one)) (natScale j (qmul (entry C zero) h))

@[simp] private theorem subst_secondLaw {l : ℕ} (σ : Fin n → PTm l) (C N h j : PTm n) :
    (secondLaw C N h j).subst σ = secondLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ j) := by
  simp [secondLaw,one]

private theorem second_step (C N h j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) N)
    (ih : Γ ⊢[PRAAx] recode (entry (stage C N h j) one) ≐
      qadd (recode (entry C one)) (natScale j (qmul (entry C zero) h))) :
    Γ ⊢[PRAAx] recode (entry (stage C N h (succ j)) one) ≐
      qadd (recode (entry C one)) (natScale (succ j) (qmul (entry C zero) h)) := by
  let P := stage C N h j
  let a := qmul (entry C zero) h
  have before : Γ ⊢[PRAAx] lt j N := lt_of_le_of_lt (le_succ_self _) hj
  have inside : Γ ⊢[PRAAx] lt one (remaining N j) :=
    le_congr (.eqRefl _) (remaining_step N j before).eqSymm
      ((succ_monus_succ one _).eqTrans (remaining_positive N (succ j) hj))
  have lead := (qmul_congr (quotient_stage_head C N h j (le_trans (le_succ_self _) before)) (.eqRefl _)).eqTrans
    (qmul_recode_left (entry C zero) h)
  have write : Γ ⊢[PRAAx] entry (stage C N h (succ j)) one ≐ horner P h two :=
    (entry_congr (stage_succ C N h j) (.eqRefl _)).eqTrans (quotient_lookup P h (remaining N j) one inside)
  exact (recode_congr write).eqTrans ((recode_eq _ (GaussianRationalHorner.horner_canonical _ _ _)).eqTrans
    ((two_prefix P h).eqTrans ((qadd_congr ih lead).eqTrans
      (add_scaled_step a _ j (GaussianRationalHorner.qmul_canonical _ _)))))

theorem quotient_stage_second (C N h j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] recode (entry (stage C N h j) one) ≐
      qadd (recode (entry C one)) (natScale j (qmul (entry C zero) h)) := by
  have all : Γ ⊢[PRAAx] .all (secondLaw (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0)) := by
    ipra_qfind (⟨lt_QF _ _,trivial⟩) [subst_secondLaw]
    · refine .impI ?_
      exact (recode_congr (entry_congr (stage_zero C N h) (.eqRefl _))).eqTrans
        ((qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_zero _)).eqTrans
          (GaussianReciprocalHorner.qadd_zero_right _ (recode_canonical _))).eqSymm
    · refine .impI ?_
      have next : lt (succ (var 0)) (Syn.shift N) ::
          secondLaw (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0) :: Γ.map Fm.shift
          ⊢[PRAAx] lt (succ (var 0)) (Syn.shift N) := Prf.hyp0
      exact second_step _ _ _ _ next (.impE Prf.hyp1 (lt_of_le_of_lt (le_succ_self _) next))
  have rule : Γ ⊢[PRAAx] secondLaw C N h j := by
    simpa only [subst_secondLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem translated_head (C N h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] entry (translated C N h) zero ≐ recode (entry C zero) := by
  let P := stage C N h N
  have shape := GaussianRationalTranslationStages.terminal_length C N h hC
  exact (translated_lookup C N h zero (zero_le N)).eqTrans
    ((GaussianRationalTranslation.evaluate_congr
        (GaussianRationalTranslation.stage_index_congr C N h (monus_zero N)) (.eqRefl _)).eqTrans
      ((singleton_evaluation P h shape).eqSymm.eqTrans (quotient_stage_head C N h N (le_refl _))))

theorem translated_second (C N h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] entry (translated C N h) one ≐ qadd (recode (entry C one)) (natScale N (qmul (entry C zero) h)) := by
  let j := monus N one
  let P := stage C N h j
  let a := qmul (entry C zero) h
  have hj : Γ ⊢[PRAAx] lt j N :=
    le_congr (.eqRefl _) ((eq_add_of_le hN).eqTrans (by ipra_ring)).eqSymm (le_refl _)
  have remain : Γ ⊢[PRAAx] remaining N j ≐ one :=
    (congrMonus (eq_add_of_le hN) (.eqRefl _)).eqTrans (add_monus _ _)
  have len : Γ ⊢[PRAAx] length P ≐ two :=
    (stage_length C N h j hC (le_trans (le_succ_self _) hj)).eqTrans (congrSucc remain)
  have lead := (qmul_congr (quotient_stage_head C N h j (le_trans (le_succ_self _) hj)) (.eqRefl _)).eqTrans
    (qmul_recode_left (entry C zero) h)
  have second := quotient_stage_second C N h j hj
  exact (translated_lookup C N h one hN).eqTrans
    ((congrAp3 hornerF len (.eqRefl _) (.eqRefl _)).eqTrans
      ((two_prefix P h).eqTrans ((qadd_congr second lead).eqTrans
        ((add_scaled_step a _ j (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
          (qadd_congr (.eqRefl _) (natScale_congr ((eq_add_of_le hN).eqTrans (by ipra_ring)).eqSymm (.eqRefl _)))))))

private theorem padded_head_zero (C N h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] entry (padded C N h) zero ≐ qzero := by
  have e := translated_head C N h hC
  have zeroDiff := (GaussianRationalValueEquality.recode_eq_iff_difference_zero (entry (translated C N h) zero)
    (entry C zero)).iffMp ((recode_congr e).eqTrans (recode_eq _ (recode_canonical _)))
  exact (sub_lookup _ _ _ _ (zero_lt_succ N)).eqTrans zeroDiff

private theorem padded_zero_prefix (C N h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] zeroPrefix (padded C N h) one := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) one :: Γ.map Fm.shift
  have hc : Δ ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa [Δ,Fm.shift,Syn.shift] using hC.shift.wk
  have atZero : Δ ⊢[PRAAx] (var 0 : PTm (n+1)) ≐ zero :=
    le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) (zero_le _)
  have e := (entry_congr (.eqRefl (padded (Syn.shift C) (Syn.shift N) (Syn.shift h))) atZero).eqTrans
    (padded_head_zero (Syn.shift C) (Syn.shift N) (Syn.shift h) hc)
  simpa [zeroPrefix,Syn.shift,Δ,one] using
    (recode_congr e).eqTrans (recode_eq _ GaussianRationalSyntheticDivision.qzero_canonical)

theorem evaluation (C N h x : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] evaluate (difference C N h) x ≐ qsub (evaluate C (qadd h x)) (evaluate C x) := by
  have extended : Γ ⊢[PRAAx] one+N ≐ length (padded C N h) :=
    ((show Γ ⊢[PRAAx] one+N ≐ succ N by ipra_ring)).eqTrans (zip_length subF _ _ _).eqSymm
  refine (tail_evaluation _ _ _ _ (padded_zero_prefix C N h hC)).eqTrans ?_
  refine (congrAp3 hornerF extended (.eqRefl _) (.eqRefl _)).eqTrans ?_
  exact (GaussianRationalMonicCompanion.difference_evaluation _ _ _ _ (translated_length C N h) hC).eqTrans
    (qsub_congr (translation_evaluation C N h x hC) (.eqRefl _))

theorem leading (C N h : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] entry (difference C N h) zero ≐ natScale N (qmul (entry C zero) h) := by
  let a := natScale N (qmul (entry C zero) h)
  let b := entry C one
  have e : Γ ⊢[PRAAx] entry (padded C N h) one ≐ a := by
    refine (sub_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hN)).eqTrans ?_
    refine (qsub_congr (translated_second C N h hC hN) (.eqRefl _)).eqTrans ?_
    refine (qsub_congr ((GaussianReciprocalHorner.qadd_commutative (recode b) a).eqTrans (qadd_recode_right a b))
      (.eqRefl _)).eqTrans ?_
    exact GaussianReciprocalHorner.qsub_add_cancel a b (natScale_canonical _ _)
  exact (tail_lookup _ _ _ _ hN).eqTrans
    ((recode_congr ((entry_congr (.eqRefl _) (add_zero one)).eqTrans e)).eqTrans (recode_eq _ (natScale_canonical _ _)))

theorem actual_Gaussian_polynomial_forward_difference_evaluation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (difference (var 0) (var 1) (var 2)) (var 3) ≐
        qsub (evaluate (var 0) (qadd (var 2) (var 3))) (evaluate (var 0) (var 3))) :=
  closeUniv 4 (.impI (evaluation _ _ _ _ Prf.hyp0))

theorem actual_Gaussian_polynomial_forward_difference_leading_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (var 0) ≐ succ (var 1) ⋏ le one (var 1)) ⟶
      (length (difference (var 0) (var 1) (var 2)) ≐ var 1 ⋏
        entry (difference (var 0) (var 1) (var 2)) zero ≐ natScale (var 1) (qmul (entry (var 0) zero) (var 2)))) :=
  closeUniv 3 (.impI (.andI (difference_length _ _ _) (leading _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifference
