import IPRADerivations.Analysis.Polynomials.GaussianRationalPolynomialBuffers
import IPRADerivations.Analysis.Polynomials.GaussianRationalHornerPerturbation

/-!
# Actual multiplication by the variable modulo a monic polynomial

Descending coefficients P=[1,...] have numerical length D+1 and R has
length D. The program forms the actual shift R++[0], subtracts its leading
coefficient times P, and returns the D coefficients after the proved zero
head. Only the original shapes and monic head are input contracts.
This is one monic reduction step, not a complete norm constructor.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalMonicCompanion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul canonical horner hornerF evaluate represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qsub_congr qzero_canonical qmul_zero_left qzero_add canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling
  (scaled scaled_length scaled_lookup evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (appendZero append_length append_lookup append_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalSumSegments
  (segment segment_length segment_lookup)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1
  (subCoefficients sub_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sub_length (C E L : PTm n) : Γ ⊢[PRAAx] length (subCoefficients C E L) ≐ L :=
  GaussianCoefficientL1.zip_length _ _ _ _

def differenceLaw (C E L z r : PTm n) : Fm PTm n := le r L ⟶
  horner (subCoefficients C E L) z r ≐ qsub (horner C z r) (horner E z r)
@[simp] theorem subst_differenceLaw {m : ℕ} (σ : Fin n → PTm m) (C E L z r : PTm n) :
    (differenceLaw C E L z r).subst σ = differenceLaw (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ L) (Syn.subst σ z) (Syn.subst σ r) := by simp [differenceLaw]

theorem difference_prefix (C E L z r : PTm n) (hr : Γ ⊢[PRAAx] le r L) : Γ ⊢[PRAAx]
    horner (subCoefficients C E L) z r ≐ qsub (horner C z r) (horner E z r) := by
  have all : Γ ⊢[PRAAx] .all (differenceLaw (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_differenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianRationalHorner.horner_zero _ _).eqTrans
        ((GaussianCoefficientNormOrder.qsub_self qzero).eqSymm.eqTrans
          (qsub_congr (GaussianRationalHorner.horner_zero C z).eqSymm
            (GaussianRationalHorner.horner_zero E z).eqSymm)))
    · simp only [subst_differenceLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift L) ::
        differenceLaw (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (subCoefficients (Syn.shift C) (Syn.shift E) (Syn.shift L)) (Syn.shift z) (var 0) ≐
          qsub (horner (Syn.shift C) (Syn.shift z) (var 0)) (horner (Syn.shift E) (Syn.shift z) (var 0)) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr (qmul_congr ih (.eqRefl _)) (sub_lookup _ _ _ _ Prf.hyp0)).eqTrans
          (GaussianRationalHornerPerturbation.horner_difference_succ _ _ _ _).eqSymm)
  have rule : Γ ⊢[PRAAx] differenceLaw C E L z r := by
    simpa only [subst_differenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem difference_evaluation (C E L z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ L)
    (hE : Γ ⊢[PRAAx] length E ≐ L) : Γ ⊢[PRAAx]
    evaluate (subCoefficients C E L) z ≐ qsub (evaluate C z) (evaluate E z) :=
  (congrAp3 hornerF (sub_length C E L) (.eqRefl _) (.eqRefl _)).eqTrans
    ((difference_prefix C E L z L (le_refl _)).eqTrans
      (qsub_congr (congrAp3 hornerF hC.eqSymm (.eqRefl _) (.eqRefl _))
        (congrAp3 hornerF hE.eqSymm (.eqRefl _) (.eqRefl _))))

/-- A raw coefficient and its normalized product with one have zero
normalized difference; this does not assert equality with the raw code. -/
theorem raw_unit_difference (q : PTm n) : Γ ⊢[PRAAx] qsub q (qmul q qone) ≐ qzero := by
  let E := GaussianRationalL1.rawDen q
  let A := GaussianRationalL1.rawGaussian q
  have hE : Γ ⊢[PRAAx] le one E := GaussianRationalL1.raw_den_positive q
  have hE2 := positive_product E E hE hE
  have hq : Γ ⊢[PRAAx] represents q A E := GaussianRationalL1.raw_represents q
  have hp := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hE hE hq
    (GaussianRationalReciprocal.qone_represents_scaled E)
  have hs := GaussianRationalHorner.represents_rescale q A E E hq
  have diff := qsub_represents _ _ _ _ _ hE2 hs hp
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (qsub_canonical _ _) qzero_canonical hE2
    (hrv := GaussianRationalHorner.zero_represents _)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := diff)
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
    GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,
    GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero]; ring

def tailLaw (C D z r : PTm n) : Fm PTm n := le r D ⟶
  horner C z (succ r) ≐ horner (segment C one D) z r
@[simp] theorem subst_tailLaw {m : ℕ} (σ : Fin n → PTm m) (C D z r : PTm n) :
    (tailLaw C D z r).subst σ = tailLaw (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ z) (Syn.subst σ r) := by simp [tailLaw]

theorem zero_head_prefix (C D z r : PTm n) (hHead : Γ ⊢[PRAAx] entry C zero ≐ qzero)
    (hr : Γ ⊢[PRAAx] le r D) : Γ ⊢[PRAAx]
    horner C z (succ r) ≐ horner (segment C one D) z r := by
  have all : Γ ⊢[PRAAx] .all (tailLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianRationalHorner.horner_succ C z zero).eqTrans
        ((qadd_congr ((qmul_congr (GaussianRationalHorner.horner_zero C z) (.eqRefl _)).eqTrans
          (qmul_zero_left z)) hHead).eqTrans
            ((qzero_add qzero qzero_canonical).eqTrans (GaussianRationalHorner.horner_zero _ _).eqSymm))).wk
    · simp only [subst_tailLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift D) :: tailLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] horner (Syn.shift C) (Syn.shift z) (succ (var 0)) ≐
          horner (segment (Syn.shift C) one (Syn.shift D)) (Syn.shift z) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have coefficient : Δ ⊢[PRAAx] entry (Syn.shift C) (succ (var 0)) ≐
          entry (segment (Syn.shift C) one (Syn.shift D)) (var 0) :=
        (entry_congr (.eqRefl _) (by ipra_ring : Δ ⊢[PRAAx] succ (var 0) ≐ one+var 0)).eqTrans
          (segment_lookup _ _ _ _ Prf.hyp0).eqSymm
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((qadd_congr (qmul_congr ih (.eqRefl _)) coefficient).eqTrans (GaussianRationalHorner.horner_succ _ _ _).eqSymm)
  have rule : Γ ⊢[PRAAx] tailLaw C D z r := by
    simpa only [subst_tailLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem zero_head_evaluation (C D z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ D)
    (hHead : Γ ⊢[PRAAx] entry C zero ≐ qzero) : Γ ⊢[PRAAx]
    evaluate C z ≐ evaluate (segment C one D) z :=
  (congrAp3 hornerF hC (.eqRefl _) (.eqRefl _)).eqTrans
    ((zero_head_prefix C D z D hHead (le_refl _)).eqTrans
      (congrAp3 hornerF (segment_length C one D).eqSymm (.eqRefl _) (.eqRefl _)))

def lead (R : PTm n) : PTm n := entry R zero
def fullDifference (P R D : PTm n) : PTm n :=
  subCoefficients (appendZero R) (scaled P (lead R)) (succ D)
def companionY (P R D : PTm n) : PTm n := segment (fullDifference P R D) one D

@[simp] theorem subst_lead {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (lead R) = lead (Syn.subst σ R) := by simp [lead]
@[simp] theorem subst_fullDifference {m : ℕ} (σ : Fin n → PTm m) (P R D : PTm n) :
    Syn.subst σ (fullDifference P R D) = fullDifference (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ D) := by simp [fullDifference]
@[simp] theorem subst_companionY {m : ℕ} (σ : Fin n → PTm m) (P R D : PTm n) :
    Syn.subst σ (companionY P R D) = companionY (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ D) := by simp [companionY]

theorem companion_length (P R D : PTm n) : Γ ⊢[PRAAx] length (companionY P R D) ≐ D := segment_length _ _ _

theorem companion_lookup (P R D i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D)
    (hR : Γ ⊢[PRAAx] length R ≐ D)
    (hi : Γ ⊢[PRAAx] lt i D) : Γ ⊢[PRAAx]
    entry (companionY P R D) i ≐
      qsub (GaussianRationalLinearProduct.padded R D (succ i)) (qmul (lead R) (entry P (succ i))) := by
  have jbound : Γ ⊢[PRAAx] lt (succ i) (succ D) := (succ_monus_succ _ _).eqTrans hi
  have appendRange : Γ ⊢[PRAAx] le (succ i) (length R) := le_congr (.eqRefl _) hR.eqSymm hi
  have rightRange : Γ ⊢[PRAAx] lt (succ i) (length P) := by
    exact le_congr (.eqRefl _) hP.eqSymm jbound
  exact (segment_lookup _ _ _ _ hi).eqTrans
    ((entry_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] one+i ≐ succ i)).eqTrans
      ((sub_lookup _ _ _ _ jbound).eqTrans
        (qsub_congr ((append_lookup R (succ i) appendRange).eqTrans
          (GaussianRationalLinearProduct.padded_congr (.eqRefl _) hR (.eqRefl _)))
          (scaled_lookup _ _ _ rightRange))))

theorem full_difference_head (P R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) : Γ ⊢[PRAAx]
    entry (fullDifference P R D) zero ≐ qzero := by
  have shape : Γ ⊢[PRAAx] lt zero (length R) := le_congr (.eqRefl _) hR.eqSymm hD
  have shifted : Γ ⊢[PRAAx] entry (appendZero R) zero ≐ lead R :=
    (append_lookup R zero (zero_le _)).eqTrans (GaussianRationalLinearProduct.padded_inside _ _ _ shape)
  have pzero : Γ ⊢[PRAAx] lt zero (length P) :=
    le_congr (.eqRefl _) hP.eqSymm (zero_lt_succ _)
  exact (sub_lookup _ _ _ _ (zero_lt_succ D)).eqTrans
    ((qsub_congr shifted ((scaled_lookup P (lead R) zero pzero).eqTrans
      (qmul_congr (.eqRefl _) hMonic))).eqTrans (raw_unit_difference (lead R)))

theorem companion_canonical (P R D : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (companionY P R D) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (companionY P R D))) :: Γ.map Fm.shift
  have rawRange : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (companionY P R D))) := Prf.hyp0
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift D) :=
    lt_congr (.eqRefl _) (companion_length (Syn.shift P) (Syn.shift R) (Syn.shift D))
      (by simpa only [Syn.shift,subst_companionY] using rawRange)
  have subRange : Δ ⊢[PRAAx] lt (one+var 0) (succ (Syn.shift D)) :=
    le_congr (by ipra_ring : Δ ⊢[PRAAx] succ (succ (var 0)) ≐ succ (one+var 0)) (.eqRefl _)
      ((succ_monus_succ _ _).eqTrans range)
  have lookup : Δ ⊢[PRAAx] entry (companionY (Syn.shift P) (Syn.shift R) (Syn.shift D)) (var 0) ≐
      qsub (entry (appendZero (Syn.shift R)) (one+var 0))
        (entry (scaled (Syn.shift P) (lead (Syn.shift R))) (one+var 0)) :=
    (segment_lookup _ _ _ _ range).eqTrans (sub_lookup _ _ _ _ subRange)
  simpa only [Δ,Syn.shift,subst_companionY] using
    GaussianRationalHorner.canonical_congr lookup (qsub_canonical _ _)

theorem full_difference_evaluation (P R D z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D)
    (hR : Γ ⊢[PRAAx] length R ≐ D) : Γ ⊢[PRAAx]
    evaluate (fullDifference P R D) z ≐
      qsub (qmul (evaluate R z) z) (qmul (lead R) (evaluate P z)) :=
  (difference_evaluation _ _ _ z ((append_length R).eqTrans (congrSucc hR))
    ((scaled_length P (lead R)).eqTrans hP)).eqTrans
      (qsub_congr (append_evaluation R z) (evaluation_linearity P (lead R) z))

/-- The leading coefficient is removed only after its actual normalized
zero has been proved, including raw and zero leading coefficients of R. -/
theorem companion_difference_evaluation (P R D z : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) : Γ ⊢[PRAAx]
    evaluate (companionY P R D) z ≐
      qsub (qmul (evaluate R z) z) (qmul (lead R) (evaluate P z)) :=
  (zero_head_evaluation (fullDifference P R D) D z (sub_length _ _ _)
    (full_difference_head P R D hD hP hMonic hR)).eqSymm.eqTrans
      (full_difference_evaluation P R D z hP hR)

/-- Exact one-step monic reduction. No polynomial identity, coefficient
representation or desired remainder value is supplied as a premise. -/
theorem companion_evaluation (P R D z : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) : Γ ⊢[PRAAx]
    qmul z (evaluate R z) ≐
      qadd (qmul (evaluate P z) (lead R)) (evaluate (companionY P R D) z) := by
  have rhs : Γ ⊢[PRAAx] qadd (qmul (evaluate P z) (lead R)) (evaluate (companionY P R D) z) ≐
      qmul (evaluate R z) z :=
    (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
      (companion_difference_evaluation P R D z hD hP hMonic hR)).eqTrans
        (GaussianRationalLinearProduct.add_sub_right _ _ (GaussianRationalHorner.qmul_canonical _ _))
  exact (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans rhs.eqSymm

def companionF : PR 3 := PTm.toPR (companionY (var 0) (var 1) (var 2))
def run (P R D : PTm n) : PTm n := ap3 companionF P R D
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (P R D : PTm n) :
    Syn.subst σ (run P R D) = run (Syn.subst σ P) (Syn.subst σ R) (Syn.subst σ D) := by simp [run]

theorem program_at (P R D : PTm n) : Γ ⊢[PRAAx] run P R D ≐ companionY P R D := by
  simpa [run,companionF,ap3] using toPR_eq (Γ := Γ) (companionY (var 0) (var 1) (var 2) : PTm 3) ![P,R,D]
theorem returned_length (P R D : PTm n) : Γ ⊢[PRAAx] length (run P R D) ≐ D :=
  (congrFst (program_at P R D)).eqTrans (companion_length _ _ _)
theorem returned_canonical (P R D : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (run P R D) := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (canonicalCoefficients (var 0) : Fm PTm 1)
    ![companionY P R D] ![run P R D] (fun i => by fin_cases i; exact (program_at P R D).eqSymm)
    (by simpa using companion_canonical (Γ := Γ) P R D)
  simpa using p
theorem returned_lookup (P R D i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D)
    (hR : Γ ⊢[PRAAx] length R ≐ D) (hi : Γ ⊢[PRAAx] lt i D) : Γ ⊢[PRAAx]
    entry (run P R D) i ≐
      qsub (GaussianRationalLinearProduct.padded R D (succ i)) (qmul (lead R) (entry P (succ i))) :=
  (entry_congr (program_at P R D) (.eqRefl _)).eqTrans (companion_lookup P R D i hP hR hi)
theorem returned_evaluation (P R D z : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) : Γ ⊢[PRAAx]
    qmul z (evaluate R z) ≐ qadd (qmul (evaluate P z) (lead R)) (evaluate (run P R D) z) :=
  (companion_evaluation P R D z hD hP hMonic hR).eqTrans
    (qadd_congr (.eqRefl _)
      ((GaussianRationalHorner.evaluate_program_at (companionY P R D) z).eqSymm.eqTrans
        ((congrAp2 GaussianRationalHorner.evaluateF (program_at P R D).eqSymm (.eqRefl _)).eqTrans
          (GaussianRationalHorner.evaluate_program_at (run P R D) z))))

theorem actual_coefficient_difference_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ var 2 ⟶ length (var 1) ≐ var 2 ⟶
      evaluate (subCoefficients (var 0) (var 1) (var 2)) (var 3) ≐
        qsub (evaluate (var 0) (var 3)) (evaluate (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (difference_evaluation _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem raw_unit_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qsub (var 0) (qmul (var 0) qone) ≐ qzero) := closeUniv 1 (raw_unit_difference _)
theorem actual_zero_head_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qzero ⟶
      evaluate (var 0) (var 2) ≐ evaluate (segment (var 0) one (var 1)) (var 2)) :=
  closeUniv 3 (.impI (.impI (zero_head_evaluation _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_monic_companion_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ var 2 ⟶ lt (var 3) (var 2) ⟶
      entry (companionY (var 0) (var 1) (var 2)) (var 3) ≐
        qsub (GaussianRationalLinearProduct.padded (var 1) (var 2) (succ (var 3)))
          (qmul (lead (var 1)) (entry (var 0) (succ (var 3))))) :=
  closeUniv 4 (.impI (.impI (.impI (companion_lookup _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_monic_companion_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      length (var 1) ≐ var 2 ⟶ qmul (var 3) (evaluate (var 1) (var 3)) ≐
        qadd (qmul (evaluate (var 0) (var 3)) (lead (var 1)))
          (evaluate (companionY (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (companion_evaluation _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_monic_companion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ companionY (var 0) (var 1) (var 2)) ⋏
      ((length (run (var 0) (var 1) (var 2)) ≐ var 2) ⋏ canonicalCoefficients (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_length _ _ _) (returned_canonical _ _ _)))
theorem returned_monic_companion_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      length (var 1) ≐ var 2 ⟶ qmul (var 3) (evaluate (var 1) (var 3)) ≐
        qadd (qmul (evaluate (var 0) (var 3)) (lead (var 1)))
          (evaluate (run (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (returned_evaluation _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalMonicCompanion
