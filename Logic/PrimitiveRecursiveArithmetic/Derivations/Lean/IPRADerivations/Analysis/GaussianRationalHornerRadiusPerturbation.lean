import IPRADerivations.Analysis.GaussianRationalHornerPerturbation
import IPRADerivations.Analysis.GaussianRationalDistanceOrder

/-!
# Exact Horner coefficient perturbation at a rational query radius

The actual original query bound is U/V with U>=V>=1. The actual equal-leading
Horner prefixes have coefficient error A/B and exact bound
k U^(k-1) A / (V^(k-1) B). Quantifier-free induction handles the zero prefix
separately and retains every runtime degree and denominator. No integer
rounding, supplied scaling identity or supplied evaluation law is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHornerRadiusPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (horner evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation
  (coefficientErrors coefficient_error_at horner_difference_succ weighted_power)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (U A k : PTm n) : PTm n := k*pw U (pred k)*A
def denominator (V B k : PTm n) : PTm n := pw V (pred k)*B

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (U A k : PTm n) :
    Syn.subst σ (numerator U A k) = numerator (Syn.subst σ U) (Syn.subst σ A) (Syn.subst σ k) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (V B k : PTm n) :
    Syn.subst σ (denominator V B k) = denominator (Syn.subst σ V) (Syn.subst σ B) (Syn.subst σ k) := by simp [denominator]

theorem numerator_index_congr (U A : PTm n) {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) :
    Γ ⊢[PRAAx] numerator U A k ≐ numerator U A l :=
  congrMul (congrMul h (congrAp2 powF (congrPred h) (.eqRefl _))) (.eqRefl _)
theorem denominator_index_congr (V B : PTm n) {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) :
    Γ ⊢[PRAAx] denominator V B k ≐ denominator V B l :=
  congrMul (congrAp2 powF (congrPred h) (.eqRefl _)) (.eqRefl _)

theorem numerator_zero (U A : PTm n) : Γ ⊢[PRAAx] numerator U A zero ≐ zero := by unfold numerator; ipra_ring
theorem denominator_zero (V B : PTm n) : Γ ⊢[PRAAx] denominator V B zero ≐ B :=
  (congrMul ((congrAp2 powF pred_zero (.eqRefl _)).eqTrans (pw_zero V)) (.eqRefl _)).eqTrans (one_mul B)
theorem numerator_succ (U A k : PTm n) : Γ ⊢[PRAAx] numerator U A (succ k) ≐ succ k*pw U k*A :=
  congrMul (congrMul (.eqRefl _) (congrAp2 powF (pred_succ k) (.eqRefl _))) (.eqRefl _)
theorem denominator_succ (V B k : PTm n) : Γ ⊢[PRAAx] denominator V B (succ k) ≐ pw V k*B :=
  congrMul (congrAp2 powF (pred_succ k) (.eqRefl _)) (.eqRefl _)

theorem denominator_positive (V B k : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] le one (denominator V B k) :=
  positive_product _ _ (GaussianPolynomialPerturbation.power_positive _ _ hV) hB

/-- The exact rational successor budget. At k=0 the V factor cancels;
at positive k the only inequality is V^k<=U^k. -/
theorem step_comparison (U V A B k : PTm n) (hUV : Γ ⊢[PRAAx] le V U) : Γ ⊢[PRAAx]
    le ((numerator U A k*U*B+A*(denominator V B k*V))*(pw V k*B))
      ((succ k*pw U k*A)*((denominator V B k*V)*B)) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have h0 : (k ≐ zero) :: Γ ⊢[PRAAx] k ≐ zero := Prf.hyp0
    have nk := natEq ((numerator_index_congr U A h0).eqTrans (numerator_zero U A))
    have dk := natEq ((denominator_index_congr V B h0).eqTrans (denominator_zero V B))
    have uk := natEq ((congrAp2 powF h0 (.eqRefl U)).eqTrans (pw_zero U))
    have vk := natEq ((congrAp2 powF h0 (.eqRefl V)).eqTrans (pw_zero V))
    have ek := natEq h0
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat
    ipra_simps
    rw [nk,dk,uk,vk,ek]
    ring
  · let Δ := (k ≐ succ (pred k)) :: Γ
    have comparison : Δ ⊢[PRAAx] le V U := hUV.wk
    have weighted : Δ ⊢[PRAAx] numerator U A k*U ≐ k*pw U k*A := by
      have e := natEq (weighted_power (Γ := Δ) U k)
      apply deriveNat
      unfold numerator
      ipra_simps
      linear_combination Groth.ι (IPRA.Q.mk Δ A)*e
    have powerV : Δ ⊢[PRAAx] pw V k ≐ pw V (pred k)*V :=
      (congrAp2 powF Prf.hyp0 (.eqRefl V)).eqTrans (pw_succ V (pred k))
    have den : Δ ⊢[PRAAx] denominator V B k*V ≐ pw V k*B :=
      (by unfold denominator; ipra_ring : Δ ⊢[PRAAx] denominator V B k*V ≐ (pw V (pred k)*V)*B).eqTrans
        (congrMul powerV.eqSymm (.eqRefl _))
    have rawNum : Δ ⊢[PRAAx] numerator U A k*U*B+A*(denominator V B k*V) ≐
        (k*pw U k*A+pw V k*A)*B :=
      (congrAdd (congrMul weighted (.eqRefl _)) (congrMul (.eqRefl _) den)).eqTrans (by ipra_ring)
    have rawDen : Δ ⊢[PRAAx] (denominator V B k*V)*B ≐ pw V k*(B*B) :=
      (congrMul den (.eqRefl _)).eqTrans (by ipra_ring)
    have last := mul_le_mul_right A (pw_le_pw k comparison)
    have added := add_le_add₂ (le_refl (k*pw U k*A)) last
    have scaled := mul_le_mul_right (pw V k*(B*B)) added
    have left : Δ ⊢[PRAAx]
        (numerator U A k*U*B+A*(denominator V B k*V))*(pw V k*B) ≐
          (k*pw U k*A+pw V k*A)*(pw V k*(B*B)) :=
      (congrMul rawNum (.eqRefl _)).eqTrans (by ipra_ring)
    have right : Δ ⊢[PRAAx] (succ k*pw U k*A)*((denominator V B k*V)*B) ≐
        (k*pw U k*A+pw U k*A)*(pw V k*(B*B)) :=
      (congrMul (.eqRefl _) rawDen).eqTrans (by ipra_ring)
    exact le_congr left.eqSymm right.eqSymm scaled

def prefixLaw (C D z N U V A B k : PTm n) : Fm PTm n := le k N ⟶
  distanceBounded (horner C z (succ k)) (horner D z (succ k)) (numerator U A k) (denominator V B k)
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C D z N U V A B k : PTm n) :
    (prefixLaw C D z N U V A B k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ z)
      (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ V) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [prefixLaw]

theorem prefix_zero (C D z U V A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ zero)) (horner D z (succ zero)) (numerator U A zero) (denominator V B zero) :=
  GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (denominator_zero V B).eqSymm
    (GaussianRationalHornerPerturbation.prefix_zero C D z U A B hB hLead)

theorem prefix_step (C D z N U V A B k : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (hUV : Γ ⊢[PRAAx] le V U) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z U V)
    (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] distanceBounded (horner C z (succ k)) (horner D z (succ k)) (numerator U A k) (denominator V B k)) :
    Γ ⊢[PRAAx] distanceBounded (horner C z (succ (succ k))) (horner D z (succ (succ k)))
      (numerator U A (succ k)) (denominator V B (succ k)) := by
  have den := denominator_positive (Γ := Γ) V B k hV hB
  have product := bounded_product _ _ _ _ _ _ den hV ih hz
  have sum := bounded_sum _ _ _ _ _ _ (positive_product _ _ den hV) hB product (coefficient_error_at C D N A B k hErrors hk)
  have actual := bound_congr (horner_difference_succ C D z (succ k)).eqSymm (.eqRefl _) (.eqRefl _) sum
  have budget : Γ ⊢[PRAAx] le
      ((numerator U A k*U*B+A*(denominator V B k*V))*denominator V B (succ k))
      (numerator U A (succ k)*((denominator V B k*V)*B)) :=
    le_congr (congrMul (.eqRefl _) (denominator_succ V B k)).eqSymm
      (congrMul (numerator_succ U A k) (.eqRefl _)).eqSymm (step_comparison U V A B k hUV)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ den hV) hB) (denominator_positive V B (succ k) hV hB) budget actual

/-- Genuine quantifier-free induction on the runtime number of lower
coefficients. The original pair comparisons are instantiated only where used. -/
theorem prefix_bound (C D z N U V A B k : PTm n)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero)
    (hV : Γ ⊢[PRAAx] le one V) (hUV : Γ ⊢[PRAAx] le V U) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z U V)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ k)) (horner D z (succ k)) (numerator U A k) (denominator V B k) := by
  have lead : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) zero ≐ entry (Syn.shift D) zero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_entry,ConciseIPRA.PTm.subst_zero,Syn.shift] using hLead.shift
  have vpos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift V) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hV.shift
  have vu : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift V) (Syn.shift U) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hUV.shift
  have bpos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift
  have errors : Γ.map Fm.shift ⊢[PRAAx] coefficientErrors (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianRationalHornerPerturbation.subst_coefficientErrors,Syn.shift] using hErrors.shift
  have query : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift U) (Syn.shift V) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (Syn.shift N)
      (Syn.shift U) (Syn.shift V) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero C D z U V A B hB hLead).wk
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift D) (Syn.shift z) (Syn.shift N)
        (Syn.shift U) (Syn.shift V) (Syn.shift A) (Syn.shift B) (var 0)
      exact prefix_step _ _ _ _ _ _ _ _ _ vpos.wk.wk vu.wk.wk bpos.wk.wk errors.wk.wk query.wk.wk
        Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C D z N U V A B k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- The exact n (U/V)^(n-1) delta estimate concerns the actual original
rational query and coefficients. It includes n=0 and zero coefficient error. -/
theorem evaluation_bound (C D z N U V A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero)
    (hV : Γ ⊢[PRAAx] le one V) (hUV : Γ ⊢[PRAAx] le V U) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z U V) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate D z) (N*pw U (pred N)*A) (pw V (pred N)*B) := by
  have actual := prefix_bound C D z N U V A B N hLead hV hUV hB hErrors hz (le_refl _)
  exact GaussianRationalDistanceOrder.distance_congr
    (congrAp3 GaussianRationalHorner.hornerF hC.eqSymm (.eqRefl _) (.eqRefl _))
    (congrAp3 GaussianRationalHorner.hornerF hD.eqSymm (.eqRefl _) (.eqRefl _)) (.eqRefl _) (.eqRefl _) actual

theorem monic_evaluation_bound (C D z N U V A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hmC : Γ ⊢[PRAAx] entry C zero ≐ GaussianRationalSyntheticDivision.qone)
    (hmD : Γ ⊢[PRAAx] entry D zero ≐ GaussianRationalSyntheticDivision.qone)
    (hV : Γ ⊢[PRAAx] le one V) (hUV : Γ ⊢[PRAAx] le V U) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z U V) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate D z) (N*pw U (pred N)*A) (pw V (pred N)*B) :=
  evaluation_bound C D z N U V A B hC hD (hmC.eqTrans hmD.eqSymm) hV hUV hB hErrors hz

/-! Actual PR8 output includes the literal evaluation difference and its
exact computed numerator/denominator budget. -/
def output (C D z N U V A B : PTm n) : PTm n :=
  pairT (GaussianRationalMetric.qsub (evaluate C z) (evaluate D z))
    (pairT (numerator U A N) (denominator V B N))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (C D z N U V A B : PTm n) : PTm n := PTm.app outputF ![C,D,z,N,U,V,A,B]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C D z N U V A B : PTm n) :
    Syn.subst σ (output C D z N U V A B) = output (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ z)
      (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ V) (Syn.subst σ A) (Syn.subst σ B) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C D z N U V A B : PTm n) :
    Syn.subst σ (run C D z N U V A B) = run (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ z)
      (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ V) (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C D z N U V A B : PTm n) : Γ ⊢[PRAAx] run C D z N U V A B ≐ output C D z N U V A B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![C,D,z,N,U,V,A,B]
theorem output_value (C D z N U V A B : PTm n) : Γ ⊢[PRAAx]
    fstT (run C D z N U V A B) ≐ GaussianRationalMetric.qsub (evaluate C z) (evaluate D z) :=
  (congrFst (program_at C D z N U V A B)).eqTrans (fst_pair _ _)
theorem output_numerator (C D z N U V A B : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C D z N U V A B)) ≐ numerator U A N :=
  (congrFst ((congrSnd (program_at C D z N U V A B)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem output_denominator (C D z N U V A B : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run C D z N U V A B)) ≐ denominator V B N :=
  (congrSnd ((congrSnd (program_at C D z N U V A B)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem program_certificate (C D z N U V A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hLead : Γ ⊢[PRAAx] entry C zero ≐ entry D zero)
    (hV : Γ ⊢[PRAAx] le one V) (hUV : Γ ⊢[PRAAx] le V U) (hB : Γ ⊢[PRAAx] le one B)
    (hErrors : Γ ⊢[PRAAx] coefficientErrors C D N A B) (hz : Γ ⊢[PRAAx] bounded z U V) : Γ ⊢[PRAAx]
    le one (sndT (sndT (run C D z N U V A B))) ⋏
      bounded (fstT (run C D z N U V A B)) (fstT (sndT (run C D z N U V A B))) (sndT (sndT (run C D z N U V A B))) :=
  .andI (le_congr (.eqRefl _) (output_denominator C D z N U V A B).eqSymm (denominator_positive V B N hV hB))
    (bound_congr (output_value C D z N U V A B).eqSymm (output_numerator C D z N U V A B).eqSymm
      (output_denominator C D z N U V A B).eqSymm (evaluation_bound C D z N U V A B hC hD hLead hV hUV hB hErrors hz))

theorem rational_radius_horner_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 3) ⟶
      entry (var 0) zero ≐ entry (var 1) zero ⟶ le one (var 5) ⟶ le (var 5) (var 4) ⟶ le one (var 7) ⟶
        coefficientErrors (var 0) (var 1) (var 3) (var 6) (var 7) ⟶ bounded (var 2) (var 4) (var 5) ⟶
          distanceBounded (evaluate (var 0) (var 2)) (evaluate (var 1) (var 2))
            (var 3*pw (var 4) (pred (var 3))*var 6) (pw (var 5) (pred (var 3))*var 7)) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact evaluation_bound _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem rational_radius_horner_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (entry (var 0) zero ≐ entry (var 1) zero ⟶ le one (var 5) ⟶ le (var 5) (var 4) ⟶ le one (var 7) ⟶
      coefficientErrors (var 0) (var 1) (var 3) (var 6) (var 7) ⟶ bounded (var 2) (var 4) (var 5) ⟶ le (var 8) (var 3) ⟶
        distanceBounded (horner (var 0) (var 2) (succ (var 8))) (horner (var 1) (var 2) (succ (var 8)))
          (numerator (var 4) (var 6) (var 8)) (denominator (var 5) (var 7) (var 8))) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact prefix_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem rational_radius_horner_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := closeUniv 8 (program_at _ _ _ _ _ _ _ _)

theorem rational_radius_horner_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 3) ⟶
      entry (var 0) zero ≐ entry (var 1) zero ⟶ le one (var 5) ⟶ le (var 5) (var 4) ⟶ le one (var 7) ⟶
        coefficientErrors (var 0) (var 1) (var 3) (var 6) (var 7) ⟶ bounded (var 2) (var 4) (var 5) ⟶
          (le one (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))) ⋏
            bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
              (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))
              (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) := by
  apply closeUniv 8
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact program_certificate _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRationalHornerRadiusPerturbation
