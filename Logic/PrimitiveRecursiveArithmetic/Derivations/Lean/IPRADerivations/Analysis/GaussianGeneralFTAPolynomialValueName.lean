import IPRADerivations.Analysis.GaussianGeneralFTARootName

/-!
# The actual same-precision general polynomial evaluation names zero

The observation at t evaluates every original coefficient at precision t
at the actual constructed root observation alpha(t). Its comparison with
the proved scheduled residual follows from the genuine coefficient-name
condition and the actual point disk. A computed fixed precision shift
then gives a canonical fast Gaussian name whose observations all satisfy
the zero bounds. No value, coherence, root, zero-name or normalization
law is assumed. Completed-field extensionality is a separate interface.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAPolynomialValueName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (R K H L)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (alpha M J)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTARootName (beta)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput sample)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def S (a : PR 3) (N h x : PTm n) : PTm n := succ N*pw (R a N h x) N
def observation (a : PR 3) (N h x t : PTm n) : PTm n := evaluate (sample a N t x) (alpha a N h x t)
def shift (a : PR 3) (N h x : PTm n) : PTm n := GaussianGeneralFTAConstants.bl ((two*two)*S a N h x+one)
def exponent (a : PR 3) (N h x t : PTm n) : PTm n := t+shift a N h x
def value (a : PR 3) (N h x t : PTm n) : PTm n := observation a N h x (exponent a N h x t)

@[simp] theorem subst_S {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (S a N h x) = S a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [S]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (observation a N h x t) = observation a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by simp [observation]
@[simp] theorem subst_shift {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (shift a N h x) = shift a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [shift]
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (exponent a N h x t) = exponent a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by simp [exponent]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (value a N h x t) = value a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by simp [value]

theorem M_ge_index (a : PR 3) (N h x t : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le t (M a N h x t) :=
  le_trans (le_trans (le_add_right t two) (GaussianGeneralFTATrajectory.J_lower a N h x t hN))
    (le_add_right _ _)

theorem same_precision_gap (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    distanceBounded (observation a N h x t) (beta a N h x t) (two*S a N h x) (unit t) := by
  have actual := GaussianRationalAllCoefficientPerturbation.evaluation_bound _ _ _ N (R a N h x)
    (unit t+unit (M a N h x t)) (unit t*unit (M a N h x t))
    (GaussianGeneralPolynomialSamples.sample_length a N t x)
    (GaussianGeneralPolynomialSamples.sample_length a N (M a N h x t) x)
    (GaussianGeneralFTAConstants.R_positive a N h x) (positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianGeneralPolynomialSamples.all_coefficient_coherence a N t (M a N h x t) x (Prf.andE₁ hSource))
    (GaussianGeneralFTARootName.alpha_disk a N k h x t hSource)
  have cross := GaussianGeneralFTARootName.later_coherence_cross (Γ := Γ) (M a N h x t) t
    (M_ge_index a N h x t (GaussianGeneralFTARootName.source_degree a N k h x hSource))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
    (le_congr (by unfold S; ipra_ring) (by unfold S; ipra_ring) (mul_le_mul_right (S a N h x) cross)) actual

theorem unit_two_shift (t : PTm n) : Γ ⊢[PRAAx] unit (t+two) ≐ (two*two)*unit t := by
  have square : Γ ⊢[PRAAx] pw two two ≐ two*two :=
    (pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))
  exact ((pw_add two t two).eqTrans (congrMul (.eqRefl _) square)).eqTrans (mul_comm _ _)

theorem observation_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (observation a N h x t) ((two*two*two)*S a N h x+one) ((two*two)*unit t) := by
  have combined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (same_precision_gap a N k h x t hSource) (GaussianGeneralFTARootName.actual_beta_zero_bound a N k h x t hSource)
  have cross : Γ ⊢[PRAAx]
      ((two*S a N h x)*unit (t+two)+one*unit t)*((two*two)*unit t) ≐
        ((two*two*two)*S a N h x+one)*(unit t*unit (t+two)) := by
    refine withEq (unit_two_shift (Γ := Γ) t) fun e => ?_
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (positive_product _ _ (le_succ_self one) (le_succ_self one)) (unit_positive _))
    (le_congr (.eqRefl _) cross (le_refl _)) combined

theorem shift_budget (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    le ((two*two)*S a N h x+one) (unit (shift a N h x)) := GaussianGeneralFTAConstants.bit_budget _

theorem half_budget (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    le (two*((two*two*two)*S a N h x+one)) ((two*two)*unit (shift a N h x)) := by
  have small : Γ ⊢[PRAAx] le
      (two*((two*two*two)*S a N h x+one)) ((two*two)*((two*two)*S a N h x+one)) :=
    le_of_eq_add (d := two) (by ipra_ring)
  exact le_trans small (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (two*two) (shift_budget a N h x)))

theorem value_half_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (value a N h x t) one (two*unit t) := by
  have comparison := mul_le_mul_right (unit t) (half_budget (Γ := Γ) a N h x)
  have target : Γ ⊢[PRAAx] le
      (((two*two*two)*S a N h x+one)*(two*unit t)) (one*((two*two)*unit (exponent a N h x t))) := by
    refine le_congr (by ipra_ring) ?_ comparison
    refine withEq (pw_add two t (shift a N h x)) fun e => ?_
    unfold exponent unit
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (le_succ_self one) (le_succ_self one)) (unit_positive _))
    (positive_product _ _ (le_succ_self one) (unit_positive _)) target
    (observation_bound a N k h x (exponent a N h x t) hSource)

theorem value_zero_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (value a N h x t) one (unit t) := by
  have comparison : Γ ⊢[PRAAx] le (one*unit t) (one*(two*unit t)) :=
    le_congr (one_mul _).eqSymm (by ipra_ring) (le_add_right (unit t) (unit t))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (le_succ_self one) (unit_positive _)) (unit_positive _)
    comparison (value_half_bound a N k h x t hSource)

theorem value_regular_at (a : PR 3) (N k h x s t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    distanceBounded (value a N h x s) (value a N h x t) (unit s+unit t) (unit s*unit t) := by
  have bound := GaussianRationalReciprocal.bounded_difference _ _ _ _ _ _ (unit_positive _) (unit_positive _)
    (value_zero_bound a N k h x s hSource) (value_zero_bound a N k h x t hSource)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) bound

theorem value_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx] canonical (value a N h x t) :=
  GaussianRationalHorner.horner_canonical _ _ _

/-! The actual same-precision evaluation name, with all original numerical
parameters packed into its persistent input. -/

def nameData (N h x : PTm n) : PTm n := pairT N (pairT h x)
def nameBody (a : PR 3) : PTm 2 := value a (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def nameF (a : PR 3) : PR 2 := PTm.toPR (nameBody a)

@[simp] theorem subst_nameData {m : ℕ} (σ : Fin n → PTm m) (N h x : PTm n) :
    Syn.subst σ (nameData N h x) = nameData (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [nameData]

theorem name_body_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    inst2 (nameBody a) t (nameData N h x) ≐ value a N h x t := by
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (value a (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (nameData N h x),fstT (sndT (nameData N h x)),sndT (sndT (nameData N h x)),t])
    (σ' := ![N,h,x,t]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [nameBody,inst2,subst_value,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using fields

theorem name_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF a) t (nameData N h x) ≐ value a N h x t := by
  have program : Γ ⊢[PRAAx] ap2 (nameF a) t (nameData N h x) ≐ inst2 (nameBody a) t (nameData N h x) := by
    simpa [nameF,ap2,inst2] using toPR_eq (Γ := Γ) (nameBody a) ![t,nameData N h x]
  exact program.eqTrans (name_body_at a N h x t)

theorem name_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 (nameF a) t (nameData N h x)) :=
  GaussianRationalHorner.canonical_congr (name_at a N h x t) (value_canonical a N h x t)

theorem name_half_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF a) t (nameData N h x)) one (two*unit t) :=
  GaussianRationalReciprocal.bound_congr (name_at a N h x t).eqSymm (.eqRefl _) (.eqRefl _)
    (value_half_bound a N k h x t hSource)

theorem name_fast (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (nameF a) (nameData N h x) := by
  have source : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      sourceInput a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift k))
        (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift.shift
  refine .allI (.allI ?_)
  simpa only [Syn.shift,subst_nameData,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    GaussianRationalDistanceOrder.distance_congr
      (name_at a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
      (name_at a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (value_regular_at a _ _ _ _ (var 1) (var 0) source)

def nameZero (a : PR 3) (N h x : PTm n) : Fm PTm n :=
  .all (bounded (ap2 (nameF a) (var 0) (nameData (Syn.shift N) (Syn.shift h) (Syn.shift x))) one (unit (var 0)))
@[simp] theorem subst_nameZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    (nameZero a N h x).subst σ = nameZero a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp only [nameZero,Fm.subst_all,GaussianRationalMetric.subst_bounded,subst_ap2,subst_nameData,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,GaussianCoefficientNameBounds.subst_unit,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

theorem name_zero (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    nameZero a N h x := by
  have source : Γ.map Fm.shift ⊢[PRAAx] sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift
  refine .allI ?_
  exact GaussianRationalReciprocal.bound_congr (name_at a (Syn.shift N) (Syn.shift h) (Syn.shift x) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) (value_zero_bound a _ _ _ _ (var 0) source)

theorem actual_same_precision_evaluation_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (observation a (var 0) (var 2) (var 3) (var 4))
        ((two*two*two)*S a (var 0) (var 2) (var 3)+one) ((two*two)*unit (var 4))) :=
  closeUniv 5 (.impI (observation_bound _ _ _ _ _ _ Prf.hyp0))
theorem actual_normalized_evaluation_half_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (value a (var 0) (var 2) (var 3) (var 4)) one (two*unit (var 4))) :=
  closeUniv 5 (.impI (value_half_bound _ _ _ _ _ _ Prf.hyp0))
theorem actual_general_polynomial_zero_name_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (GaussianEuclideanDistanceName.pointCN (nameF a) (nameData (var 0) (var 2) (var 3)) ⋏
        nameZero a (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.andI (name_fast _ _ _ _ _ Prf.hyp0) (name_zero _ _ _ _ _ Prf.hyp0)))
theorem actual_general_polynomial_value_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (nameF a) (var 3) (nameData (var 0) (var 1) (var 2)) ≐ value a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (name_at _ _ _ _ _)
theorem actual_general_polynomial_value_canonical_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (canonical (ap2 (nameF a) (var 3) (nameData (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (name_canonical _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAPolynomialValueName
