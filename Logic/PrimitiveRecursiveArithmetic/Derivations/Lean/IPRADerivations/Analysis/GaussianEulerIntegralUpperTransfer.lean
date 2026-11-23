import IPRADerivations.Analysis.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Analysis.GaussianRationalSlackRemoval

/-!
# Uniform compact bounds transfer to the original Euler and Gamma names

The improper query p is literally the original compact query p+4 at
cutoff p. A bound C+2^-t on the original compact observations therefore
bounds that same improper query by C+2^-p. The original Euler/Gamma
identity and one actual Euclidean finite gap give the same requested
allowance for Gamma. This is a reusable conditional transfer; the
compact bound, in particular C=A+D_R, is supplied separately.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegralUpperTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerIntegralGammaIdentification (source original_Euler_integral_is_Gamma)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def compactObservation (t k z R B A : PTm n) : PTm n :=
  ap2 GaussianGammaEulerCompactQuadrature.nameF t (GaussianGammaEulerCompactQuadrature.data z R B k A)
def compactUpper (z R B A C : PTm n) : Fm PTm n := .all (.all
  (bounded (compactObservation (var 0) (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
    (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)))
    (Syn.shift (Syn.shift C)*unit (var 0)+one) (unit (var 0))))
def paperConstant (A R : PTm n) : PTm n := A+GaussianGammaIntegralCutoffs.tailCoefficient R
@[simp] theorem subst_compactObservation {m : ℕ} (σ : Fin n → PTm m) (t k z R B A : PTm n) :
    Syn.subst σ (compactObservation t k z R B A) = compactObservation (Syn.subst σ t) (Syn.subst σ k)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [compactObservation]
@[simp] theorem subst_compactUpper {m : ℕ} (σ : Fin n → PTm m) (z R B A C : PTm n) :
    (compactUpper z R B A C).subst σ = compactUpper (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ C) := by simp [compactUpper,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_paperConstant {m : ℕ} (σ : Fin n → PTm m) (A R : PTm n) :
    Syn.subst σ (paperConstant A R) = paperConstant (Syn.subst σ A) (Syn.subst σ R) := by
  simp [paperConstant,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem compact_at (t k z R B A C : PTm n) (h : Γ ⊢[PRAAx] compactUpper z R B A C) : Γ ⊢[PRAAx]
    bounded (compactObservation t k z R B A) (C*unit t+one) (unit t) := by
  have pair : Γ ⊢[PRAAx] .all
      (bounded (compactObservation (var 0) (Syn.shift k) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A))
        (Syn.shift C*unit (var 0)+one) (unit (var 0))) := by
    simpa only [compactUpper,Fm.subst_all,GaussianRationalMetric.subst_bounded,subst_compactObservation,
      PTm.subst_mul,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,
      Syn.up_zero,Syn.up_one,Syn.up_succ,Foundations.BoundedFormulas.subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var,one,PTm.subst_succ,PTm.subst_zero] using h.allE k
  simpa only [GaussianRationalMetric.subst_bounded,subst_compactObservation,PTm.subst_mul,PTm.subst_add,
    GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.inst_succ,
    Syn.subst_inst_shift,one,PTm.subst_succ,PTm.subst_zero] using pair.allE t


/-- Only one original compact observation is needed for this endpoint. -/
theorem improper_from_observation (p z R B A C : PTm n)
    (h : Γ ⊢[PRAAx] bounded (compactObservation (p+num 4) p z R B A)
      (C*unit (p+num 4)+one) (unit (p+num 4))) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
      (C*unit p+one) (unit p) := by
  have later := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right p (num 4))
  have original := GaussianRationalReciprocal.bound_congr
    (GaussianEulerImproperName.original_observation p z R B A).eqSymm (.eqRefl _) (.eqRefl _) h
  exact bounded_radius_mono _ _ _ _ _ (unit_positive _) (unit_positive p)
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (C*unit p*unit (p+num 4)) later)) original

theorem original_improper_upper (p z R B A C : PTm n)
    (h : Γ ⊢[PRAAx] compactUpper z R B A C) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
      (C*unit p+one) (unit p) :=
  improper_from_observation p z R B A C (compact_at (p+num 4) p z R B A C h)

theorem gamma_upper_budget (p t z R B A C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A) (h : Γ ⊢[PRAAx] compactUpper z R B A C) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (ap2 gammaF p (gammaData z R B A)) (C*unit p+one) (unit p) two t := by
  have identity := GaussianNameEquivalence.cross_symm _ _ _ _ (original_Euler_integral_is_Gamma z R B A hs)
  have distance := GaussianNameEquivalence.cross_at _ _ _ _ p t identity
  have den := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive t)
  have norm := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den (unit_positive t)
    distance (original_improper_upper t z R B A C h)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ den (unit_positive t))
    (positive_product _ _ (unit_positive p) (unit_positive t))
    (le_congr (by unfold unit; ipra_ring) (.eqRefl _) (le_refl _)) norm

theorem original_gamma_upper (p z R B A C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A) (h : Γ ⊢[PRAAx] compactUpper z R B A C) : Γ ⊢[PRAAx]
    bounded (ap2 gammaF p (gammaData z R B A)) (C*unit p+one) (unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two (unit_positive p)
    (gamma_upper_budget p (GaussianRationalSlackRemoval.precision (ap2 gammaF p (gammaData z R B A))
      (C*unit p+one) (unit p) two) z R B A C hs h)

theorem original_improper_A_D_R (p z R B A : PTm n)
    (h : Γ ⊢[PRAAx] compactUpper z R B A (paperConstant A R)) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
      (paperConstant A R*unit p+one) (unit p) := original_improper_upper p z R B A _ h

theorem original_gamma_A_D_R (p z R B A : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A) (h : Γ ⊢[PRAAx] compactUpper z R B A (paperConstant A R)) : Γ ⊢[PRAAx]
    bounded (ap2 gammaF p (gammaData z R B A)) (paperConstant A R*unit p+one) (unit p) :=
  original_gamma_upper p z R B A _ hs h

theorem original_uniform_compact_bound_transfers_to_improper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (compactUpper (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      bounded (ap2 GaussianEulerImproperName.nameF (var 0) (GaussianEulerImproperName.data (var 1) (var 2) (var 3) (var 4)))
        (var 5*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 6 (.impI (original_improper_upper _ _ _ _ _ _ Prf.hyp0))
theorem original_uniform_compact_bound_transfers_to_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ compactUpper (var 1) (var 2) (var 3) (var 4) (var 5)) ⟶
      bounded (ap2 gammaF (var 0) (gammaData (var 1) (var 2) (var 3) (var 4)))
        (var 5*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 6 (.impI (original_gamma_upper _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegralUpperTransfer
