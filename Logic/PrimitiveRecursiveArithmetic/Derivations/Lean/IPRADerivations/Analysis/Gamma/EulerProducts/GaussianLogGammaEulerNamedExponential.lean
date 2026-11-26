import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerNamed
import IPRADerivations.Analysis.Exponential.GaussianNamedRadiusExponentialFreeze
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerExponentialFrozen
import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNamedHalfPlanePoleFree

/-!
# The exponential of the named right-half-plane log-Gamma

A common late observation of the original input pays for both the
log-Gamma freeze and the original Gamma freeze. The rational identity
holds at that observation, and the named exponential reads the frozen
logarithm with its actual query clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianLogGammaEulerExponentialFrozen (logData)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_trans diagonal_at)
open GaussianNamedInverseRate (independentRate subst_independentRate diagonal_rate)
open GaussianRadiusExponentialName (inputPrecision)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianLogGammaEulerNamed.nameF
local notation "ld" => GaussianLogGammaEulerNamed.data
local notation "source" => GaussianLogGammaEulerNamed.source
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "disk" => GaussianNamedRadiusExponentialFreeze.radius

def nameF (f : PR 2) : PR 2 := Exp (L f)

def data (f : PR 2) (x M R : PTm n) : PTm n :=
  ed (disk (L f) (ld x M R)) (ld x M R)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x M R : PTm n) :
    Syn.subst σ (data f x M R) = data f (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ R) := by
  simp [data]

theorem name_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x M R) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianNamedRadiusExponentialFreeze.original_input _ _ (GaussianLogGammaEulerNamed.name_regular f x M R h))

private theorem rate_data_congr (f g : PR 2) (x y y' A D : PTm n)
    (e : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] independentRate f g x y' A D := by
  simpa only [subst_independentRate, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
    Prf.eqSubst1 (independentRate f g (Syn.shift x) (var 0) (Syn.shift A) (Syn.shift D)) e
      (by simpa only [subst_independentRate, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h)

theorem original_observation (f : PR 2) (p x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data f x M R)) (ap2 (G f) p (gd x M)) (num 6) (unit p) := by
  let map := GaussianLogGammaEulerNamed.rationalMap
  let X := ld x M R
  let W := disk (L f) X
  let t := inputPrecision W p
  let a := GaussianNamedRightHalfPlaneLift.clock map t M R
  let b := GaussianNamedGamma.clock f p x M
  let k := a+b
  let q := ap2 f k x
  let Y := logData q
  let Z := GaussianNamedGammaLateInput.encodedData f k x M
  have ha : Γ ⊢[PRAAx] le a k := le_add_right a b
  have hb : Γ ⊢[PRAAx] le b k := le_add_left b a
  have hLate : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f p k x M :=
    .andI h.andE₁ (.andI (le_trans (GaussianNamedGamma.clock_margin f p x M) hb)
      (le_trans (GaussianNamedGamma.clock_demand f p x M p (le_succ_self p)) hb))
  have cert := GaussianNamedRightHalfPlaneSigned.actual_late f x M k h.andE₁ hLate.andE₂.andE₁
  have hf := GaussianLogGammaEulerNamed.name_regular f x M R h
  have hy : Γ ⊢[PRAAx] pointCN F Y :=
    GaussianLogGammaEulerCofinal.canonical_regular _ _ _ _ cert.andE₁.andE₁
  have freeze : Γ ⊢[PRAAx] independentRate (L f) F X Y one (unit t) :=
    rate_data_congr (L f) F X _ Y one (unit t) (GaussianLogGammaEulerNamed.rational_data_at q)
      (GaussianLogGammaEulerNamed.late_rational_rate f t k x M R h ha)
  have firstInput := GaussianNamedRadiusExponentialFreeze.original_input (L f) X hf
  have frozenInput := GaussianNamedRadiusExponentialFreeze.partner_input (L f) F X Y t hf hy freeze
  have expFreeze := GaussianNamedRadiusExponentialFreeze.exponential_distance (L f) F W X Y p firstInput frozenInput freeze
  have gammaFreeze := GaussianLogGammaEulerExponentialFrozen.frozen_equivalent f p k x M W hLate frozenInput
  have rational := diagonal_at (Exp F) gammaF (ed W Y) Z p (cross_to_diagonal _ _ _ _ gammaFreeze)
  have hp := unit_positive (Γ := Γ) p
  have raw := diagonal_rate (G f) gammaF (gd x M) Z one (unit p) p hp
    (GaussianNamedGammaLateInput.original_independent_rate f p k x M hLate)
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 gammaF p Z) (ap2 (G f) p (gd x M)) (num 3) (unit p) :=
    distance_symmetric _ _ _ _ hp
      (distance_radius_mono _ _ _ _ (num 3) (unit p) (positive_product _ _ hp hp) hp
        (le_of_eq_add (d := zero) (by ipra_ring)) raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp expFreeze rational) last)

theorem gamma_equivalent (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (G f) (data f x M R) (gd x M) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (name_regular f x M R h) (GaussianNamedGamma.name_regular f x M h.andE₁) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by
    simpa only [Fm.shift, Syn.shift, sh, GaussianNamedRightHalfPlaneLift.subst_source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, sh, subst_data,
    GaussianNamedGamma.subst_data, PTm.subst_num] using original_observation f (var 0) (sh x) (sh M) (sh R) hs

theorem pole_free_equivalent (f : PR 2) (x M R S E : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hp : Γ ⊢[PRAAx] GaussianGammaNamedPoleFree.source f x S E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (GaussianGammaNamedPoleFree.nameF f) (data f x M R)
      (GaussianGammaNamedPoleFree.data x S E) :=
  cross_trans _ _ _ _ _ _ (gamma_equivalent f x M R h)
    (GaussianGammaNamedHalfPlanePoleFree.original_cross f x M S E h.andE₁ hp)

theorem actual_named_complex_log_Gamma_exponentiates_to_original_Gamma_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶
        crossEquivalent (nameF f) (G f) (data f (var 0) (var 1) (var 2)) (gd (var 0) (var 1))) :=
  closeUniv 3 (.impI (gamma_equivalent f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedExponential
