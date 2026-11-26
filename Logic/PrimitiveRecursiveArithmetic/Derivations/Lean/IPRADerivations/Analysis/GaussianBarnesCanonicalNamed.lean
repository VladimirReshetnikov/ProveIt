import IPRADerivations.Analysis.GaussianBarnesCanonicalNamedDemand
import IPRADerivations.Analysis.GaussianBarnesCanonicalUniformContinuity
import IPRADerivations.Analysis.GaussianBarnesCanonicalProperness

/-!
# The original Barnes evaluator on regular Gaussian names

The actual rational Barnes modulus fixes each input observation.
The sampler is regular on every certified disk and agrees with the
existing rational evaluator on every name for an admitted rational.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalNamedDemand (Modulus source data frozenData)
open GaussianBarnesCanonicalUniformContinuity (inputClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "VD" => GaussianBarnesCanonicalValue.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

def inputClockF : PR 2 := PTm.toPR (inputClock (var 0) (var 1))

@[simp] private theorem subst_prefactorRadius {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius R) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R) := by
  let r := Syn.subst σ R
  let l : PTm n := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
  let c : PTm n := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
  let l' : PTm m := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
  let c' : PTm m := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
  change Syn.subst σ ((two*(R*l)+two)+(two*(R+(R*R)*(one+c))+two)) =
    (two*(r*l')+two)+(two*(r+(r*r)*(one+c'))+two)
  simp [r,l,c,l',c',one,two,GaussianStirlingConstant.nameData]

private theorem subst_inputClock {m : ℕ} (σ : Fin n → PTm m) (R p : PTm n) :
    Syn.subst σ (inputClock R p) = inputClock (Syn.subst σ R) (Syn.subst σ p) := by
  simp [inputClock,GaussianBarnesCanonicalUniformContinuity.gain,GaussianBarnesCanonicalUniformCutoff.cutoff,
    GaussianBarnesCanonicalUniformCutoff.gain,GaussianBarnesCanonicalDiskBound.prefixBound,
    GaussianBarnesCanonicalPrefactorLipschitz.gain,GaussianBarnesCanonicalPrefactorLipschitz.disk,
    GaussianBarnesCanonicalPrefactorLipschitz.exponentGain,GaussianBarnesCanonicalPrefactorLipschitz.linearGain,
    GaussianBarnesCanonicalPrefactorLipschitz.quadraticGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,GaussianBarnesCanonicalPrefactor.negativeHalf,
    one,two]

theorem input_clock_at (R p : PTm n) : Γ ⊢[PRAAx] ap2 inputClockF R p ≐ inputClock R p := by
  simpa only [inputClockF,ap2,subst_inputClock,Syn.subst_var,Matrix.cons_val] using
    toPR_eq (Γ := Γ) (inputClock (var 0) (var 1) : PTm 2) ![R,p]

def modulus : Modulus where
  inputClockF := inputClockF
  uniform_input z w R B D p hz hw h :=
    GaussianBarnesCanonicalUniformContinuity.uniform_input z w R B D p hz hw
      (distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (congrAp2 powF (input_clock_at R p) (.eqRefl two)) h)

abbrev nameF (f : PR 2) : PR 2 := GaussianBarnesCanonicalNamedDemand.nameF modulus f
abbrev clock (p R : PTm n) : PTm n := GaussianBarnesCanonicalNamedDemand.clock modulus p R

theorem sample_at (f : PR 2) (p x R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x R) ≐ ap2 V (succ p) (frozenData f (clock p R) x R) :=
  GaussianBarnesCanonicalNamedDemand.sample_at modulus f p x R

theorem name_regular (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x R) :=
  GaussianBarnesCanonicalNamedDemand.name_regular modulus f x R h

theorem proper (f g : PR 2) (x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R) (data y R) :=
  GaussianBarnesCanonicalNamedDemand.proper modulus f g x y R hf hg h

theorem constant_source (z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] source constantF (ofGaussian z B) R :=
  .andI (constant_regular _) (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound _ _
    (GaussianGammaEulerHead.fraction_disk z R B h.andE₁ h.andE₂))

private theorem constant_observations (p q z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF constantF) p (data (ofGaussian z B) R)) (ap2 V q (VD z R B))
      (unit p+unit q) (unit p*unit q) := by
  let x := ofGaussian z B
  let k := clock p R
  let y := ap2 constantF k x
  have admitted := GaussianBarnesCanonicalNamedDemand.native_source constantF k x R (constant_source z R B h)
  have same : Γ ⊢[PRAAx] ofGaussian (rawGaussian y) (rawDen y) ≐ x :=
    (GaussianNameArithmetic.recode_congr (constant_at k x)).eqTrans
      (GaussianExponentialReference.recode_fixed x (ofGaussian_canonical z B h.andE₁))
  have qNear := GaussianBarnesCanonicalProperness.comparison_at (rawGaussian y) z R R (rawDen y) B (succ p) q admitted h same
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_succ_self p)
  have widened := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive (succ p)) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (by ipra_le 𝔞(unit q*unit q)*sl grow) qNear
  exact distance_congr (sample_at constantF p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) widened

theorem constant_cross (z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF) V (data (ofGaussian z B) R) (VD z R B) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] disk (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,sh,Δ,GaussianBarnesCanonicalNamedDemand.subst_data,
    GaussianBarnesCanonicalValue.subst_data,GaussianRationalHorner.subst_ofGaussian] using
    constant_observations (var 1) (var 0) (sh z) (sh R) (sh B) hs

theorem bind (f : PR 2) (x z R B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hz : Γ ⊢[PRAAx] disk z R B)
    (he : Γ ⊢[PRAAx] crossEquivalent f constantF x (ofGaussian z B)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) V (data x R) (VD z R B) :=
  cross_trans (nameF f) (nameF constantF) V (data x R) (data (ofGaussian z B) R) (VD z R B)
    (proper f constantF x (ofGaussian z B) R hf (constant_source z R B hz) he) (constant_cross z R B hz)

theorem actual_Barnes_named_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (pointCN f (var 0) ⟶ pointCN (nameF f) (data (var 0) (GaussianNameBounds.U f (var 0)))) :=
  closeUniv 1 (.impI (name_regular f _ _ (GaussianBarnesCanonicalNamedDemand.source_of_regular f _ Prf.hyp0)))

theorem actual_Barnes_named_rational_binding_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 2) ⟶ disk (var 1) (var 2) (var 3) ⟶
        crossEquivalent f constantF (var 0) (ofGaussian (var 1) (var 3)) ⟶
        crossEquivalent (nameF f) V (data (var 0) (var 2)) (VD (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (bind f _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamed
