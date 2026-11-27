import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.NamedValues.GaussianGammaNegativeIntervalNamedGamma
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedGammaNativeDomain
import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaNamedPoleFreeEncoding
import IPRADerivations.Analysis.Gamma.Names.PoleFree.Regularity.GaussianGammaNamedPoleFreeFrozen

/-!
# Native Gamma at named negative real inputs

The log-absolute-value construction and the arbitrary-complex pole-free
evaluator share a late rational observation of the offset. The common
observation is passed as an exact argument to the original Gamma program,
with a disk and pole certificate independent of the observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular rateFactor)
open GaussianGammaNegativeIntervalNamedGammaNativeDomain (input radius shiftF shiftData shift_regular
  encodedNumerator encodedDenominator frozenData frozen_source frozen_shift_at frozen_cross)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (three)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => gammaF
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "gd" => GaussianGammaNegativeIntervalNative.data

theorem shift_source (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] GaussianGammaNamedPoleFree.source (shiftF f) (shiftData x N) (radius N) E := by
  refine .andI (shift_regular f x N hf.andE₁) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let J := Syn.shift N
  let H := Syn.shift E
  have hx : Δ ⊢[PRAAx] input f X H := by
    simpa only [input,Δ,X,H,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hf.shift
  have raw := GaussianGammaNamedPoleFreeEncoding.raw_source_of_fraction
    (ap2 (shiftF f) (var 0) (shiftData X J)) (encodedNumerator f (var 0) X J) (radius J)
    (encodedDenominator f (var 0) X) one H
    (frozen_source f (var 0) X H J hx) (frozen_shift_at f (var 0) X H J hx)
  simpa only [GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_shiftData,
    GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_radius,Δ,X,H,J,Syn.shift] using raw

theorem raw_frozen_cross (f : PR 2) (k x E N : PTm n) (hf : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] crossEquivalent G G
      (GaussianGammaNamedPoleFree.encodedData (shiftF f) k (shiftData x N) (radius N) E)
      (gd (sampleNumerator f k x) (sampleDenominator f k x) N) := by
  have base := GaussianGammaNamedPoleFreeEncoding.raw_gamma_cross
    (ap2 (shiftF f) k (shiftData x N)) (encodedNumerator f k x N) (radius N)
    (encodedDenominator f k x) E (frozen_source f k x E N hf) (frozen_shift_at f k x E N hf)
  exact cross_trans G G G _ (frozenData f k x E N) _ base (frozen_cross f k x E N hf)

theorem cofinal_rate (f : PR 2) (s x E N : PTm n) (hf : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] independentRate (actualF f) (P (shiftF f))
      (actualData f x E N) (pd (shiftData x N) (radius N) E) (rateFactor f x E N+one) (unit s) := by
  let F := actualF f
  let H := P (shiftF f)
  let u := actualData f x E N
  let v := pd (shiftData x N) (radius N) E
  let K := rateFactor f x E N
  let left := GaussianGammaNegativeIntervalNamedLog.clock s E N
  let right := GaussianGammaNamedPoleFree.clock s (radius N) E
  let k := left+right
  let z := gd (sampleNumerator f k x) (sampleDenominator f k x) N
  let w := GaussianGammaNamedPoleFree.encodedData (shiftF f) k (shiftData x N) (radius N) E
  have hs := shift_source f x E N hf
  have actual := GaussianGammaNegativeIntervalNamedGamma.actual_frozen_rate f s k x E N hf (le_add_right left right)
  have native := GaussianGammaNamedPoleFreeFrozen.original_frozen_rate
    (shiftF f) s k (shiftData x N) (radius N) E hs (le_add_left right left)
  have moved := GaussianNamedRateTransport.transport H G H G v w v z one (unit s)
    (unit_positive s) native
    (cross_refl _ _ (GaussianGammaNamedPoleFree.name_regular _ _ _ _ hs))
    (cross_symm G G w z (raw_frozen_cross f k x E N hf))
  have reversed := GaussianNamedRateComposition.symmetric H G v z one (unit s) (unit_positive s) moved
  exact GaussianNamedRateComposition.same_denominator F G H u z v K (unit s) one (unit_positive s) actual reversed

private theorem subst_actualData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (actualData f x E N) = actualData f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [actualData,GaussianGammaNegativeIntervalNamedGamma.signedData,
    GaussianGammaFiniteApproximantName.exponentialInputData]

private theorem subst_rateFactor {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    Syn.subst σ (rateFactor f x E N) = rateFactor f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [rateFactor,three,one,two]

private theorem observation_at (f : PR 2) (p x E N : PTm n) (hf : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (actualF f) p (actualData f x E N))
      (ap2 (P (shiftF f)) p (pd (shiftData x N) (radius N) E)) (rateFactor f x E N+three) (unit p) := by
  let K := rateFactor f x E N
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have obs := diagonal_rate (actualF f) (P (shiftF f)) _ _ (K+one) U p hU (cofinal_rate f p x E N hf)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := zero) (by unfold three; ipra_ring)) obs

theorem original_cross (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] input f x E) :
    Γ ⊢[PRAAx] crossEquivalent (actualF f) (P (shiftF f)) (actualData f x E N)
      (pd (shiftData x N) (radius N) E) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (rateFactor f x E N+three)
    (actual_regular f x E N hf)
    (GaussianGammaNamedPoleFree.name_regular _ _ _ _ (shift_source f x E N hf)) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hs : Δ ⊢[PRAAx] input f (sh x) (sh E) := by
    simpa only [input,Δ,sh,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hf.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_actualData,subst_rateFactor,
    GaussianGammaNamedPoleFree.subst_data,GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_shiftData,
    GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_radius,LeanProofs.IPRA.PTm.subst_add,three,one,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Δ,sh,Syn.shift] using
    observation_at f (var 0) (sh x) (sh E) (sh N) hs

theorem actual_named_negative_Gamma_pole_free_binding_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (input f (var 0) (var 1) ⟶ crossEquivalent (actualF f) (P (shiftF f))
        (actualData f (var 0) (var 1) (var 2)) (pd (shiftData (var 0) (var 2)) (radius (var 2)) (var 1))) :=
  closeUniv 3 (.impI (original_cross f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding
