import IPRADerivations.Analysis.GaussianGammaNamedRealCritical
import IPRADerivations.Analysis.GaussianGammaNamedPoleFreeQuotientProperness
import IPRADerivations.Analysis.GaussianNamedDyadicIncrement

/-!
# Extensionality of the original pole-free real Gamma derivative

Use one explicit dyadic increment small enough for both certificates.
The two original quotients agree at equivalent input names. Their
uniform rates therefore give the same derivative, irrespective of
the independently chosen disk and pole margins.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivativeProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaNamedPoleFree (source source_at)
open GaussianGammaNamedRealCritical (cost derivative_rate)
open GaussianGammaNamedRealDerivative (nameF data name_regular)
open GaussianGammaNamedRealDerivativeDemand (modulus modulus_positive margin_small)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "Q" => GaussianGammaNamedHalfPlanePoleFreeQuotient.nameF
local notation "qd" => GaussianGammaNamedHalfPlanePoleFreeQuotient.data

theorem comparison_rate (f g : PR 2) (p x y R E S B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hr : Γ ⊢[PRAAx] realSamples f x)
    (hg : Γ ⊢[PRAAx] source g y S B) (hs : Γ ⊢[PRAAx] realSamples g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] independentRate (nameF f) (nameF g) (data f x E) (data g y B)
      (cost f x E+cost g y B) (unit p) := by
  let A := modulus f p x E
  let C := modulus g p y B
  let a := GaussianFastValueCut.exponent (A+C) p
  let z := GaussianNamedDyadicIncrement.data a
  let F := Q f constantF
  let G := Q g constantF
  let u := qd f constantF x z R E (succ R) (two*E) a
  let v := qd g constantF y z S B (succ S) (two*B) a
  have hp := unit_positive (Γ := Γ) p
  have demand : Γ ⊢[PRAAx] le (A+C) (unit a) :=
    le_trans (le_of_eq_add (d := (A+C)*LeanProofs.IPRA.PTm.monus (unit p) one) (by
      have e := natEq (eq_add_of_le hp)
      apply deriveNat
      ipra_simps
      linear_combination (𝔞(A)+𝔞(C))*e)) (GaussianFastValueCut.query_budget _ _)
  have stepF := GaussianNamedDyadicIncrement.source a A (modulus_positive f p x E) (le_trans (le_add_right _ _) demand)
  have stepG := GaussianNamedDyadicIncrement.source a C (modulus_positive g p y B) (le_trans (le_add_left _ _) demand)
  have capF := margin_small f constantF p x z E (source_at f zero x R E hf).andE₂.andE₂.andE₁ stepF.andE₂.andE₂
  have capG := margin_small g constantF p y z B (source_at g zero y S B hg).andE₂.andE₂.andE₁ stepG.andE₂.andE₂
  have qeq := GaussianGammaNamedPoleFreeQuotientProperness.small_increment_proper f g constantF x y z R E S B a
    hf hg stepF.andE₂.andE₁ capF capG he
  have fder := derivative_rate f constantF p x z R E a (.andI (.andI hf hr) stepF)
  have gder := derivative_rate g constantF p y z S B a (.andI (.andI hg hs) stepG)
  have changeRight := GaussianNamedRateTransport.transport G (nameF g) F (nameF g) v (data g y B)
    u (data g y B) (cost g y B) (unit p) hp gder qeq (cross_refl _ _ (name_regular g y S B hg hs))
  exact same_denominator (nameF f) F (nameF g) (data f x E) u (data g y B) (cost f x E) (unit p) (cost g y B) hp
    (symmetric _ _ _ _ _ _ hp fder) changeRight

private theorem subst_derivative_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E : PTm n) :
    Syn.subst σ (data f x E) = data f (Syn.subst σ x) (Syn.subst σ E) := by
  have pos (u : ZT n) : Syn.subst σ u.pos = (u.subst σ).pos := rfl
  have neg (u : ZT n) : Syn.subst σ u.neg = (u.subst σ).neg := rfl
  simp [data,GaussianGammaNamedRealDerivative.flag,GaussianGammaNamedRealDerivative.sampleReal,
    pos,neg,LeanProofs.IPRA.Signum.sg,
    GaussianNamedPositiveDigamma.derivativeData,GaussianGammaNamedPoleFreeNegativeChartDerivative.derivativeData,
    GaussianGammaNegativeIntervalNamedDerivative.data,GaussianGammaNegativeIntervalNamedGamma.actualData,
    GaussianGammaNegativeIntervalNamedGamma.signedData,GaussianGammaFiniteApproximantName.exponentialInputData,one,two]

private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E : PTm n) :
    Syn.subst σ (cost f x E) = cost f (Syn.subst σ x) (Syn.subst σ E) := by
  simp [cost,GaussianGammaNamedPoleFreeNegativeChartDerivative.cost,
    GaussianGammaNegativeIntervalNamedIncrementDerivative.cost,GaussianGammaNegativeIntervalNamedIncrementDerivative.factorCost,
    GaussianGammaNegativeIntervalNamedIncrementDerivative.correctionCost,
    GaussianGammaNegativeIntervalNamedInverseFactorIncrement.gain,GaussianGammaNegativeIntervalNamedInverseDerivative.gain,
    GaussianGammaNegativeIntervalNamedTerminalDerivative.derivativeData,one,two]

private theorem diagonal_at (f g : PR 2) (p x y R E S B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hr : Γ ⊢[PRAAx] realSamples f x)
    (hg : Γ ⊢[PRAAx] source g y S B) (hs : Γ ⊢[PRAAx] realSamples g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data f x E)) (ap2 (nameF g) p (data g y B))
      ((cost f x E+cost g y B)+two) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have obs := diagonal_rate (nameF f) (nameF g) _ _ (cost f x E+cost g y B) (unit p) p hp
    (comparison_rate f g p x y R E S B hf hr hg hs he)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by unfold two; ipra_ring)) obs

theorem proper (f g : PR 2) (x y R E S B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hr : Γ ⊢[PRAAx] realSamples f x)
    (hg : Γ ⊢[PRAAx] source g y S B) (hs : Γ ⊢[PRAAx] realSamples g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x E) (data g y B) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ ((cost f x E+cost g y B)+two)
    (name_regular f x R E hf hr) (name_regular g y S B hg hs) (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have fSrc : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh E) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift
  have fReal : Δ ⊢[PRAAx] realSamples f (sh x) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hr.shift
  have gSrc : Δ ⊢[PRAAx] source g (sh y) (sh S) (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift
  have gReal : Δ ⊢[PRAAx] realSamples g (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hs.shift
  have eq : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,subst_derivative_data,subst_cost,
    PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal_at f g (var 0) (sh x) (sh y) (sh R) (sh E) (sh S) (sh B) fSrc fReal gSrc gReal eq

theorem actual_pole_free_real_Gamma_derivative_extensional_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 0) (var 2) (var 3) ⋏ realSamples f (var 0)) ⟶
        (source g (var 1) (var 4) (var 5) ⋏ realSamples g (var 1)) ⟶
        crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (nameF g) (data f (var 0) (var 3)) (data g (var 1) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (proper f g _ _ _ _ _ _ Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivativeProperness
