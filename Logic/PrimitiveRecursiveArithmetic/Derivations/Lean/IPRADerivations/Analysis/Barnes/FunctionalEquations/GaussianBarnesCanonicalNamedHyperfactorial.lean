import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalOrdinaryUpperGrowth
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerNamed
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Exponential.GaussianRadiusExponentialName

/-!
# The analytic hyperfactorial at regular named inputs

At a certified right-half-plane input, the original log-Gamma name
supplies the exponent (z−1) Log Γ(z). The original shifted Barnes name
supplies the denominator. Its certified reciprocal gives a regular
hyperfactorial name satisfying the cleared product identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameReciprocal (apart nameData name_fast product_one_left)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)
open GaussianBarnesCanonicalOrdinaryUpperGrowth (minusOne valueData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalOrdinaryUpperGrowth.nameF
local notation "L" => GaussianLogGammaEulerNamed.nameF
local notation "ld" => GaussianLogGammaEulerNamed.data
local notation "logSource" => GaussianLogGammaEulerNamed.source

def exponentF (f : PR 2) : PR 2 := multiplyF (addF f constantF) (L f)
def exponentData (f : PR 2) (x M R : PTm n) : PTm n :=
  multiplyData (addF f constantF) (L f) (addData x minusOne) (ld x M R)
def powerRadius (f : PR 2) (x M R : PTm n) : PTm n := GaussianNameBounds.U (exponentF f) (exponentData f x M R)
abbrev powerF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (exponentF f)
def powerData (f : PR 2) (x M R : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (powerRadius f x M R) (exponentData f x M R)

abbrev inverseF (f : PR 2) : PR 2 := GaussianNameReciprocal.nameF (G f)
def inverseData (x R h : PTm n) : PTm n := nameData h (valueData x R)
abbrev nameF (f : PR 2) : PR 2 := multiplyF (powerF f) (inverseF f)
def data (f : PR 2) (x M R h : PTm n) : PTm n :=
  multiplyData (powerF f) (inverseF f) (powerData f x M R) (inverseData x R h)
abbrev productF (f : PR 2) : PR 2 := multiplyF (nameF f) (G f)
def productData (f : PR 2) (x M R h : PTm n) : PTm n :=
  multiplyData (nameF f) (G f) (data f x M R h) (valueData x R)

def source (f : PR 2) (x M R h : PTm n) : Fm PTm n :=
  logSource f x M R ⋏ apart (G f) h (valueData x R)

theorem barnes_source (f : PR 2) (x M R : PTm n) (hs : Γ ⊢[PRAAx] logSource f x M R) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedDemand.source f x R :=
  GaussianBarnesCanonicalNamedFrozen.source_widen f x (GaussianNameBounds.U f x) R
    (GaussianBarnesCanonicalNamedDemand.source_of_regular f x hs.andE₁.andE₁) hs.andE₂

theorem barnes_regular (f : PR 2) (x M R : PTm n) (hs : Γ ⊢[PRAAx] logSource f x M R) :
    Γ ⊢[PRAAx] pointCN (G f) (valueData x R) :=
  GaussianBarnesCanonicalOrdinaryUpperGrowth.regular f x R (barnes_source f x M R hs)

theorem exponent_regular (f : PR 2) (x M R : PTm n) (hs : Γ ⊢[PRAAx] logSource f x M R) :
    Γ ⊢[PRAAx] pointCN (exponentF f) (exponentData f x M R) :=
  multiply_fast _ _ _ _ (add_fast f constantF x minusOne hs.andE₁.andE₁ (constant_regular minusOne))
    (GaussianLogGammaEulerNamed.name_regular f x M R hs)

theorem power_input (f : PR 2) (x M R : PTm n) (hs : Γ ⊢[PRAAx] logSource f x M R) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (exponentF f) (powerRadius f x M R) (exponentData f x M R) :=
  let h := exponent_regular f x M R hs
  .andI h (GaussianNameBounds.all_samples_bounded _ _ h)

theorem power_regular (f : PR 2) (x M R : PTm n) (hs : Γ ⊢[PRAAx] logSource f x M R) :
    Γ ⊢[PRAAx] pointCN (powerF f) (powerData f x M R) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (power_input f x M R hs)

theorem inverse_regular (f : PR 2) (x M R h : PTm n) (hs : Γ ⊢[PRAAx] source f x M R h) :
    Γ ⊢[PRAAx] pointCN (inverseF f) (inverseData x R h) :=
  name_fast _ _ _ (barnes_regular f x M R hs.andE₁) hs.andE₂

theorem regular (f : PR 2) (x M R h : PTm n) (hs : Γ ⊢[PRAAx] source f x M R h) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x M R h) :=
  multiply_fast _ _ _ _ (power_regular f x M R hs.andE₁) (inverse_regular f x M R h hs)

theorem cleared_relation (f : PR 2) (x M R h : PTm n) (hs : Γ ⊢[PRAAx] source f x M R h) :
    Γ ⊢[PRAAx] crossEquivalent (productF f) (powerF f) (productData f x M R h) (powerData f x M R) := by
  let u := powerData f x M R
  let v := inverseData x R h
  let w := valueData x R
  let y := multiplyData (inverseF f) (G f) v w
  have hu := power_regular f x M R hs.andE₁
  have hv := inverse_regular f x M R h hs
  have hw := barnes_regular f x M R hs.andE₁
  have hprod := multiply_fast (inverseF f) (G f) v w hv hw
  have assoc := multiply_associative (powerF f) (inverseF f) (G f) u v w hu hv hw
  have one := product_one_left (G f) h w hw hs.andE₂
  have collapse := GaussianGammaAdjacentCutoff.multiply_cross (powerF f) (powerF f)
    (multiplyF (inverseF f) (G f)) oneF u u y u hu hu hprod (one_fast u) (cross_refl _ _ hu)
    (cross_trans _ _ _ _ _ _ one (GaussianBoundedInverseApartness.ones_equivalent w u))
  exact cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ collapse (multiply_one (powerF f) u hu))

theorem actual_named_Barnes_hyperfactorial_cleared_relation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let M := var 1
       let R := var 2
       let h := var 3
       source f x M R h ⟶
         pointCN (nameF f) (data f x M R h) ⋏
           crossEquivalent (productF f) (powerF f) (productData f x M R h) (powerData f x M R)) :=
  closeUniv 4 (.impI (.andI (regular f _ _ _ _ Prf.hyp0) (cleared_relation f _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorial
