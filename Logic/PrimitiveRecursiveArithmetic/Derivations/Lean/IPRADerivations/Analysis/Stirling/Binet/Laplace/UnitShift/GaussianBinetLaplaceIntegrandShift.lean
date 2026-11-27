import IPRADerivations.Analysis.Stirling.Binet.Laplace.UnitShift.GaussianBinetLaplaceExponentialShift
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Integrands.GaussianBinetLaplaceIntegrand
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripHorizon
import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.GaussianBinetKernelWeightedBridge

/-!
# Exact pointwise unit difference of the original Laplace integrand

The difference of the two original cofinal integrand names equals
the original damping factor multiplied by the actual weighted
Binet kernel, `exp(-zt) ((1-exp(-t)) K(t))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceIntegrandShift

open_ipra
open GaussianBinetKernelRows (inputData)
open GaussianBinetLaplaceExponentialShift (shift_multiply shifted_source)
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one_left oneF one_at one_fast)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianBinetLaplaceExponential.nameF
local notation "eData" => GaussianBinetLaplaceExponential.data
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "W" => GaussianBinetKernelWeightedBridge.nameF
local notation "wData" => GaussianBinetKernelWeightedBridge.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "difference" => GaussianNamedDifference.data

def differenceF : PR 2 := Diff cofinalF cofinalF
def differenceData (X Y D sign R T A B : PTm n) : PTm n :=
  difference (cofinalData X Y D sign R T A B) (cofinalData (X+D) Y D sign (R+one) T A B)
def differenceDataWithRadius (X Y D sign R S T A B : PTm n) : PTm n :=
  difference (cofinalData X Y D sign R T A B) (cofinalData (X+D) Y D sign S T A B)
def factoredF : PR 2 := multiplyF E W
def factoredData (X Y D sign R T A B : PTm n) : PTm n :=
  multiplyData E W (eData X Y D sign R T A B) (wData A B)

ipra_subst differenceData [one]

ipra_subst differenceDataWithRadius

ipra_subst factoredData

private theorem one_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x :=
  GaussianNameRingLaws.constant_one_cross x

private theorem difference_times (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (Diff f g) h) (Diff (multiplyF f h) (multiplyF g h))
      (multiplyData (Diff f g) h (difference x y) z) (difference (multiplyData f h x z) (multiplyData g h y z)) := by
  have swap := multiply_commutative (Diff f g) h (difference x y) z (GaussianNamedDifference.name_regular _ _ _ _ hf hg) hh
  have dist := GaussianNamedDifferenceAlgebra.distribute h f g z x y hh hf hg
  have fix := difference_proper (multiplyF h f) (multiplyF f h) (multiplyF h g) (multiplyF g h) _ _ _ _
    (multiply_fast _ _ _ _ hh hf) (multiply_fast _ _ _ _ hf hh) (multiply_fast _ _ _ _ hh hg) (multiply_fast _ _ _ _ hg hh)
    (multiply_commutative h f z x hh hf) (multiply_commutative h g z y hh hg)
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ dist fix)

theorem difference_regular (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] pointCN differenceF (differenceData X Y D sign R T A B) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _ h)
    (GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _
      (.andI (shifted_source X Y D sign R h.andE₁) h.andE₂))

theorem row_factor (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] crossEquivalent differenceF factoredF (differenceData X Y D sign R T A B)
      (factoredData X Y D sign R T A B) := by
  let x := eData X Y D sign R T A B
  let x' := eData (X+D) Y D sign (R+one) T A B
  let y := decayData A B
  let z := inputData A B
  let b := (qone : PTm n)
  let P := multiplyF constantF K
  let Q := multiplyF decayF K
  let p := multiplyData constantF K b z
  let q := multiplyData decayF K y z
  have hB := h.andE₂.andE₁
  have ht := h.andE₂.andE₂
  have hx := GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ hB ht
  have hv := shifted_source X Y D sign R h.andE₁
  have hx' := GaussianBinetLaplaceExponential.regular (X+D) Y D sign (R+one) T A B hv hB ht
  have hy := GaussianEulerDecayQuadraturePrecision.observation_regular (Γ := Γ) A B
  have hz := GaussianBinetKernelCofinal.regular A B hB
  have hb := constant_regular (Γ := Γ) b
  have hp : Γ ⊢[PRAAx] pointCN P p := multiply_fast _ _ _ _ hb hz
  have hq : Γ ⊢[PRAAx] pointCN Q q := multiply_fast _ _ _ _ hy hz
  have hEK := multiply_fast _ _ _ _ hx hz
  have hSK := multiply_fast _ _ _ _ hx' hz
  have identity := multiply_cross constantF oneF K K b z z z hb (one_fast z) hz hz (one_constant z) (cross_refl _ _ hz)
  have unit_identity := cross_trans _ _ _ _ _ _ identity (multiply_one_left K z hz)
  have insert := multiply_cross E E K P x x z p hx hx hz hp (cross_refl _ _ hx) (cross_symm _ _ _ _ unit_identity)
  have scale := shift_multiply X Y D sign R T A B h.andE₁ hB ht
  have move := multiply_cross E (multiplyF E decayF) K K x' (multiplyData E decayF x y) z z hx'
    (multiply_fast _ _ _ _ hx hy) hz hz scale (cross_refl _ _ hz)
  have group := cross_trans _ _ _ _ _ _ move (multiply_associative E decayF K x y z hx hy hz)
  have diff := difference_proper cofinalF (multiplyF E P) cofinalF (multiplyF E Q) _ _ _ _ hEK
    (multiply_fast _ _ _ _ hx hp) hSK (multiply_fast _ _ _ _ hx hq) insert group
  have extract := cross_symm _ _ _ _ (GaussianNamedDifferenceAlgebra.distribute E P Q x p q hx hp hq)
  have weight := cross_symm _ _ _ _ (difference_times constantF decayF K b y z hb hy hz)
  have attach := multiply_cross E E (Diff P Q) W x x (difference p q) (wData A B) hx hx
    (GaussianNamedDifference.name_regular _ _ _ _ hp hq)
    (multiply_fast _ _ _ _ (GaussianNamedDifference.name_regular _ _ _ _ hb hy) hz) (cross_refl _ _ hx) weight
  exact cross_trans _ _ _ _ _ _ diff (cross_trans _ _ _ _ _ _ extract attach)

theorem difference_regular_with_radius (X Y D sign R S T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B)
    (h' : Γ ⊢[PRAAx] input (X+D) Y D sign S T A B) :
    Γ ⊢[PRAAx] pointCN differenceF (differenceDataWithRadius X Y D sign R S T A B) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _ h)
    (GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _ h')

theorem row_factor_with_radius (X Y D sign R S T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B)
    (h' : Γ ⊢[PRAAx] input (X+D) Y D sign S T A B) :
    Γ ⊢[PRAAx] crossEquivalent differenceF factoredF (differenceDataWithRadius X Y D sign R S T A B)
      (factoredData X Y D sign R T A B) := by
  have hb : Γ ⊢[PRAAx] input (X+D) Y D sign (R+one) T A B :=
    .andI (shifted_source X Y D sign R h.andE₁) h.andE₂
  have base := GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _ h
  have before := GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _ h'
  have after := GaussianBinetLaplaceIntegrand.cofinal_regular _ _ _ _ _ _ _ _ hb
  have shifted := GaussianBinetLaplaceStripHorizon.integrand_coherence .cofinal (X+D) Y D sign S T (R+one) T
    ConciseIPRA.PTm.zero A B h' hb
  have replace := difference_proper cofinalF cofinalF cofinalF cofinalF _ _ _ _ base base before after
    (cross_refl _ _ base) shifted
  exact cross_trans _ _ _ _ _ _ replace (row_factor X Y D sign R T A B h)

theorem actual_Binet_Laplace_integrand_unit_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let T := var 5
     let A := var 6
     let B := var 7
     input X Y D sign R T A B ⟶ crossEquivalent differenceF factoredF
       (differenceData X Y D sign R T A B) (factoredData X Y D sign R T A B)) :=
  closeUniv 8 (.impI (row_factor _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_Binet_Laplace_integrand_unit_difference_with_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let S := var 5
     let T := var 6
     let A := var 7
     let B := var 8
     (input X Y D sign R T A B ⋏ input (X+D) Y D sign S T A B) ⟶
       crossEquivalent differenceF factoredF (differenceDataWithRadius X Y D sign R S T A B)
         (factoredData X Y D sign R T A B)) :=
  closeUniv 9 (.impI (row_factor_with_radius _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceIntegrandShift
