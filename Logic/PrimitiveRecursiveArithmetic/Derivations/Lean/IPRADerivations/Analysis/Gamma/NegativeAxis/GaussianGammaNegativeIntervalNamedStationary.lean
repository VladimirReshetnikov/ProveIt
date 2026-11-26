import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedGammaInverse
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDerivative
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaNegativeIntervalNamedDigammaRoot
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalWendelUniform

/-!
# Stationary offsets for the unscaled cofinal Gamma derivative

The actual named Gamma has an inverse formed from the negative
log-magnitude and the same interval sign. It cancels in the
named derivative product, so the unscaled cofinal derivative
vanishes exactly at the selected shifted digamma zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedStationary

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular)
open GaussianGammaNegativeIntervalNamedGammaInverse (inverseF inverseData inverse_regular left_inverse)
open GaussianGammaNegativeIntervalNamedInput (root_source)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_commutative multiply_associative
  multiply_one_left oneF one_fast zeroF zero_at zero_fast)
open GaussianNamedEulerUnitTime (source)
open GaussianRationalHorner (qzero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "ld" => GaussianGammaNegativeIntervalNamedLog.data
local notation "D" => GaussianGammaNegativeIntervalNamedDigamma.nameF
local notation "dd" => GaussianGammaNegativeIntervalNamedDigamma.data
local notation "TF" => GaussianGammaNegativeIntervalNamedDerivative.nameF
local notation "td" => GaussianGammaNegativeIntervalNamedDerivative.data

private theorem product_zero (F : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF F zeroF) zeroF (multiplyData F zeroF x zero) zero := by
  have zeroProduct : Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF F) zeroF
      (multiplyData constantF F qzero x) zero := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _
      (multiply_fast _ _ _ _ (constant_regular _) hf) (zero_fast _)
    refine .allI ?_
    simpa [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
      (GaussianGammaRationalWendelBoundary.zero_product_at (Γ := Γ.map Fm.shift) F (var 0)
        qzero (Syn.shift x) (.eqRefl _)).eqTrans (zero_at (var 0) zero).eqSymm
  have turn := multiply_commutative F zeroF x zero hf (zero_fast _)
  have move := multiply_cross zeroF constantF F F zero qzero x x (zero_fast _) (constant_regular _) hf hf
    (GaussianGammaRationalWendelUniform.zero_constant zero) (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ turn (cross_trans _ _ _ _ _ _ move zeroProduct)

theorem derivative_zero_of_digamma_zero (f : PR 2) (x W N : PTm n) (hs : Γ ⊢[PRAAx] source f x W)
    (hz : Γ ⊢[PRAAx] crossEquivalent (D f) zeroF (dd x W N) zero) :
    Γ ⊢[PRAAx] crossEquivalent (TF f) zeroF (td f x W N) zero := by
  have hG := actual_regular f x W N hs
  have hD := GaussianGammaNegativeIntervalNamedDigamma.name_regular f x W N hs
  have move := multiply_cross (actualF f) (actualF f) (D f) zeroF (actualData f x W N) (actualData f x W N)
    (dd x W N) zero hG hG hD (zero_fast _) (cross_refl _ _ hG) hz
  exact cross_trans _ _ _ _ _ _ move (product_zero _ _ hG)

private theorem cancel_zero (I G P : PR 2) (u v w a : PTm n) (hI : Γ ⊢[PRAAx] pointCN I u)
    (hG : Γ ⊢[PRAAx] pointCN G v) (hP : Γ ⊢[PRAAx] pointCN P w)
    (inv : Γ ⊢[PRAAx] crossEquivalent (multiplyF I G) oneF (multiplyData I G u v) a)
    (hz : Γ ⊢[PRAAx] crossEquivalent (multiplyF G P) zeroF (multiplyData G P v w) zero) :
    Γ ⊢[PRAAx] crossEquivalent P zeroF w zero := by
  let GP := multiplyF G P
  let gp := multiplyData G P v w
  let IG := multiplyF I G
  let ig := multiplyData I G u v
  have hIG := multiply_fast I G u v hI hG
  have hGP := multiply_fast G P v w hG hP
  have invAt := cross_trans IG oneF oneF ig a w inv (GaussianBoundedInverseApartness.ones_equivalent a w)
  have move := multiply_cross IG oneF P P ig w w w hIG (one_fast _) hP hP invAt (cross_refl _ _ hP)
  have drop : Γ ⊢[PRAAx] crossEquivalent (multiplyF IG P) P (multiplyData IG P ig w) w :=
    cross_trans _ _ _ _ _ _ move (multiply_one_left P w hP)
  have recover : Γ ⊢[PRAAx] crossEquivalent (multiplyF I GP) P (multiplyData I GP u gp) w :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative I G P u v w hI hG hP)) drop
  have kill := multiply_cross I I GP zeroF u u gp zero hI hI hGP (zero_fast _) (cross_refl _ _ hI) hz
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ recover)
    (cross_trans _ _ _ _ _ _ kill (product_zero I u hI))

theorem digamma_zero_of_derivative_zero (f : PR 2) (x W N : PTm n) (hs : Γ ⊢[PRAAx] source f x W)
    (hz : Γ ⊢[PRAAx] crossEquivalent (TF f) zeroF (td f x W N) zero) :
    Γ ⊢[PRAAx] crossEquivalent (D f) zeroF (dd x W N) zero :=
  cancel_zero (inverseF f) (actualF f) (D f) (inverseData f x W N) (actualData f x W N) (dd x W N)
    (ld x W N) (inverse_regular f x W N hs) (actual_regular f x W N hs)
    (GaussianGammaNegativeIntervalNamedDigamma.name_regular f x W N hs) (left_inverse f x W N hs) hz

theorem root_stationary (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (TF fractionLocationF) zeroF (td fractionLocationF N (mesh N) N) zero :=
  derivative_zero_of_digamma_zero fractionLocationF N (mesh N) N (root_source N)
    (cross_trans (D fractionLocationF) zeroF zeroF _ qzero zero (GaussianGammaNegativeIntervalNamedDigammaRoot.root_zero N)
      (GaussianGammaRationalWendelBoundary.zero_data_cross qzero zero))

theorem unique_stationary (f : PR 2) (x W N : PTm n) (hs : Γ ⊢[PRAAx] source f x W)
    (hz : Γ ⊢[PRAAx] crossEquivalent (TF f) zeroF (td f x W N) zero) :
    Γ ⊢[PRAAx] crossEquivalent fractionLocationF f N x :=
  cross_symm f fractionLocationF x N
    (GaussianGammaNegativeIntervalNamedDigammaRoot.unique_zero f x W N hs
      (cross_trans (D f) zeroF zeroF _ zero qzero (digamma_zero_of_derivative_zero f x W N hs hz)
        (GaussianGammaRationalWendelBoundary.zero_data_cross zero qzero)))

theorem actual_negative_interval_cofinal_Gamma_stationary_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent (TF fractionLocationF) zeroF (td fractionLocationF (var 0) (mesh (var 0)) (var 0)) zero) :=
  closeUniv 1 (root_stationary _)

theorem actual_negative_interval_cofinal_Gamma_stationary_unique_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ crossEquivalent (TF f) zeroF (td f (var 0) (var 1) (var 2)) zero ⟶
        crossEquivalent fractionLocationF f (var 2) (var 0)) :=
  closeUniv 3 (.impI (.impI (unique_stationary f (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedStationary
