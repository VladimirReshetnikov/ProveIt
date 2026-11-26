import IPRADerivations.Analysis.Euler.ExponentialSubstitution.GaussianEulerExponentialLogPartition
import IPRADerivations.Analysis.Euler.ExponentialSubstitution.GaussianEulerExponentialEndpointEscape

/-!
# The actual logarithmic image endpoints exhaust the real line

The first and last rational grid times encode the original Euler
cutoffs exactly. Properness transports their logarithms to the unchanged
endpoint names. The finite cofinality bounds therefore hold at the
literal scaled grid encodings, with an explicit observation allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialCutoffPartition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (logF data sample)
open GaussianEulerExponentialEndpointEscape (minimumCutoff negativeInteger)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianRationalSyntheticBounds (natCode)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_cutoff_endpoint_names (k A R N : PTm n) (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent logF logF (data N (etaDen k A R*N)) (data one (etaDen k A R)) ⋏
    crossEquivalent logF logF (data ((one+width k A R)*N) (etaDen k A R*N)) (data (top k A R) one) := by
  let E := etaDen k A R
  let T := top k A R
  let W := width k A R
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have ht := GaussianGammaIntegralCutoffs.top_positive (Γ := Γ) k A R
  have hd := positive_product _ _ he hn
  have hright : Γ ⊢[PRAAx] le one ((one+W)*N) := positive_product _ _ (le_add_right one W) hn
  have rightEq : Γ ⊢[PRAAx] ((one+W)*N)*one ≐ (E*N)*T :=
    (congrMul (congrMul (exact_right_endpoint k A R) (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)
  exact .andI
    (GaussianPositiveRationalLogarithmProperness.original_logarithm_proper _ _ _ _ (.andI hn hd)
      (.andI (le_refl one) he) (by ipra_ring))
    (GaussianPositiveRationalLogarithmProperness.original_logarithm_proper _ _ _ _ (.andI hright hd)
      (.andI ht (le_refl one)) rightEq)

theorem original_cutoff_grid_escape (p t k A R N : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hn : Γ ⊢[PRAAx] le one N) (hk : Γ ⊢[PRAAx] le (minimumCutoff t) k) : Γ ⊢[PRAAx]
    upper (fstT (sample p N (etaDen k A R*N))) (negativeInteger t) (num 3) (unit p) ⋏
    upper (natCode t) (fstT (sample p ((one+width k A R)*N) (etaDen k A R*N))) (num 3) (unit p) := by
  let P := unit p
  let lo := fstT (sample p N (etaDen k A R*N))
  let hi := fstT (sample p ((one+width k A R)*N) (etaDen k A R*N))
  let a := fstT (sample p one (etaDen k A R))
  let b := fstT (sample p (top k A R) one)
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hp hp
  have same := original_cutoff_endpoint_names k A R N hn
  have left := cross_at _ _ _ _ p p same.andE₁
  have right := cross_at _ _ _ _ p p (cross_symm _ _ _ _ same.andE₂)
  have leftUpper : Γ ⊢[PRAAx] upper lo a (P+P) (P*P) :=
    upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hd left)
  have rightUpper : Γ ⊢[PRAAx] upper b hi (P+P) (P*P) :=
    upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hd right)
  have leftEnd := GaussianEulerExponentialEndpointEscape.original_left_endpoint p t k A R hA hk
  have rightEnd := GaussianEulerExponentialEndpointEscape.original_right_endpoint p t k A R hk
  have l := upper_triangle _ _ _ _ _ _ _ leftUpper leftEnd
  have r := upper_triangle _ _ _ _ _ _ _ rightEnd rightUpper
  exact .andI (upper_mono _ _ _ _ _ _ (positive_product _ _ hd hp) l (le_of_eq_add (d := zero) (by ipra_ring)))
    (upper_mono _ _ _ _ _ _ (positive_product _ _ hp hd) r (le_of_eq_add (d := zero) (by ipra_ring)))

theorem actual_logarithmic_cutoff_grid_escape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 3) ⋏ (le one (var 5) ⋏ le (minimumCutoff (var 1)) (var 2))) ⟶
      upper (fstT (sample (var 0) (var 5) (etaDen (var 2) (var 3) (var 4)*var 5))) (negativeInteger (var 1)) (num 3) (unit (var 0)) ⋏
      upper (natCode (var 1)) (fstT (sample (var 0) ((one+width (var 2) (var 3) (var 4))*var 5)
        (etaDen (var 2) (var 3) (var 4)*var 5))) (num 3) (unit (var 0))) :=
  closeUniv 6 (.impI (original_cutoff_grid_escape _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialCutoffPartition
