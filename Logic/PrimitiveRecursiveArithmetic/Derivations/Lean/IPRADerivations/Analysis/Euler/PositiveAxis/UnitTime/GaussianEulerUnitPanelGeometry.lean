import IPRADerivations.Analysis.Beta.Partitions.Alignment.GaussianBetaSharpFiniteBinding
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactAlignedThreeSplit
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianCompactModulusAlignedTime

/-!
# The unit panel in the original Euler cutoff interval

The middle panel is exactly the interval from one to two. The three
positive integer widths use the original cutoff denominator and a
common mesh step. The actual split error is the length factor times
four observation tolerances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitPanelGeometry

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top height eta_den_positive height_positive)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (quadrature)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def leftWidth (k A R : PTm n) : PTm n := monus (etaDen k A R) one
def rightWidth (k A R : PTm n) : PTm n := etaDen k A R*monus (top k A R) two

abbrev leftPanel (s k A R K z B : PTm n) : PTm n :=
  quadrature evaluatorF s (leftWidth k A R*K) one (leftWidth k A R) (etaDen k A R) (fixedData z B)
abbrev unitPanel (s k A R K z B : PTm n) : PTm n :=
  quadrature evaluatorF s (etaDen k A R*K) (etaDen k A R) (etaDen k A R) (etaDen k A R) (fixedData z B)
abbrev rightPanel (s k A R K z B : PTm n) : PTm n :=
  quadrature evaluatorF s (rightWidth k A R*K) (two*etaDen k A R) (rightWidth k A R)
    (etaDen k A R) (fixedData z B)
def pieces (s k A R K z B : PTm n) : PTm n :=
  qadd (qadd (leftPanel s k A R K z B) (unitPanel s k A R K z B)) (rightPanel s k A R K z B)

theorem left_endpoint (k A R : PTm n) : Γ ⊢[PRAAx] one+leftWidth k A R ≐ etaDen k A R :=
  (eq_add_of_le (eta_den_positive k A R)).eqSymm

theorem top_at_least_three (k A R : PTm n) : Γ ⊢[PRAAx] le (num 3) (top k A R) := by
  unfold top height
  ipra_le 2*𝔞(k)+2*𝔞(A)+2*𝔞(GaussianGammaIntegralCutoffs.tailCoefficient R)+17

theorem last_endpoint (k A R : PTm n) : Γ ⊢[PRAAx]
    two*etaDen k A R+rightWidth k A R ≐ etaDen k A R*top k A R := by
  have h2 := le_trans (le_succ_self two) (top_at_least_three (Γ := Γ) k A R)
  change Γ ⊢[PRAAx] two*etaDen k A R+etaDen k A R*monus (top k A R) two ≐ etaDen k A R*top k A R
  have e := natEq (eq_add_of_le h2)
  apply deriveNat
  ipra_simps
  rw [e]
  ring

theorem total_width (k A R : PTm n) : Γ ⊢[PRAAx]
    leftWidth k A R+etaDen k A R+rightWidth k A R ≐ width k A R := by
  ipra_lc natEq (left_endpoint (Γ := Γ) k A R)+natEq (last_endpoint (Γ := Γ) k A R)-
    natEq (exact_right_endpoint (Γ := Γ) k A R)

theorem widths_positive (k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    le one (leftWidth k A R) ⋏ le one (etaDen k A R) ⋏ le one (rightWidth k A R) := by
  have grow := GaussianExponentialReference.unit_monotone (positive_product _ _ hA (height_positive k A R))
  have h2 : Γ ⊢[PRAAx] le two (etaDen k A R) := by
    have bit : Γ ⊢[PRAAx] unit (one : PTm n) ≐ two :=
      (pw_succ two LeanProofs.ConciseIPRA.PTm.zero).eqTrans
        ((congrMul (pw_zero two) (.eqRefl _)).eqTrans (one_mul _))
    exact le_congr bit (.eqRefl _) grow
  have l : Γ ⊢[PRAAx] le one (leftWidth k A R) := by
    have eq := natEq (left_endpoint (Γ := Γ) k A R)
    apply le_of_eq_add (d := monus (etaDen k A R) two)
    have other := natEq (eq_add_of_le h2)
    apply deriveNat
    ipra_simps
    linear_combination eq+other
  have h3 := top_at_least_three (Γ := Γ) k A R
  have e := natEq (eq_add_of_le (le_trans (le_succ_self two) h3))
  have m : Γ ⊢[PRAAx] le one (monus (top k A R) two) := by
    apply le_of_eq_add (d := monus (top k A R) (num 3))
    have other := natEq (eq_add_of_le h3)
    apply deriveNat
    ipra_simps
    linear_combination other-e
  exact .andI l (.andI (eta_den_positive k A R)
    (positive_product _ _ (eta_den_positive k A R) m))

theorem actual_euler_unit_panel_split (s k A R K z B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (GaussianBetaSharpFiniteBinding.fullEuler s k A R K z B) (pieces s k A R K z B)
      (num 4*width k A R) (etaDen k A R*unit s) := by
  let E := etaDen k A R
  let L := leftWidth k A R
  let U := rightWidth k A R
  let W := width k A R
  let x := fixedData z B
  have w := total_width (Γ := Γ) k A R
  have ep : Γ ⊢[PRAAx] one+(L+E) ≐ two*E :=
    (show Γ ⊢[PRAAx] one+(L+E) ≐ (one+L)+E by ipra_ring).eqTrans
      ((congrAdd (left_endpoint k A R) (.eqRefl E)).eqTrans (by ipra_ring))
  have he := eta_den_positive (Γ := Γ) k A R
  have input := GaussianBetaRefinedFixedCompactComparison.original_interval_source z R B k A h
  have native := GaussianEulerCompactAdditivity.sampled_modulus z R B one W E (top k A R) input
  have align := GaussianCompactModulusAlignedTime.of_sampled_modulus evaluatorF one W E
    (GaussianEulerCompactModulus.lipschitz R E (top k A R)) x native
  have small : Γ ⊢[PRAAx] GaussianCompactAlignedTime.alignedSamples evaluatorF one (L+E+U) E x := by
    have direct := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
      (GaussianCompactAlignedTime.alignedSamples evaluatorF one (var 0) (var 1) (var 2) : Fm PTm 3)
      ![W,E,x] ![L+E+U,E,x]
      (fun i => by fin_cases i; exact w.eqSymm; exact .eqRefl _; exact .eqRefl _)
      (by simpa [one] using align)
    simpa [one] using direct
  have split := GaussianCompactAlignedThreeSplit.original_three_piece_split evaluatorF s one L E U E K x
    (.andI (le_refl one) (.andI he (.andI hK small)))
  have full := GaussianCompactAlignedSplit.quadrature_congr evaluatorF (.eqRefl s)
    (congrMul w (.eqRefl K)) (.eqRefl one) w (.eqRefl E) (.eqRefl x)
  have middle := GaussianCompactAlignedSplit.quadrature_congr (Γ := Γ) evaluatorF (.eqRefl s)
    (.eqRefl (E*K)) (left_endpoint k A R) (.eqRefl E) (.eqRefl E) (.eqRefl x)
  have right := GaussianCompactAlignedSplit.quadrature_congr (Γ := Γ) evaluatorF (.eqRefl s)
    (.eqRefl (U*K)) ep (.eqRefl U) (.eqRefl E) (.eqRefl x)
  exact GaussianRationalDistanceOrder.distance_congr full
    (GaussianRationalSyntheticDivision.qadd_congr
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) middle) right)
    (congrMul (.eqRefl (num 4)) w) (.eqRefl _) split

theorem actual_euler_unit_panel_split_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((GaussianGammaEulerCompactQuadrature.source (var 5) (var 3) (var 6) ⋏ le one (var 4)) ⟶
       distanceBounded
         (GaussianBetaSharpFiniteBinding.fullEuler (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
         (pieces (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
         (num 4*width (var 1) (var 2) (var 3)) (etaDen (var 1) (var 2) (var 3)*unit (var 0))) :=
  closeUniv 7 (.impI (actual_euler_unit_panel_split _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitPanelGeometry
