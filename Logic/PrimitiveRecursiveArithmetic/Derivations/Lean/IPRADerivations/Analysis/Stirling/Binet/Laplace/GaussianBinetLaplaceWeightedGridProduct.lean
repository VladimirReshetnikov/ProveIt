import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceWeightedGridReadback
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetWeightedExponentialBound
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetExponentialIntegralGrid
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedProductObservationBound

/-!
# Uniform comparison with a literal weighted rectangle row

Use the two original factor programs and bounds that are uniform in
the rational time tag.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedGridProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceIntegrand (cofinalF cofinalData input)
open GaussianBinetWeightedExponentialBound (radius observation_bound)
open GaussianBinetWeightedExponentialUniform (readBudget finite_readback)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRootApproximationWitness (pointBounds)
open GaussianLogGammaEulerHead (argument)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianBinetLaplaceExponential.nameF
local notation "ed" => GaussianBinetLaplaceExponential.data
local notation "WE" => GaussianBinetWeightedExponential.nameF
local notation "wed" => GaussianBinetWeightedExponential.data

def baseCost (T : PTm n) : PTm n := num 8+two*(two+radius T)
def rowBudget (q M T : PTm n) : PTm n := baseCost T*M+two*readBudget q M T

theorem exp_bound (q X Y D sign R T a b : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T a b) :
    Γ ⊢[PRAAx] bounded (ap2 E q (ed X Y D sign R T a b)) two one := by
  have hq := unit_positive (Γ := Γ) q
  have budget : Γ ⊢[PRAAx] le ((unit q+one)*one) (two*unit q) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (unit q)) hq)
  exact bounded_radius_mono _ _ _ _ _ hq (le_refl one) budget
    (GaussianBinetLaplaceExponential.unit_bound q X Y D sign R T a b h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)

theorem original_product_readback (q X Y D sign R T a b : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianBinetLaplaceWeightedShiftRow.nameF q
      (GaussianBinetLaplaceWeightedShiftRow.data X Y D sign R T a b))
      (qmul (ap2 E q (ed X Y D sign R T a b)) (ap2 WE q (wed a b))) (two*(two+radius T)) (unit q) := by
  let x := ed X Y D sign R T a b
  let y := wed a b
  have hb := h.andE₂.andE₁
  have ht := h.andE₂.andE₂
  have hE := GaussianBinetLaplaceExponential.regular X Y D sign R T a b h.andE₁ hb ht
  have hW := GaussianBinetKernelWeightedBridgeZero.weighted_regular a b hb
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hh : Δ ⊢[PRAAx] input (sh X) (sh Y) (sh D) (sh sign) (sh R) (sh T) (sh a) (sh b) := by
    simpa only [sh, Δ, Fm.shift, Syn.shift, GaussianBinetLaplaceIntegrand.subst_input] using h.shift
  have e : Γ ⊢[PRAAx] pointBounds E two x := by
    refine .allI ?_
    simpa only [x,pointBounds,Δ,sh,Syn.shift,GaussianBinetLaplaceExponential.subst_data,
      two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      exp_bound (var 0) (sh X) (sh Y) (sh D) (sh sign) (sh R) (sh T) (sh a) (sh b) hh
  have w : Γ ⊢[PRAAx] pointBounds WE (radius T) y := by
    refine .allI ?_
    simpa only [y,pointBounds,Δ,sh,Syn.shift,GaussianBinetWeightedExponential.subst_data,
      GaussianBinetWeightedExponentialBound.subst_radius] using
      observation_bound (var 0) (sh a) (sh b) (sh T) hh.andE₂.andE₁ hh.andE₂.andE₂
  exact GaussianNamedProductObservationBound.sample_error E WE x y q two (radius T) hE hW e w

theorem difference_to_row (q M X Y D sign R S T a b : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T a b) (hs : Γ ⊢[PRAAx] input (X+D) Y D sign S T a b)
    (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (ap2 cofinalF q (cofinalData X Y D sign R T a b)) (ap2 cofinalF q (cofinalData (X+D) Y D sign S T a b)))
      (qmul (GaussianBinetExponentialIntegralGrid.row q (qnegative (argument X Y D sign)) (R*T) a b)
        (GaussianBinetWeightedExponentialGrid.value q M a b)) (rowBudget q M T) (M*unit q) := by
  let x := ap2 E q (ed X Y D sign R T a b)
  let y := ap2 WE q (wed a b)
  let w := GaussianBinetWeightedExponentialGrid.value q M a b
  let U := unit q
  let Q := M*U
  have hU := unit_positive (Γ := Γ) q
  have hQ := positive_product M U hM hU
  have first := GaussianBinetLaplaceWeightedGridReadback.sample_difference q X Y D sign R S T a b h hs
  have prod := original_product_readback q X Y D sign R T a b h
  have pair := distance_triangle_same _ _ _ _ _ _ hU first prod
  have start := distance_radius_mono _ _ _ _ (baseCost T*M) Q hU hQ
    (le_of_eq_add (d := zero) (by dsimp only [Q,U,baseCost]; ipra_ring)) pair
  have near := finite_readback q M a b T hM h.andE₂.andE₁ h.andE₂.andE₂
  have last := GaussianNameRingLaws.product_right_error x y w _ Q (radius T) two hQ near
    (observation_bound q a b T h.andE₂.andE₁ h.andE₂.andE₂) (exp_bound q X Y D sign R T a b h)
  exact distance_triangle_same _ _ _ _ _ _ hQ start last

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedGridProduct
