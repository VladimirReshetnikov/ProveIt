import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.SineComparisons.GaussianBinetArctangentSineUniform
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayPointwise
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedProductObservationBound

/-!
# Replacing the weighted arctangent by the scheduled sine rectangle

Move the frozen real exponential to the actual sine clock. Its norm
is at most two at that clock, so the bounded-angle uniform error can
then be multiplied by the specific frozen exponential observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 580000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSinePoint

open_ipra
open GaussianBinetArctangentSineUniform (clock cutoff count roundingCost)
open GaussianBinetSecondDecayPointwise (angle row fullDecay)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def cost (K T : PTm n) : PTm n := num 20+two*(K*T)

def point (q X Y D sign a b R T K H J : PTm n) : PTm n :=
  let p := clock q D R T K
  let N := count q D R T K
  qmul (GaussianBinetOscillatorySineRectangle.value p X Y D sign a b R T (cutoff q T K) N)
    (fullDecay (p+N) a b H J)

ipra_subst cost [two]

ipra_subst point [fullDecay, two]

theorem clock_later (q D R T K : PTm n) :
    Γ ⊢[PRAAx] le q (clock q D R T K+count q D R T K) := by
  let L := cutoff q T K
  let W := roundingCost q D R T K (D*L)
  have first : Γ ⊢[PRAAx] le q (GaussianFastValueCut.exponent W q) := le_add_right _ _
  exact le_trans (le_trans first (le_add_left _ _)) (le_add_right _ _)

theorem point_error (q X Y D sign a b R T K H J : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hb : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] le a (b*T)) (hk : Γ ⊢[PRAAx] le D (K*X)) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] distanceBounded (row q X Y D sign a b H J) (point q X Y D sign a b R T K H J)
      (cost K T) (unit q) := by
  let p := clock q D R T K
  let N := count q D R T K
  let l := p+N
  let c := two*(a*H)
  let e := b*J
  let f := angle q X Y D sign a b
  let g := GaussianBinetOscillatorySineRectangle.value p X Y D sign a b R T (cutoff q T K) N
  let v := fullDecay q a b H J
  let w := fullDecay l a b H J
  have hq := unit_positive (Γ := Γ) q
  have hl := unit_positive (Γ := Γ) l
  have he : Γ ⊢[PRAAx] le one e := positive_product _ _ hb hJ
  have ang : Γ ⊢[PRAAx] bounded f (K*T) one := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb hz.andE₁.andE₁.andE₁) (le_refl one) ?_
      (GaussianBinetArctangentQuadratureBound.name_bound q X Y D sign a b hz.andE₁ hb)
    ipra_le 𝔞(D)*sl ha+𝔞(T)*𝔞(b)*sl hk
  have decay : Γ ⊢[PRAAx] bounded w two one :=
    bounded_radius_mono _ _ _ _ _ hl (le_refl one) (by ipra_le sl hl)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound l c e he)
  let cv := GaussianEulerIntegrandName.decayPoint c e
  let d := decayData c e
  have input := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF cv (constant_regular cv)
  have regular : Γ ⊢[PRAAx] pointCN decayF d :=
    GaussianRadiusExponentialName.name_regular constantF (GaussianNameBounds.U constantF cv) cv input
  have ordered : Γ ⊢[PRAAx] le q l := clock_later q D R T K
  have later : Γ ⊢[PRAAx] distanceBounded w v two (unit q) :=
    GaussianNamedProductObservationBound.late_observation decayF d q l regular ordered
  have retime : Γ ⊢[PRAAx] distanceBounded v w two (unit q) :=
    distance_symmetric w v two (unit q) hq later
  have first := GaussianApproximateInverseDistance.multiply_distance f v w (K*T) two (unit q) hq ang retime
  have sine : Γ ⊢[PRAAx] distanceBounded f g (num 10) (unit q) :=
    GaussianBinetArctangentSineUniform.sample_error q X Y D sign a b R T K hz hb ha hk
  have tail : Γ ⊢[PRAAx] distanceBounded (qmul f w) (qmul g w) (two*num 10) (unit q) :=
    distance_congr (GaussianRationalPowerAlgebra.qmul_commutative w f) (GaussianRationalPowerAlgebra.qmul_commutative w g)
      (.eqRefl _) (.eqRefl _) (GaussianApproximateInverseDistance.multiply_distance w f g two _ _ hq decay sine)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hq first tail)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSinePoint
