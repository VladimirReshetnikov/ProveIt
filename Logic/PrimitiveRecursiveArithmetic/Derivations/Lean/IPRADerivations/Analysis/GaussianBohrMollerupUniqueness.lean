import IPRADerivations.Analysis.GaussianBohrMollerupComparison
import IPRADerivations.Analysis.GaussianBohrMollerupNativeNormalization
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# Effective Bohr–Mollerup uniqueness on positive rationals

For each requested precision the cutoff grows primitively recursively
with the dyadic denominator. Both directions of weak order follow
from the same comparison after exchanging the two fixed presentations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1850000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupPeriod (differenceF differenceData difference_regular)
open GaussianBohrMollerupPresentation (Presentation argument observe_value laws native)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaEulerRationalLogOrder (order_refl)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNameRingLaws (zeroF zero_at zero_fast)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedRealOrderTransport (transport)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero positive_product ofGaussian_canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_congr upper_of_radius upper_mono upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def cutoff (a p : PTm n) (b : PTm n) : PTm n := succ (a*(a+b)*unit p)

private theorem fraction_distance (r b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (fraction r b) qzero r b := by
  let q := fraction r b
  have hq := ofGaussian_canonical (Γ := Γ) (ComplexLogarithmRemainder.scale r ComplexLogarithmRemainder.oneCode) b hb
  have v := GaussianEulerDecayFactorBounds.fraction_is_radius_point r b hb
  have bound := bound_congr v.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded r b hb)
  exact bound_congr (GaussianRationalReconstruction.qsub_zero_right q hq).eqSymm (.eqRefl _) (.eqRefl _) bound

theorem same_precision_comparison (P Q : Presentation) (a b p y : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper
      (fstT (ap2 (productF (differenceF P Q)) p (productData (differenceF P Q) b (differenceData P Q a b))))
      (fstT (ap2 zeroF p y)) (one+two) (unit p) := by
  let j := cutoff a p b
  let D := productF (differenceF P Q)
  let x := productData (differenceF P Q) b (differenceData P Q a b)
  let u := unit p
  let c := a*(a+b)
  let k := fraction one u
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hb := unit_positive (Γ := Γ) p
  have hJ := positive_product (Γ := Γ) _ _ s.andE₂ hj
  have hlarge : Γ ⊢[PRAAx] le (u*c) (one*(b*j)) := by
    have large : Γ ⊢[PRAAx] le (c*u) j := le_succ_self _
    ipra_le sl large + 𝔞 j*sl s.andE₂
  have order₁ := GaussianBohrMollerupComparison.comparison P Q a b j hp hq s hj
  have order₂ := GaussianStirlingMultiplicativeBoundsLog.constant_order (fraction c (b*j)) k
    (GaussianStirlingMultiplicativeBoundsLog.fractions_order c (b*j) one u hJ hb hlarge)
  have joined := GaussianEulerPowerChartTimeOrder.order_trans D C C x (fraction c (b*j)) k order₁ order₂
  have approx := GaussianNamedNaturalScaleOrder.common_upper D C x k p joined
  have radius := scalar_coordinate_distance k (qzero : PTm n) one u hb (fraction_distance one u hb)
  have tail := upper_congr (congrFst (constant_at p k)).eqSymm (congrFst (zero_at p y)).eqSymm
    (.eqRefl _) (.eqRefl _) (upper_of_radius _ _ _ _ radius)
  have together := upper_triangle _ _ _ _ _ _ _ approx tail
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hb hb) together (le_of_eq_add (by dsimp [u]; ipra_ring) (d := ConciseIPRA.PTm.zero))

theorem order (P Q : Presentation) (a b : PTm n) (hp : Γ ⊢[PRAAx] laws P)
    (hq : Γ ⊢[PRAAx] laws Q) (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] realOrder P.nameF Q.nameF (argument P a b) (argument Q a b) := by
  let x := differenceData P Q a b
  let y := argument Q a b
  let D := differenceF P Q
  let S := productF D
  let X := productData D b x
  have rx := difference_regular P Q a b hp.andE₂.andE₁ hq.andE₂.andE₁ s
  have rX := GaussianNamedNaturalScaleOrder.regular D b x rx
  have small : Γ ⊢[PRAAx] realOrder S zeroF X y := by
    apply order_from_envelope _ _ _ _ (one+two) rX (zero_fast _)
    refine .allI ?_
    let Δ := Γ.map Fm.shift
    let A := Syn.shift a
    let B := Syn.shift b
    have hP : Δ ⊢[PRAAx] laws P := by simpa [Δ,Fm.shift] using hp.shift
    have hQ : Δ ⊢[PRAAx] laws Q := by simpa [Δ,Fm.shift] using hq.shift
    have hS : Δ ⊢[PRAAx] source A B := by simpa [Δ,Fm.shift,Syn.shift,A,B] using s.shift
    simpa [envelope,Syn.shift,Δ,D,S,X,x,A,B] using
      same_precision_comparison P Q A B (var 0) (Syn.shift y) hP hQ hS
  have scale := transport _ _ _ _ _ _ _ _ (GaussianNameEquivalence.cross_refl _ _ rX)
    (cross_symm _ _ _ _ (GaussianBohrMollerupZeroAlgebra.scaled_zero b y)) small
  have nonpositive := GaussianNamedNaturalScaleOrder.reflect_order D zeroF b x y s.andE₂ rx (zero_fast y) scale
  exact GaussianBohrMollerupZeroAlgebra.order_of_difference_nonpositive _ _ _ _
    (observe_value P a b hp.andE₂.andE₁ s).andE₁ (observe_value Q a b hq.andE₂.andE₁ s).andE₁ nonpositive

theorem uniqueness (P Q : Presentation) (a b : PTm n) (hp : Γ ⊢[PRAAx] laws P)
    (hq : Γ ⊢[PRAAx] laws Q) (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF Q.nameF (argument P a b) (argument Q a b) :=
  GaussianStirlingMultiplicativeBoundsStrictOrder.real_antisymmetry _ _ _ _
    (observe_value P a b hp.andE₂.andE₁ s).andE₂ (observe_value Q a b hq.andE₂.andE₁ s).andE₂
    (order P Q a b hp hq s) (order Q P a b hq hp s)

theorem actual_fixed_presentation_Bohr_Mollerup_uniqueness_closed (P : Presentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (laws P ⟶ source (var 0) (var 1) ⟶
        crossEquivalent P.nameF native.nameF (argument P (var 0) (var 1)) (argument native (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (uniqueness P native _ _ Prf.hyp0.wk
    GaussianBohrMollerupNativeNormalization.native_laws Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupUniqueness
