import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridComparison
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance

/-!
# Read the fixed factorial coefficient from the actual opposite grid

The coefficient one place below the leading term is the exact stored
coefficient at the difference order. Transfer its finite scalar
observation to the regular fixed-order name at an independent clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr length)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData finite_regular)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (target)
open GaussianBarnesCanonicalFiniteTaylorGrid (polynomial)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (scaledPolynomial)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (readbackGain)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalCoefficientScaling (scaled_lookup)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_as_product natScale_congr natScale_product naturalPoint)
open GaussianRationalSyntheticDivision (qmul_congr)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteF
local notation "gd" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteData
local notation "T" => GaussianBarnesCanonicalTaylorProductDerivativeName.finiteCoefficient
local notation "precision" => GaussianBarnesCanonicalExponentTaylorBallSchedule.precision

def prefactorClock (p z R B M e : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.precision (clock p z (R+one) B M e) (R+one)

def observationCost (q z R B H r M e : PTm n) : PTm n :=
  multiplyModulus finiteNameF constantF (finiteData z (R+one) B r)
    (T (precision q (R+one) (e*H)) z (R+one) B r M e)+one

def numerator (u s p q z R B H r M e : PTm n) : PTm n :=
  two*(rateNumerator (readbackGain z (R+one) B e) (unit p) u s+observationCost q z R B H r M e*unit p*unit u)

def denominator (u s p : PTm n) : PTm n := rateDenominator (unit p) u s

theorem next_lookup (q z R B H r M e : PTm n) (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) :
    Γ ⊢[PRAAx] entry (polynomial q z R B H r M e) one ≐ productCoefficient (precision q (R+one) (e*H)) z (R+one) B r M e := by
  have idx : Γ ⊢[PRAAx] monus (previous M) e ≐ one :=
    ((congrMonus hdeg (.eqRefl e)).eqTrans
      (congrMonus (by ipra_ring : Γ ⊢[PRAAx] succ e ≐ one+e) (.eqRefl e))).eqTrans (add_monus one e)
  change Γ ⊢[PRAAx] entry (polynomial q z R B H r M e) one ≐
    entry (polynomial q z R B H r M e) (monus (previous M) e)
  exact entry_congr (.eqRefl _) idx.eqSymm

theorem scaled_target (s q z R B H r M e : PTm n) (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) :
    Γ ⊢[PRAAx] target s q z R B H r M e ≐
      natScale two (qmul (ap2 finiteNameF s (finiteData z (R+one) B r))
        (T (precision q (R+one) (e*H)) z (R+one) B r M e)) := by
  let C := polynomial q z R B H r M e
  let a := ap2 finiteNameF s (finiteData z (R+one) B r)
  let b := T (precision q (R+one) (e*H)) z (R+one) B r M e
  have hLen : Γ ⊢[PRAAx] length C ≐ succ (succ e) :=
    (GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial_length q z (R+one) B (e*H) r M).eqTrans (congrSucc hdeg)
  have hIndex : Γ ⊢[PRAAx] lt one (length C) :=
    lt_congr (.eqRefl one) hLen.eqSymm (Common.lt_succ_of_le (zero_lt_succ e))
  have atOne := scaled_lookup C a one hIndex
  have read : Γ ⊢[PRAAx] natScale (fact e) (entry (scaledPolynomial s q z R B H r M e) one) ≐ qmul a b :=
    (natScale_congr (.eqRefl _) atOne).eqTrans ((natScale_product (fact e) a (entry C one)).eqSymm.eqTrans
      (qmul_congr (.eqRefl a) (natScale_congr (.eqRefl _) (next_lookup q z R B H r M e hdeg))))
  exact natScale_congr (.eqRefl two) read

theorem clock_ready (p q z R B H M e : PTm n) (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M e) q) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready p z (R+one) B M e (precision q (R+one) (e*H)) := by
  let a := clock p z (R+one) B M e
  have paid : Γ ⊢[PRAAx] le (prefactorGain (R+one)*unit a) (unit (prefactorClock p z R B M e)) := query_budget _ _
  have later : Γ ⊢[PRAAx] le q (precision q (R+one) (e*H)) := le_add_right _ _
  exact le_trans paid (unit_monotone (le_trans hq later))

theorem independent_readback (p q z R B H r M J e : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M e) q) :
    Γ ⊢[PRAAx] independentRate F G (fd z (R+one) B r J e)
      (gd (precision q (R+one) (e*H)) z (R+one) B r M e) (readbackGain z (R+one) B e) (unit p) := by
  let Q := precision q (R+one) (e*H)
  let x := fd z (R+one) B r M e
  let y := fd z (R+one) B r J e
  let v := gd Q z (R+one) B r M e
  have he : Γ ⊢[PRAAx] le e (previous M) := le_congr (.eqRefl e) hdeg.eqSymm (le_succ_self e)
  have base := GaussianBarnesCanonicalFixedTaylorDerivativeName.readback_rate p Q z (R+one) B r M e hz he
    (clock_ready p q z R B H M e hq)
  have cross := GaussianBarnesCanonicalTaylorDerivativeOrderInvariance.fixed_cross z (R+one) B r J M e hz hJ he
  have reg := GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finite_regular Q z (R+one) B r M e hz
  exact GaussianNamedRateTransport.transport F G F G x v y v _ _ (unit_positive p) base cross (cross_refl G v reg)

theorem readback (u s p q z R B H r M J e : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M e) q) :
    Γ ⊢[PRAAx] distanceBounded (target s q z R B H r M e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
      (numerator u s p q z R B H r M e) (denominator u s p) := by
  let Q := precision q (R+one) (e*H)
  let x := finiteData z (R+one) B r
  let b := T Q z (R+one) B r M e
  let v := gd Q z (R+one) B r M e
  let Y := ap2 F u (fd z (R+one) B r J e)
  let Z := qmul (ap2 finiteNameF s x) b
  let L := observationCost q z R B H r M e
  let D := denominator u s p
  let A := rateNumerator (readbackGain z (R+one) B e) (unit p) u s+L*unit p*unit u
  have hD : Γ ⊢[PRAAx] le one D := GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive p)
  have first := rate_at F G (fd z (R+one) B r J e) v (readbackGain z (R+one) B e) (unit p) u s
    (independent_readback p q z R B H r M J e hz hdeg hJ hq)
  have raw := GaussianNameRingLaws.multiply_sample_error finiteNameF constantF x b s
    (finite_regular z (R+one) B r hz) (constant_regular b)
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 G s v) Z L (unit s) :=
    distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at s b)) (.eqRefl _) (.eqRefl _) raw
  have fit : Γ ⊢[PRAAx] le (L*D) ((L*unit p*unit u)*unit s) :=
    le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [D,denominator,rateDenominator]; ipra_ring)
  have adjusted := distance_radius_mono _ _ _ _ _ _ (unit_positive s) hD fit second
  have distance : Γ ⊢[PRAAx] distanceBounded Z Y A D :=
    distance_symmetric _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD first adjusted)
  have double := GaussianNamedDifferenceQuotient.scale_distance (naturalPoint two) Z Y two A D hD
    (GaussianNamedNaturalScale.natural_point_bound two) distance
  exact distance_congr
    ((natScale_as_product two Z).eqSymm.eqTrans (scaled_target s q z R B H r M e hdeg).eqSymm)
    (natScale_as_product two Y).eqSymm (.eqRefl _) (.eqRefl _) double

theorem actual_Barnes_finite_Taylor_even_grid_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (let u := var 0
     let s := var 1
     let p := var 2
     let q := var 3
     let z := var 4
     let R := var 5
     let B := var 6
     let H := var 7
     let r := var 8
     let M := var 9
     let J := var 10
     let e := var 11
     (source z (R+one) B ⋏ (previous M ≐ succ e ⋏ (le e (previous J) ⋏ le (prefactorClock p z R B M e) q))) ⟶
       distanceBounded (target s q z R B H r M e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
         (numerator u s p q z R B H r M e) (denominator u s p)) :=
  closeUniv 12 (.impI (readback (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    (var 9) (var 10) (var 11) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridReadback
