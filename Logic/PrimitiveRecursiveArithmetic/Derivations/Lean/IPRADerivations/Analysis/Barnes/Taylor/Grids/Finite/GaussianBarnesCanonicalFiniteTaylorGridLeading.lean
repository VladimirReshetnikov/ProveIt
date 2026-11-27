import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGrid
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorDerivativeName
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Read back the leading coefficient of the common Barnes grid polynomial

At its full degree the actual scheduled grid polynomial reads the same
coefficient as the fixed-cutoff sampler. The lower bound on the grid
precision is independent of the finite cutoff and the displacement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridLeading

open_ipra
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteTaylorGrid (polynomial)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (readbackGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyData multiplyModulus)
open GaussianNamedInverseRate (independentRate subst_independentRate rateNumerator rateDenominator)
open GaussianRationalCoefficientScaling (scaled scaled_lookup)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_as_product naturalPoint)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "precision" => GaussianBarnesCanonicalExponentTaylorBallSchedule.precision
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteF

def prefactorClock (p z R B M : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.precision (clock p z (R+one) B M (previous M)) (R+one)

def coefficient (q z R B H r M : PTm n) : PTm n :=
  natScale (fact (previous M)) (entry (polynomial q z R B H r M (previous M)) zero)

def data (q z R B H r M : PTm n) : PTm n :=
  multiplyData finiteNameF constantF (finiteData z (R+one) B r) (coefficient q z R B H r M)

theorem leading_lookup (q z R B H r M : PTm n) :
    Γ ⊢[PRAAx] entry (polynomial q z R B H r M (previous M)) zero ≐
      productCoefficient (precision q (R+one) (previous M*H)) z (R+one) B r M (previous M) := by
  change Γ ⊢[PRAAx] entry (polynomial q z R B H r M (previous M)) zero ≐
    entry (polynomial q z R B H r M (previous M)) (monus (previous M) (previous M))
  exact LeanProofs.IPRA.Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_self _).eqSymm

theorem clock_ready (p q z R B H M : PTm n) (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M) q) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready
      p z (R+one) B M (previous M) (precision q (R+one) (previous M*H)) := by
  let S := R+one
  let a := clock p z S B M (previous M)
  have payment : Γ ⊢[PRAAx] le (prefactorGain S*unit a) (unit (prefactorClock p z R B M)) :=
    query_budget _ _
  have fresh : Γ ⊢[PRAAx] le q (precision q S (previous M*H)) := le_add_right _ _
  exact le_trans payment (GaussianExponentialReference.unit_monotone (le_trans hq fresh))

theorem readback_rate (p q z R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M) q) :
    Γ ⊢[PRAAx] independentRate F G (fd z (R+one) B r M (previous M)) (data q z R B H r M)
      (readbackGain z (R+one) B (previous M)) (unit p) := by
  let E := previous M
  let S := R+one
  let x := fd z S B r M E
  let A := readbackGain z S B E
  let Q := precision q S (E*H)
  let y := GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteData Q z S B r M E
  have h : Γ ⊢[PRAAx] y ≐ data q z R B H r M := by
    ipra_congr (multiplyData finiteNameF constantF (var 0) (natScale (fact (var 1)) (var 2)) : PTm 3) with
      [.eqRefl (finiteData z S B r), .eqRefl E, (leading_lookup q z R B H r M).eqSymm]
      using [y,data,coefficient,GaussianBarnesCanonicalTaylorProductFiniteDerivativeRate.finiteData,
        GaussianBarnesCanonicalTaylorProductDerivativeName.finiteData,GaussianBarnesCanonicalTaylorProductDerivativeName.finiteCoefficient]
  have raw := GaussianBarnesCanonicalFixedTaylorDerivativeName.readback_rate p Q z S B r M E hz
    (le_refl E) (clock_ready p q z R B H M hq)
  have e := Prf.eqSubst1 (Γ := Γ) (independentRate F G (Syn.shift x) (var 0) (Syn.shift A) (Syn.shift (unit p))) h
    (by simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using raw)
  simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using e

theorem scaled_leading (u q z R B H r M : PTm n) :
    Γ ⊢[PRAAx] natScale (fact (previous M)) (entry (scaled (polynomial q z R B H r M (previous M)) u) zero) ≐
      qmul u (coefficient q z R B H r M) := by
  let P := polynomial q z R B H r M (previous M)
  let k := fact (previous M)
  let a := naturalPoint k
  let v := entry P zero
  have hP : Γ ⊢[PRAAx] length P ≐ succ (previous M) :=
    GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial_length q z (R+one) B (previous M*H) r M
  have h0 : Γ ⊢[PRAAx] lt zero (length P) :=
    Order.zero_lt_of_eq_succ hP
  have step := scaled_lookup P u zero h0
  exact (natScale_as_product k _).eqTrans ((qmul_congr (.eqRefl a) step).eqTrans
    ((GaussianReciprocalHorner.qmul_associative a u v).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative a u) (.eqRefl v)).eqTrans
        ((GaussianReciprocalHorner.qmul_associative u a v).eqTrans
          (qmul_congr (.eqRefl u) (natScale_as_product k v).eqSymm)))))

def observationCost (q z R B H r M : PTm n) : PTm n :=
  multiplyModulus finiteNameF constantF (finiteData z (R+one) B r) (coefficient q z R B H r M)+one

def observationNumerator (t s p q z R B H r M : PTm n) : PTm n :=
  rateNumerator (readbackGain z (R+one) B (previous M)) (unit p) t s+
    observationCost q z R B H r M*unit p*unit t

theorem rational_readback (t s p q z R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (hq : Γ ⊢[PRAAx] le (prefactorClock p z R B M) q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F t (fd z (R+one) B r M (previous M)))
      (qmul (ap2 finiteNameF s (finiteData z (R+one) B r)) (coefficient q z R B H r M))
      (observationNumerator t s p q z R B H r M) (rateDenominator (unit p) t s) := by
  let x := finiteData z (R+one) B r
  let v := coefficient q z R B H r M
  let b := data q z R B H r M
  let P := observationCost q z R B H r M
  let D := rateDenominator (unit p) t s
  have hd : Γ ⊢[PRAAx] le one D :=
    GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive p)
  have first := GaussianNamedInverseRate.rate_at F G (fd z (R+one) B r M (previous M)) b
    (readbackGain z (R+one) B (previous M)) (unit p) t s (readback_rate p q z R B H r M hz hq)
  have raw := GaussianNameRingLaws.multiply_sample_error finiteNameF constantF x v s
    (GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z (R+one) B r hz) (constant_regular v)
  have next : Γ ⊢[PRAAx] distanceBounded (ap2 G s b) (qmul (ap2 finiteNameF s x) v) P (unit s) :=
    distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at s v)) (.eqRefl _) (.eqRefl _) raw
  have fit : Γ ⊢[PRAAx] le (P*D) ((P*unit p*unit t)*unit s) :=
    le_of_eq_add (d := zero) (by dsimp only [D,rateDenominator]; ipra_ring)
  have adjusted := distance_radius_mono _ _ _ _ _ _ (unit_positive s) hd fit next
  exact distance_triangle_same _ _ _ _ _ _ hd first adjusted

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridLeading
