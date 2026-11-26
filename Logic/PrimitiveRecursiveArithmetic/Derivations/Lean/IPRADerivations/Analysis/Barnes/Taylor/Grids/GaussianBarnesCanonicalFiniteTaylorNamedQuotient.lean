import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorGridIncrementRate
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalTaylorNamedQuotient

/-!
# Named fixed-cutoff Barnes factorial quotient

The evaluator uses the original neighboring fixed factorial names
at the same literal cutoff. The normalized grid estimate applies
after reading those names at one late endpoint clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorNamedQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_mono normSq normSq_scale scale)
open GaussianBarnesCanonicalFiniteTaylorGridIncrementRate (observationClock numerator)
open GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial (mixedGrid)
open GaussianBarnesCanonicalTaylorNamedQuotient (endpointClock scale_difference)
open GaussianBarnesCanonicalFiniteTaylorEvenGridLimit (quadraticClock)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1)
open GaussianNamedDifferenceQuotient (input inverse raw independent_readback scale_distance)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (bounded_iff distanceBounded qsub)
open GaussianRationalNaturalScale (natScale natScale_as_product natScale_product natScale_represents naturalPoint)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev nameF : PR 2 := GaussianNamedDifferenceQuotient.nameF F F

def data (z h R B r J e : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data F F (fd (add z h) (R+one) B r J e) (fd z (R+one) B r J e) h B

def leadingNumerator (R M e h : PTm n) : PTm n := numerator R M e h+norm1 h

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem quotient_input (z h R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx]
    input F F (fd (add z h) (R+one) B r J e) (fd z (R+one) B r J e) h B :=
  .andI (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular _ _ _ _ _ _ (widen _ _ _ hw) hJ)
    (.andI (GaussianBarnesCanonicalFixedTaylorDerivativeName.regular _ _ _ _ _ _ (widen _ _ _ hz) hJ)
      (.andI hz.andE₁ hn))

theorem regular (z h R B r J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx] pointCN nameF (data z h R B r J e) :=
  GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (quotient_input z h R B r J e hz hw hn hJ)

private theorem doubled_readback (p k x y h B : PTm n)
    (hi : Γ ⊢[PRAAx] input F F x y h B) : Γ ⊢[PRAAx] distanceBounded
    (natScale two (ap2 nameF p (GaussianNamedDifferenceQuotient.data F F x y h B)))
    (qmul (inverse h B) (qsub (natScale two (ap2 F k x)) (natScale two (ap2 F k y))))
    (two*GaussianNamedDifferenceQuotient.numerator B p k k) (GaussianNamedDifferenceQuotient.denominator p k k) := by
  let d := ap2 nameF p (GaussianNamedDifferenceQuotient.data F F x y h B)
  let r := raw F F k k x y h B
  let s : PTm n := naturalPoint two
  have dec := scale_distance s d r two _ _ (GaussianNamedDifferenceQuotient.denominator_positive p k k)
    (GaussianNamedNaturalScale.natural_point_bound two) (independent_readback F F p k k x y h B hi)
  have bind := (qmul_congr (.eqRefl (inverse h B)) (scale_difference (Γ := Γ) two (ap2 F k x) (ap2 F k y))).eqTrans
    (natScale_product two (inverse h B) (qsub (ap2 F k x) (ap2 F k y)))
  exact distance_congr (natScale_as_product two d).eqSymm
    ((natScale_as_product two r).eqSymm.eqTrans bind.eqSymm) (.eqRefl _) (.eqRefl _) dec

theorem rate (p z h R B r M J e t : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock z h R B r M e) t) : Γ ⊢[PRAAx]
    distanceBounded (natScale two (ap2 nameF p (data z h R B r J e))) (mixedGrid t z h R B r e)
      (leadingNumerator R M e h*unit p+two*B) (B*unit p) := by
  let k := endpointClock B
  let j := exponent (num 4*(B*B)) zero
  let P := unit p
  let K := unit k
  let H := norm1 h
  let x := fd (add z h) (R+one) B r J e
  let y := fd z (R+one) B r J e
  let q := natScale two (ap2 nameF p (data z h R B r J e))
  let w := qmul (inverse h B) (qsub (natScale two (ap2 F k x)) (natScale two (ap2 F k y)))
  let m := mixedGrid t z h R B r e
  let A := numerator R M e h
  have hB := hz.andE₁
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hd := positive_product B P hB (unit_positive p)
  have forward : Γ ⊢[PRAAx] le (quadraticClock B) k := le_add_right _ _
  have fit : Γ ⊢[PRAAx] le (num 4*(B*B)) K :=
    le_trans (le_congr ((congrMul (.eqRefl (num 4*(B*B))) (pw_zero two)).eqTrans (by ipra_ring))
      (.eqRefl _) (query_budget (num 4*(B*B)) zero)) (unit_monotone (le_add_left j (quadraticClock B)))
  have budget : Γ ⊢[PRAAx]
      le ((two*GaussianNamedDifferenceQuotient.numerator B p k k)*(B*P))
        ((H*P+two*B)*GaussianNamedDifferenceQuotient.denominator p k k) := by
    change Γ ⊢[PRAAx] le ((two*(K*K+B*P*(K+K)))*(B*P)) ((H*P+two*B)*(P*K*K))
    ipra_le 𝔞(P)*𝔞(P)*𝔞(K)*sl fit+𝔞(P)*𝔞(P)*𝔞(K)*𝔞(K)*sl hH
  have first : Γ ⊢[PRAAx] distanceBounded q w (H*P+two*B) (B*P) :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedDifferenceQuotient.denominator_positive p k k) hd budget
      (doubled_readback p k x y h B (quotient_input z h R B r J e hz hw hn hJ))
  have second : Γ ⊢[PRAAx] distanceBounded w m (A*P) (B*P) :=
    distance_radius_mono _ _ _ _ _ _ hB hd (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianBarnesCanonicalFiniteTaylorGridIncrementRate.rate z h R B r M J e t k k hz hw hn hsmall hdeg hJ ht forward forward)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [leadingNumerator,A,H,P]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd first second)

theorem actual_Barnes_finite_named_factorial_quotient_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let J := var 6
     let e := var 7
     let t := var 8
     let p := var 9
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h) ⋏ le ((e*stepDivisor R)*norm1 h) B) ⟶
       (previous M ≐ succ e ⋏ le e (previous J)) ⟶ le (observationClock z h R B r M e) t ⟶
       (pointCN nameF (data z h R B r J e) ⋏
         distanceBounded (natScale two (ap2 nameF p (data z h R B r J e))) (mixedGrid t z h R B r e)
           (leadingNumerator R M e h*unit p+two*B) (B*unit p))) :=
  closeUniv 10 (.impI (.impI (.impI (.andI
    (regular _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁ Prf.hyp1.andE₂)
    (rate _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁
      Prf.hyp1.wk.andE₂.andE₂.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorNamedQuotient
