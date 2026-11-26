import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorGridIncrementRate
import IPRADerivations.Analysis.Names.GaussianNamedNaturalScale

/-!
# Named Barnes factorial difference quotient

The actual regular quotient uses the neighboring cofinal factorial
names and the literal rational step. A late common readback of the two
endpoint names absorbs their error into the linear step radius, while
the quotient itself can be read at a separately chosen clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorNamedQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_mono normSq normSq_scale scale)
open GaussianBarnesCanonicalCofinalTaylorEvenGridLimit (observationClock)
open GaussianBarnesCanonicalCofinalTaylorGridIncrementRate (mixedGrid numerator)
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

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev nameF : PR 2 := GaussianNamedDifferenceQuotient.nameF F F

def data (z h R B J e : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data F F (fd (add z h) (R+one) B J e) (fd z (R+one) B J e) h B

def endpointClock (B : PTm n) : PTm n := quadraticClock B+exponent (num 4*(B*B)) zero

def leadingNumerator (R M e h : PTm n) : PTm n := numerator R M e h+norm1 h

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem quotient_input (z h R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx]
    input F F (fd (add z h) (R+one) B J e) (fd z (R+one) B J e) h B :=
  .andI (GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ (widen _ _ _ hw) hJ)
    (.andI (GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ (widen _ _ _ hz) hJ)
      (.andI hz.andE₁ hn))

theorem regular (z h R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hJ : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx] pointCN nameF (data z h R B J e) :=
  GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (quotient_input z h R B J e hz hw hn hJ)

theorem scale_difference (k x y : PTm n) : Γ ⊢[PRAAx]
    qsub (natScale k x) (natScale k y) ≐ natScale k (qsub x y) :=
  (qsub_congr (natScale_as_product k x) (natScale_as_product k y)).eqTrans
    ((multiplication_difference (naturalPoint k) x y).eqTrans (natScale_as_product k (qsub x y)).eqSymm)

/-- A bound for doubled samples gives half the radius for the original
samples, with no assumption on their raw numerator representation. -/
theorem halve_distance (x y A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] distanceBounded (natScale two x) (natScale two y) A B) :
    Γ ⊢[PRAAx] distanceBounded x y A (two*B) := by
  let q := qsub x y
  let a := rawGaussian q
  let D := rawDen q
  have hD := raw_den_positive (Γ := Γ) q
  have wide := positive_product two B (le_succ_self one) hB
  have raw' := bound_congr (scale_difference two x y) (.eqRefl A) (.eqRefl B) hd
  have norm := (bounded_iff (natScale two q) (scale two a) D A B hD hB
    (natScale_represents two q a D hD (raw_represents q))).iffMp raw'
  exact (bounded_iff q a D A (two*B) hD wide (raw_represents q)).iffMpr
    (le_congr ((congrMul (.eqRefl (B*B)) (normSq_scale two a)).eqTrans (by ipra_ring :
      Γ ⊢[PRAAx] (B*B)*((two*two)*normSq a) ≐ ((two*B)*(two*B))*normSq a)) (.eqRefl _) norm)

/-- Combine the two doubled comparisons and keep the ordinary
independent-clock allowance after removing the doubling. -/
theorem compare_via_grid (x grid y A C B p u : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hx : Γ ⊢[PRAAx] distanceBounded (natScale two x) grid (A*unit p+two*B) (B*unit p))
    (hy : Γ ⊢[PRAAx] distanceBounded grid (natScale two y) (C*unit u+two*B) (B*unit u)) :
    Γ ⊢[PRAAx] distanceBounded x y (rateNumerator (A+C) B p u) (rateDenominator B p u) := by
  let P := unit p
  let U := unit u
  let Q := rateDenominator B p u
  let S := rateNumerator (A+C) B p u
  let D := (A+C)*P*U+two*B*(P+U)
  have hP := positive_product B P hB (unit_positive p)
  have hU := positive_product B U hB (unit_positive u)
  have hQ := GaussianNamedInverseRate.denominator_positive B p u hB
  have first : Γ ⊢[PRAAx] distanceBounded (natScale two x) grid ((A*P+two*B)*U) Q :=
    distance_radius_mono _ _ _ _ _ _ hP hQ
      (le_of_eq_add (d := zero) (by dsimp only [Q,rateDenominator,P,U]; ipra_ring)) hx
  have second : Γ ⊢[PRAAx] distanceBounded grid (natScale two y) ((C*U+two*B)*P) Q :=
    distance_radius_mono _ _ _ _ _ _ hU hQ
      (le_of_eq_add (d := zero) (by dsimp only [Q,rateDenominator,P,U]; ipra_ring)) hy
  have both : Γ ⊢[PRAAx] distanceBounded (natScale two x) (natScale two y) D Q :=
    distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [D]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hQ first second)
  have pay : Γ ⊢[PRAAx] le D (two*S) :=
    le_of_eq_add (d := (A+C)*P*U) (by dsimp only [D,S,rateNumerator,P,U]; ipra_ring)
  exact distance_radius_mono _ _ D (two*Q) S Q (positive_product two Q (le_succ_self one) hQ)
    hQ (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right Q pay)) (halve_distance x y D Q hQ both)

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

theorem rate (p z h R B M J e t : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock B e) t) : Γ ⊢[PRAAx]
    distanceBounded (natScale two (ap2 nameF p (data z h R B J e))) (mixedGrid t z h R B e)
      (leadingNumerator R M e h*unit p+two*B) (B*unit p) := by
  let k := endpointClock B
  let j := exponent (num 4*(B*B)) zero
  let P := unit p
  let K := unit k
  let H := norm1 h
  let x := fd (add z h) (R+one) B J e
  let y := fd z (R+one) B J e
  let q := natScale two (ap2 nameF p (data z h R B J e))
  let r := qmul (inverse h B) (qsub (natScale two (ap2 F k x)) (natScale two (ap2 F k y)))
  let m := mixedGrid t z h R B e
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
  have first : Γ ⊢[PRAAx] distanceBounded q r (H*P+two*B) (B*P) :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedDifferenceQuotient.denominator_positive p k k) hd budget
      (doubled_readback p k x y h B (quotient_input z h R B J e hz hw hn hJ))
  have second : Γ ⊢[PRAAx] distanceBounded r m (A*P) (B*P) :=
    distance_radius_mono _ _ _ _ _ _ hB hd (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianBarnesCanonicalCofinalTaylorGridIncrementRate.rate z h R B M J e t k k hz hw hn hsmall hdeg hJ ht forward forward)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [leadingNumerator,A,H,P]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd first second)

theorem actual_Barnes_named_factorial_quotient_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let J := var 5
     let e := var 6
     let t := var 7
     let p := var 8
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h) ⋏ le ((e*stepDivisor R)*norm1 h) B) ⟶
       (previous M ≐ succ e ⋏ le e (previous J)) ⟶ le (observationClock B e) t ⟶
       (pointCN nameF (data z h R B J e) ⋏
         distanceBounded (natScale two (ap2 nameF p (data z h R B J e))) (mixedGrid t z h R B e)
           (leadingNumerator R M e h*unit p+two*B) (B*unit p))) :=
  closeUniv 9 (.impI (.impI (.impI (.andI
    (regular _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁ Prf.hyp1.andE₂)
    (rate _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁
      Prf.hyp1.wk.andE₂.andE₂.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorNamedQuotient
