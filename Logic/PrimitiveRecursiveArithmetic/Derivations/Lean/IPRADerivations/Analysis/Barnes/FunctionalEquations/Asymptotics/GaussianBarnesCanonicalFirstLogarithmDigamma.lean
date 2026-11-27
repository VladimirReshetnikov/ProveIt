import IPRADerivations.Analysis.Barnes.FunctionalEquations.Asymptotics.GaussianBarnesCanonicalFirstLogarithmDigammaSeries
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Asymptotics.GaussianBarnesCanonicalFirstLogarithmConstant
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# The original positive Barnes logarithmic derivative and digamma

Let `x=(A-B)/B`. The original first logarithmic derivative at the Barnes
argument `A/B` agrees with `(log(2π)-1)/2 + x*(ψ(A/B)-1)`. Its fixed
constant is also expressed directly by the original Stirling constant
minus one half.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmDigamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFirstLogarithmDigammaPrefix (coordinate)
open GaussianBarnesCanonicalFirstLogarithmDigammaSeries
  (unscaledF unscaledData unscaled_regular scaledF scaledData scaled_regular series_cross)
open GaussianBarnesCanonicalPositiveFirstLogarithm (prefactorData prefactor_regular seriesData seriesF series_regular)
open GaussianBarnesCanonicalPositiveSecondLogarithm (coefficientF coefficientData coefficient_regular)
open GaussianBarnesCanonicalPrefactor
  (quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf twicePoint add_entries scale_entries)
open GaussianBarnesCanonicalPrefactorInverse (exponentF)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular gammaF gamma_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast zeroF zero_fast negativeF negativeData negative_fast add_negative
  add_commutative add_associative distributive)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (qzero qadd qadd_canonical ofGaussian_canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_zero_right)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right qmul_one_right)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => exponentF
local notation "D" => GaussianGammaDigammaNative.nameF
local notation "C" => constantF
local notation "Q" => quadraticCoefficientF
local notation "K" => coefficientF
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "d" => GaussianGammaDigammaNative.data

def baseData : PTm n := exponentOf qone qzero

def slopeF : PR 2 := GaussianNamedDifference.nameF D oneF

def slopeData (A B : PTm n) : PTm n := GaussianNamedDifference.data (d A B) zero

def nameF : PR 2 := addF E (multiplyF C slopeF)

def data (A B : PTm n) : PTm n :=
  addData baseData (multiplyData C slopeF (coordinate A B) (slopeData A B))

private theorem base_regular : Γ ⊢[PRAAx] pointCN E (baseData : PTm n) :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.regular qone qzero

private theorem slope_regular (A B : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B) :
    Γ ⊢[PRAAx] pointCN slopeF (slopeData A B) :=
  GaussianNamedDifference.name_regular _ _ _ _ (GaussianGammaDigammaNative.name_regular A B hs) (one_fast _)

theorem regular (A B : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  add_fast _ _ _ _ base_regular (multiply_fast _ _ _ _ (constant_regular _) (slope_regular A B hs))

theorem prefactor_split (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent E (addF E (multiplyF C K)) (prefactorData A B)
      (addData baseData (multiplyData C K (coordinate A B) coefficientData)) := by
  let c := coordinate A B
  let t := twicePoint (center A B) B
  let w : PTm n := qadd qone qone
  let u := exponentOf qzero w
  let f := multiplyF C E
  let bc : PTm n := baseData
  have hc := constant_regular (Γ := Γ) c
  have hU := GaussianBarnesCanonicalPrefactorExponentDerivative.regular (Γ := Γ) qzero w
  have h0 := GaussianBarnesCanonicalPrefactorExponentDerivative.regular (Γ := Γ) qzero t
  have oneEntry := qmul_one_right c (ofGaussian_canonical (center A B) B hB)
  have twice : Γ ⊢[PRAAx] GaussianRationalHorner.qmul c w ≐ t :=
    (GaussianRationalCoefficientScaling.qmul_add c qone qone).eqTrans (qadd_congr oneEntry oneEntry)
  have shift := scale_entries c qzero w qzero t (qmul_zero_right c) twice
  have plus := add_entries (Γ := Γ) qone qzero qzero t qone t (qadd_zero_right qone qone_canonical)
    ((qadd_commutative qzero t).eqTrans (qadd_zero_right t (qadd_canonical _ _)))
  have expanded := add_cross E E E f bc bc (exponentOf qzero t) (multiplyData C E c u)
    base_regular base_regular h0 (multiply_fast _ _ _ _ hc hU) (cross_refl _ _ base_regular)
    (cross_symm _ _ _ _ shift)
  have basis := multiply_cross C C E K c c u coefficientData hc hc hU coefficient_regular
    (cross_refl _ _ hc) GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor.basis
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ plus) (cross_trans _ _ _ _ _ _ expanded
    (add_cross E E f (multiplyF C K) bc bc (multiplyData C E c u) (multiplyData C K c coefficientData)
      base_regular base_regular (multiply_fast _ _ _ _ hc hU) (multiply_fast _ _ _ _ hc coefficient_regular)
      (cross_refl _ _ base_regular) basis))

theorem cancel_gamma (A B : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B) :
    Γ ⊢[PRAAx] crossEquivalent (addF K unscaledF) slopeF
      (addData coefficientData (unscaledData A B)) (slopeData A B) := by
  let k : PTm n := quadraticCoefficientData
  let o : PTm n := zero
  let g : PTm n := zero
  let v := d A B
  let no := negativeData o
  let H := negativeF oneF
  let s := slopeData A B
  let b := unscaledData A B
  let L := addF gammaF oneF
  let l := addData g o
  let Z := addF oneF H
  let zz := addData o no
  have ho := one_fast (Γ := Γ) o
  have hg := gamma_regular (Γ := Γ) (n := n)
  have hv := GaussianGammaDigammaNative.name_regular A B hs
  have hn := negative_fast oneF o ho
  have hr := slope_regular A B hs
  have hb := unscaled_regular A B hs
  have commute := add_cross Q L slopeF slopeF k l s s quadratic_coefficient_regular
    (add_fast _ _ _ _ hg ho) hr hr (add_commutative oneF gammaF o g ho hg) (cross_refl _ _ hr)
  have swap := GaussianGammaEulerRationalLogOrder.add_interleave gammaF oneF D H g o v no hg ho hv hn
  have inverseAtB : Γ ⊢[PRAAx] crossEquivalent Z zeroF zz b :=
    cross_trans Z zeroF zeroF zz o b (add_negative oneF o ho)
      (GaussianNameRingLaws.zero_name_cross o b)
  have cut := add_cross unscaledF unscaledF Z zeroF b b zz b hb hb (add_fast _ _ _ _ ho hn)
    (zero_fast b) (cross_refl _ _ hb) inverseAtB
  have joined := cross_trans _ _ _ _ _ _ commute (cross_trans _ _ _ _ _ _ swap
    (cross_trans _ _ _ _ _ _ cut (GaussianNameRingLaws.add_zero unscaledF b hb)))
  have adapt := add_cross K K unscaledF (addF Q slopeF) coefficientData coefficientData b (addData k s)
    coefficient_regular coefficient_regular hb (add_fast _ _ _ _ quadratic_coefficient_regular hr)
    (cross_refl _ _ coefficient_regular) (cross_symm _ _ _ _ joined)
  exact cross_trans _ _ _ _ _ _ adapt (GaussianGammaStrongLogConvexityAlgebra.add_negative_front Q slopeF k s
    quadratic_coefficient_regular hr)

theorem original_cross (A B R : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B)
    (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalPositiveFirstLogarithm.nameF nameF
      (GaussianBarnesCanonicalPositiveFirstLogarithm.data A B R) (data A B) := by
  let c := coordinate A B
  let b : PTm n := baseData
  let F := multiplyF C K
  let G := multiplyF C (addF K unscaledF)
  let P := multiplyF C slopeF
  let x := multiplyData C K c coefficientData
  let y := scaledData A B
  let z := addData coefficientData (unscaledData A B)
  let w := multiplyData C (addF K unscaledF) c z
  let s := slopeData A B
  let u := multiplyData C slopeF c s
  have hc := constant_regular (Γ := Γ) c
  have hF := multiply_fast _ _ _ _ hc (coefficient_regular (Γ := Γ))
  have hY := scaled_regular A B hs
  have hZ := add_fast _ _ _ _ (coefficient_regular (Γ := Γ)) (unscaled_regular A B hs)
  have hW := multiply_fast _ _ _ _ hc hZ
  have hS := slope_regular A B hs
  have hf := add_fast _ _ _ _ (base_regular (Γ := Γ)) hF
  have replace := add_cross E (addF E F) seriesF scaledF (prefactorData A B) (addData b x)
    (seriesData A B R) y (prefactor_regular A B) hf (series_regular A B R h) hY
    (prefactor_split A B hs.andE₂) (series_cross A B R hs h)
  have assoc := add_associative E F scaledF b x y base_regular hF hY
  have factor := distributive C K unscaledF c coefficientData (unscaledData A B)
    hc coefficient_regular (unscaled_regular A B hs)
  have cancel := multiply_cross C C (addF K unscaledF) slopeF c c z s hc hc hZ hS
    (cross_refl _ _ hc) (cancel_gamma A B hs)
  have product := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ factor) cancel
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ assoc
    (add_cross E E (addF F scaledF) P b b (addData x y) u base_regular base_regular
      (add_fast _ _ _ _ hF hY) (multiply_fast _ _ _ _ hc hS) (cross_refl _ _ base_regular) product))

def explicitF : PR 2 := addF GaussianBarnesCanonicalFirstLogarithmConstant.nameF (multiplyF C slopeF)

def explicitData (A B : PTm n) : PTm n :=
  addData GaussianBarnesCanonicalFirstLogarithmConstant.data
    (multiplyData C slopeF (coordinate A B) (slopeData A B))

theorem explicit_cross (A B R : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source A B)
    (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalPositiveFirstLogarithm.nameF explicitF
      (GaussianBarnesCanonicalPositiveFirstLogarithm.data A B R) (explicitData A B) := by
  let F := multiplyF C slopeF
  let u := multiplyData C slopeF (coordinate A B) (slopeData A B)
  have hu : Γ ⊢[PRAAx] pointCN F u := multiply_fast _ _ _ _ (constant_regular _) (slope_regular A B hs)
  have fixed : Γ ⊢[PRAAx] crossEquivalent E GaussianBarnesCanonicalFirstLogarithmConstant.nameF
      baseData GaussianBarnesCanonicalFirstLogarithmConstant.data :=
    GaussianBarnesCanonicalFirstLogarithmConstant.original_cross
  have constant := add_cross E GaussianBarnesCanonicalFirstLogarithmConstant.nameF F F baseData
    GaussianBarnesCanonicalFirstLogarithmConstant.data u u base_regular
    GaussianBarnesCanonicalFirstLogarithmConstant.regular hu hu fixed (cross_refl _ _ hu)
  exact cross_trans _ _ _ _ _ _ (original_cross A B R hs h) constant

theorem actual_Barnes_first_logarithm_digamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let A := var 0; let B := var 1; let R := var 2
     (GaussianStirlingGammaLogarithm.source A B ⋏ disk (center A B) R B) ⟶
       crossEquivalent GaussianBarnesCanonicalPositiveFirstLogarithm.nameF explicitF
         (GaussianBarnesCanonicalPositiveFirstLogarithm.data A B R) (explicitData A B)) :=
  closeUniv 3 (.impI (explicit_cross _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmDigamma
