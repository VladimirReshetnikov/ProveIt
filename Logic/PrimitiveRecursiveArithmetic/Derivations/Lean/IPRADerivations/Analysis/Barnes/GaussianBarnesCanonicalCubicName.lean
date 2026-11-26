import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogObservation
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent

/-!
# The original cubic logarithm and the exact first two terms

The unscaled rounded cubic observations are a regular name. Adding the
exact rational first two Taylor terms produces the original rounded
local logarithm. Both actual rounding codes are compared to the same
exact finite Taylor value.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCubicName

open_ipra
open ComplexLogarithmName (baseNumerator baseDenominator base_positive)
open GaussianBarnesCanonicalLogRow (cubic roundedCubic rounding_distance)
open GaussianBarnesCanonicalLogObservation (cubic_ordered_distance)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLocalLogarithmName (source data)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder
  (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_from_later_observations)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr rescale_to)
open DyadicComplexLogarithm (unit precision)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "dyadic" => GaussianCoefficientNameBounds.unit
local notation "L" => GaussianLocalLogarithmName.pointF

def base (z N : PTm n) : PTm n := ofGaussian (baseNumerator z N) (baseDenominator N)

def nameF : PR 2 := PTm.toPR (roundedCubic (var 0) (fstT (var 1))
  (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_base {m : ℕ} (σ : Fin n → PTm m) (z N : PTm n) :
    Syn.subst σ (base z N) = base (Syn.subst σ z) (Syn.subst σ N) := by simp [base]

theorem sample_at (p z R N : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R N) ≐ roundedCubic p z R N := by
  let X := data z R N
  have raw : Γ ⊢[PRAAx] ap2 nameF p X ≐ roundedCubic p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF,ap2] using
      toPR_eq (Γ := Γ) (roundedCubic (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (roundedCubic (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,z,R,N])
    (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

private theorem guard_bits (p C : PTm n) (hC : Γ ⊢[PRAAx] le C (num 16)) :
    Γ ⊢[PRAAx] le (C*dyadic p) (one*unit p) :=
  le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (GaussianLocalLogarithmName.unit_factor p).eqSymm
    |>.eqTrans (one_mul _).eqSymm) (mul_le_mul_right (dyadic p) hC)

theorem regular (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] pointCN nameF (data z R N) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have h' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  have ordered {Θ : List (Fm PTm (n+2))} (a b : PTm (n+2)) (hab : Θ ⊢[PRAAx] le a b)
      (hc : Θ ⊢[PRAAx] source (sh z) (sh R) (sh N)) :
      Θ ⊢[PRAAx] distanceBounded (roundedCubic b (sh z) (sh R) (sh N)) (roundedCubic a (sh z) (sh R) (sh N))
        one (dyadic a) :=
    distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive _) (GaussianCoefficientNameBounds.unit_positive _)
      (guard_bits a (num 5) (le_of_eq_add (d := num 11) (by ipra_ring)))
      (cubic_ordered_distance a b (sh z) (sh R) (sh N) hc hab)
  have hbound : Δ ⊢[PRAAx] distanceBounded (roundedCubic p (sh z) (sh R) (sh N)) (roundedCubic q (sh z) (sh R) (sh N))
      (dyadic p+dyadic q) (dyadic p*dyadic q) :=
    distance_from_later_observations _ _ p q (ordered p q Prf.hyp0 h'.wk) (ordered q p Prf.hyp0 h'.wk)
  simpa only [pointCN,GaussianLocalLogarithmName.subst_data,GaussianEuclideanPointDistance.unit,
    GaussianCoefficientNameBounds.unit,Syn.shift,sh,p,q,Δ] using
    distance_congr (sample_at p (sh z) (sh R) (sh N)).eqSymm
      (sample_at q (sh z) (sh R) (sh N)).eqSymm (.eqRefl _) (.eqRefl _) hbound

theorem finite_split (z N l : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qadd (cubic z N l) (base z N) ≐ GaussianFiniteLogarithmSampler.sample z N l := by
  let D := LogarithmRemainder.denominator N l
  let E := baseDenominator N
  let F := E*D
  let a := ComplexLogarithmRemainder.series z N l
  let b := baseNumerator z N
  let c := ComplexLogarithmName.finiteNumerator z N l
  have hD := LogarithmRemainder.denominator_positive N l hN
  have hE := base_positive N hN
  have hF := positive_product _ _ hE hD
  have r := rescale_to (cubic z N l) a D E F (ofGaussian_represents a D hD) (mul_comm _ _)
  have s := rescale_to (base z N) b E D F (ofGaussian_represents b E hE) (.eqRefl _)
  have both := GaussianRationalHorner.qadd_represents _ _ _ _ _ hF r s
  have sumEq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (ComplexLogarithmRemainder.scale E a) (ComplexLogarithmRemainder.scale D b)) c := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [c,ComplexLogarithmName.finiteNumerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add, a,b,D,E] <;> ring
  have raw := GaussianRationalHorner.represents_congr (.eqRefl _) sumEq (.eqRefl _) both
  exact GaussianRationalHorner.canonical_unique _ _ c F (GaussianRationalHorner.qadd_canonical _ _)
    (ofGaussian_canonical c F hF) hF raw (ofGaussian_represents c F hF)

private theorem add_fixed {x y : PTm n} (a A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y A D) :
    Γ ⊢[PRAAx] distanceBounded (qadd x a) (qadd y a) A D :=
  distance_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ hD h (GaussianRationalPowerDifference.distance_refl_zero a D hD))

theorem raw_split_observation (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (qadd (roundedCubic p z R N) (base z N))
      (ap2 L p (data z R N)) (num 6) (unit p) := by
  let D := unit p
  let a := base z N
  have hD := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have inner := add_fixed a two D hD (rounding_distance p z R N hN)
  have first := distance_congr (.eqRefl _) (finite_split z N (precision p) hN) (.eqRefl _) (.eqRefl _) inner
  have second := distance_symmetric _ _ _ _ hD (GaussianLocalLogarithmName.point_rounding_distance p z R N hN)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first second)

theorem split_observation (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (addF nameF constantF) p (addData (data z R N) (base z N)))
      (ap2 L p (data z R N)) one (dyadic p) := by
  let t := GaussianFastValueCut.exponent two p
  let D := unit p
  let a := base z N
  let x := data z R N
  have hD := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have read := (GaussianExponentialReference.add_sample (Γ := Γ) nameF constantF x a p).eqTrans
    (qadd_congr (sample_at t z R N) (constant_at t a))
  have first := add_fixed a (num 5) D hD (cubic_ordered_distance p t z R N h (le_add_right _ _))
  have second := raw_split_observation p z R N h.andE₁
  have total := distance_triangle_same _ _ _ _ _ _ hD first second
  have hcap : Γ ⊢[PRAAx] le ((num 5+num 6)*dyadic p) (one*D) :=
    guard_bits p _ (le_of_eq_add (d := num 5) (by ipra_ring))
  exact distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hD (GaussianCoefficientNameBounds.unit_positive p) hcap total)

theorem split_cross (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) :
    Γ ⊢[PRAAx] crossEquivalent (addF nameF constantF) L (addData (data z R N) (base z N)) (data z R N) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ one
    (add_fast nameF constantF _ _ (regular z R N h) (constant_regular _))
    (GaussianLocalLogarithmName.name_regular z R N h)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, sh, GaussianNameArithmetic.subst_addData,
    GaussianLocalLogarithmName.subst_data, subst_base, one, PTm.subst_succ, PTm.subst_zero] using
    split_observation (var 0) (sh z) (sh R) (sh N) hs

theorem actual_local_logarithm_cubic_split_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ crossEquivalent (addF nameF constantF) L
        (addData (data (var 0) (var 1) (var 2)) (base (var 0) (var 2))) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (split_cross _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCubicName
