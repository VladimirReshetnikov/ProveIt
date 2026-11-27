import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Logarithms.GaussianEulerUnitLogarithmicMargin
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveExponentialOrder

/-!
# The actual logarithm of the positive unit-substitution time

At u=a/b with 0<a<b, every original harmonic observation of log(b/a)
is a proved positive rational fraction. The original positive-rational
logarithm is evaluated on that actual fraction, with its own observation
query. A fixed lower margin b and Fast(2b,p) pay the inner observations;
the outer query p+1 pays the remaining half of each dyadic allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicComposition

open_ipra
open GaussianEulerUnitLogarithmicMargin (source numerator denominator timeF timeData evaluated_time_domain)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def query (p b : PTm n) : PTm n := GaussianFastValueCut.exponent (two*b) p
def observation (p a b : PTm n) : PTm n := GaussianPositiveRationalLogarithm.sample (succ p)
  (numerator (query p b) a b) (denominator (query p b) a b)
def data (a b : PTm n) : PTm n := pairT a b
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (sndT (var 1)))
def sample (p a b : PTm n) : PTm n := ap2 nameF p (data a b)
def radius (b : PTm n) : PTm n := GaussianCompactLogarithmBounds.radius b b

ipra_subst query
ipra_subst observation
ipra_subst data
ipra_subst sample
ipra_subst radius

theorem sample_at (p a b : PTm n) : Γ ⊢[PRAAx] sample p a b ≐ observation p a b := by
  have first : Γ ⊢[PRAAx] sample p a b ≐ observation p (fstT (data a b)) (sndT (data a b)) := by
    simpa [sample,nameF,ap2] using toPR_eq (Γ := Γ)
      (observation (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,data a b]
  have second := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (observation (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![p,fstT (data a b),sndT (data a b)]) (σ' := ![p,a,b]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact snd_pair _ _)
  exact first.eqTrans (by simpa using second)

private theorem scalar_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    fstT (fraction a b) ≐ GaussianPositiveRationalLogarithmVariation.time a b := by
  have rep := (GaussianRationalHorner.ofGaussian_represents (Γ := Γ)
    (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b hb).andE₁
  have actual : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat a) b :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
      ring) (.eqRefl _) rep
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb).andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ hb) actual (RationalCubeMidpoint.fraction_represents _ _ hb) hb hb (.eqRefl _)

private theorem scalar_time_distance (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    RationalValueBounds.radius
      (GaussianPositiveRationalLogarithmVariation.time (numerator p a b) (denominator p a b))
      (GaussianPositiveRationalLogarithmVariation.time (numerator q a b) (denominator q a b))
      (unit p+unit q) (unit p*unit q) := by
  have cp := GaussianEulerUnitLogarithmicMargin.actual_time_fraction p a b (le_of_lt h.andE₂)
  have cq := GaussianEulerUnitLogarithmicMargin.actual_time_fraction q a b (le_of_lt h.andE₂)
  have old := GaussianNameEquivalence.point_at timeF (timeData a b) p q (GaussianEulerUnitLogarithmicMargin.time_regular a b h)
  have actual := distance_congr cp cq (.eqRefl _) (.eqRefl _) old
  exact RationalValueBounds.radius_congr
    (scalar_fraction _ _ (GaussianEulerUnitLogarithmicMargin.denominator_positive p a b))
    (scalar_fraction _ _ (GaussianEulerUnitLogarithmicMargin.denominator_positive q a b)) (.eqRefl _) (.eqRefl _)
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) actual)

private theorem observation_regularity (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (observation p a b) (observation q a b) (unit p+unit q) (unit p*unit q) := by
  let r := query p b
  let s := query q b
  let A := unit r+unit s
  let D := unit r*unit s
  have hr := evaluated_time_domain r a b h
  have hs := evaluated_time_domain s a b h
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive r) (unit_positive s)
  have input : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithmVariation.input
      (numerator r a b) (denominator r a b) (numerator s a b) (denominator s a b) b A D :=
    .andI hr.andE₁ (.andI hs.andE₁ (.andI hD (.andI hr.andE₂.andE₁ (.andI hs.andE₂.andE₁ (scalar_time_distance r s a b h)))))
  have raw := GaussianPositiveRationalLogarithmVariation.original_observations (succ p) (succ q)
    (numerator r a b) (denominator r a b) (numerator s a b) (denominator s a b) b A D input
  have bp : Γ ⊢[PRAAx] le (two*b*unit p) (unit r) := GaussianFastValueCut.query_budget _ _
  have bq : Γ ⊢[PRAAx] le (two*b*unit q) (unit s) := GaussianFastValueCut.query_budget _ _
  have up : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
  have uq : Γ ⊢[PRAAx] unit (succ q) ≐ two*unit q := (pw_succ two q).eqTrans (mul_comm _ _)
  have eN : Γ ⊢[PRAAx] rateNumerator (b*A) D (succ p) (succ q) ≐
      (b*A)*(two*unit p)*(two*unit q)+D*(two*unit p+two*unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) uq) (congrMul (.eqRefl _) (congrAdd up uq))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) (succ q) ≐ D*(two*unit p)*(two*unit q) :=
    congrMul (congrMul (.eqRefl _) up) uq
  have adjusted := distance_congr (.eqRefl _) (.eqRefl _) eN eD raw
  have hd := positive_product _ _ (positive_product _ _ hD (positive_product _ _ (zero_lt_succ one) (unit_positive p)))
    (positive_product _ _ (zero_lt_succ one) (unit_positive q))
  exact distance_radius_mono _ _ _ _ _ _ hd
    (positive_product _ _ (unit_positive p) (unit_positive q)) (by
      dsimp only [A,D]
      ipra_le (2*𝔞(unit p)*𝔞(unit q)*𝔞(unit s)*𝔞(unit q))*sl bp+
        (2*𝔞(unit p)*𝔞(unit q)*𝔞(unit r)*𝔞(unit p))*sl bq) adjusted

theorem sample_regularity (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample q a b) (unit p+unit q) (unit p*unit q) :=
  distance_congr (sample_at p a b).eqSymm (sample_at q a b).eqSymm (.eqRefl _) (.eqRefl _) (observation_regularity p q a b h)

theorem name_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data a b) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [GaussianEuclideanDistanceName.pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,
    Syn.shift,subst_data,sample] using sample_regularity (var 1) (var 0) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) hs

theorem sample_bound (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    bounded (sample p a b) (radius b) one :=
  GaussianRationalReciprocal.bound_congr (sample_at p a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCompactLogarithmBounds.sample_bound (succ p) _ _ b b (le_trans h.andE₁ (le_of_lt h.andE₂)) (evaluated_time_domain (query p b) a b h))

theorem actual_unit_logarithmic_composition_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicComposition
