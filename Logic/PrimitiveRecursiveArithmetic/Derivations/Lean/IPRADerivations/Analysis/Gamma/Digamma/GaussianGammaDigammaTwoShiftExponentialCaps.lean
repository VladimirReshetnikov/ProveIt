import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftBinding
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaHarmonicCells
import IPRADerivations.Analysis.Exponential.GaussianExponentialUnitPerturbation
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope

/-!
# Sharp unit-radius bounds for constant exponential caps

The original exponential name obeys 1−2t ≤ exp(−t) and
exp(t) ≤ 1+2t for an exact rational 0≤t≤1.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExponentialCaps

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaHarmonicCells (point_fraction_represents)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRadiusExponentialName (sample data)
open GaussianRationalHorner (canonical ofGaussian_canonical qadd scalar_congr)
open GaussianRationalMetric (bounded qnegative qsub)
open GaussianRationalReciprocal (bound_congr bounded_negative qone_represents_scaled)
open GaussianRationalSyntheticDivision (qone)
open RationalArgmin (rationalLE)
open RationalRepresentedUpper (left right to_signed)
open RationalValueBounds (upper upper_of_radius upper_of_order upper_congr radius_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def lower (k a : PTm n) : PTm n := qsub qone (fraction (two*k) a)
def upperPoint (k a : PTm n) : PTm n := qadd qone (fraction (two*k) a)

@[simp] theorem subst_lower {m : ℕ} (σ : Fin n → PTm m) (k a : PTm n) :
    Syn.subst σ (lower k a) = lower (Syn.subst σ k) (Syn.subst σ a) := by simp [lower,two]
@[simp] theorem subst_upperPoint {m : ℕ} (σ : Fin n → PTm m) (k a : PTm n) :
    Syn.subst σ (upperPoint k a) = upperPoint (Syn.subst σ k) (Syn.subst σ a) := by simp [upperPoint,two]

private theorem unit_fraction (k a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] bounded (fraction k a) k a :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point k a ha).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded k a ha)

private theorem unit_input (q k a : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hk : Γ ⊢[PRAAx] le k a)
    (h : Γ ⊢[PRAAx] bounded q k a) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF one q :=
  GaussianSignedNameExponentialOrder.constant_input q one
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ ha (le_refl one)
      (by ipra_le sl hk) h)

private theorem one_rep (a : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT qone) (ZT.ofNat a) a :=
  scalar_congr (.eqRefl _) (by apply ZT.derive; simp [GaussianRootAlgebra.re_scale,
    GaussianRootAlgebra.re_one,ZT.toZ_ofNat]) (.eqRefl _)
    (qone_represents_scaled (Γ := Γ) a).andE₁

private theorem real_rep (z : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT z)
    (ComplexLogarithmRemainder.re (GaussianRationalL1.rawGaussian z)) (GaussianRationalL1.rawDen z) :=
  (GaussianRationalL1.raw_represents (Γ := Γ) z).andE₁

private theorem upper_rep (k a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (upperPoint k a)) (ZT.ofNat a+ZT.ofNat (two*k)) a :=
  scalar_congr (RationalGaussianRealPart.real_add _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalHorner.scalar_add_same _ _ _ _ _ ha (one_rep a) (point_fraction_represents (two*k) a ha))

private theorem lower_rep (k a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (lower k a)) (ZT.ofNat a + (-ZT.ofNat (two*k))) a := by
  have rn : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qnegative (fraction (two*k) a))) (-ZT.ofNat (two*k)) a :=
    scalar_congr (fst_pair _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (RationalRepresentations.represents_negative _ _ _ (point_fraction_represents (two*k) a ha))
  exact scalar_congr (RationalGaussianRealPart.real_add _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalHorner.scalar_add_same _ _ _ _ _ ha (one_rep a) rn)

private theorem explicit_upper (z k a : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] upper (fstT z) (fstT qone) (two*k) a) :
    Γ ⊢[PRAAx] rationalLE (fstT z) (fstT (upperPoint k a)) := by
  let d := GaussianRationalL1.rawDen z
  let r := ComplexLogarithmRemainder.re (GaussianRationalL1.rawGaussian z)
  let k' := two*k
  have o := to_signed _ _ r (ZT.ofNat one) d one k' a (real_rep z) (one_rep one) h
  apply RationalArithmetic.order_of_representations _ _ r (ZT.ofNat a+ZT.ofNat k') d a (real_rep z) (upper_rep k a ha)
    (GaussianRationalL1.raw_den_positive z) ha
  apply zle_of_toZ (PolynomialBisection.slack (left r one a) (right (ZT.ofNat one) d one k' a))
  have e := zle_toZ o
  simp only [left,right,PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,
    Q.mk_mul,Q.mk_one,map_mul,map_one] at e ⊢
  linear_combination e

private theorem explicit_lower (z k a : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] upper (fstT qone) (fstT z) (two*k) a) :
    Γ ⊢[PRAAx] rationalLE (fstT (lower k a)) (fstT z) := by
  let d := GaussianRationalL1.rawDen z
  let r := ComplexLogarithmRemainder.re (GaussianRationalL1.rawGaussian z)
  let k' := two*k
  have o := to_signed _ _ (ZT.ofNat one) r one d k' a (one_rep one) (real_rep z) h
  apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat a+(-ZT.ofNat k')) r a d (lower_rep k a ha) (real_rep z)
    ha (GaussianRationalL1.raw_den_positive z)
  apply zle_of_toZ (PolynomialBisection.slack (left (ZT.ofNat one) d a) (right r one d k' a))
  have e := zle_toZ o
  simp only [left,right,PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,
    Q.mk_mul,Q.mk_one,map_mul,map_one] at e ⊢
  linear_combination e

private theorem sample_caps (p k a : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hk : Γ ⊢[PRAAx] le k a) :
    Γ ⊢[PRAAx]
      (rationalLE (fstT (lower k a)) (fstT (sample constantF one p (qnegative (fraction k a)))) ⋏
       rationalLE (fstT (sample constantF one p (fraction k a))) (fstT (upperPoint k a))) := by
  let q := fraction k a
  have h := unit_fraction k a ha
  have qP := GaussianExponentialUnitPerturbation.constant_sample_two q k a p ha hk h (ofGaussian_canonical _ _ ha)
  have qN := GaussianExponentialUnitPerturbation.constant_sample_two (qnegative q) k a p ha hk
    (bounded_negative _ _ _ ha h) (GaussianRationalMetric.qnegative_canonical _)
  have pR := scalar_coordinate_distance _ _ _ _ ha qP
  have nR := radius_symmetric _ _ _ _ (scalar_coordinate_distance _ _ _ _ ha qN)
  exact .andI (explicit_lower _ k a ha (upper_of_radius _ _ _ _ nR)) (explicit_upper _ k a ha (upper_of_radius _ _ _ _ pR))

theorem constant_caps (k a : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hk : Γ ⊢[PRAAx] le k a) :
    Γ ⊢[PRAAx]
      (realOrder constantF (E constantF) (lower k a) (ed constantF (qnegative (fraction k a))) ⋏
       realOrder (E constantF) constantF (ed constantF (fraction k a)) (upperPoint k a)) := by
  let q := fraction k a
  let v := qnegative q
  let D := data one q
  let B := data one v
  have cp := constant_regular (Γ := Γ) q
  have cv := constant_regular (Γ := Γ) v
  have small := unit_fraction k a ha
  have ip := unit_input q k a ha hk small
  have iv := unit_input v k a ha hk (bounded_negative _ _ _ ha small)
  have hp := GaussianRadiusExponentialName.name_regular _ _ _ ip
  have hv := GaussianRadiusExponentialName.name_regular _ _ _ iv
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have H : Δ ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift,Δ] using ha.shift
  have K : Δ ⊢[PRAAx] le (Syn.shift k) (Syn.shift a) := by simpa [Fm.shift,Syn.shift,Δ] using hk.shift
  have h := sample_caps p (Syn.shift k) (Syn.shift a) H K
  have left : Γ ⊢[PRAAx] envelope constantF (E constantF) (lower k a) B zero := by
    refine .allI ?_
    simpa [envelope,B,v,q,Syn.shift,p,sample,Δ] using
      (upper_congr (congrFst (constant_at p (lower (Syn.shift k) (Syn.shift a))).eqSymm) (.eqRefl _)
        (.eqRefl _) (.eqRefl _) (upper_of_order _ _ zero (GaussianCoefficientNameBounds.unit p) h.andE₁))
  have right : Γ ⊢[PRAAx] envelope (E constantF) constantF D (upperPoint k a) zero := by
    refine .allI ?_
    simpa [envelope,D,q,Syn.shift,p,sample,Δ] using
      (upper_congr (.eqRefl _) (congrFst (constant_at p (upperPoint (Syn.shift k) (Syn.shift a))).eqSymm)
        (.eqRefl _) (.eqRefl _) (upper_of_order _ _ zero (GaussianCoefficientNameBounds.unit p) h.andE₂))
  have lo := order_from_envelope _ _ _ _ _ (constant_regular _) hv left
  have hi := order_from_envelope _ _ _ _ _ hp (constant_regular _) right
  have eq := GaussianExponentialRadiusIndependence.same_input_cross constantF _ _ q ip (exponential_input _ _ cp)
  have ev := GaussianExponentialRadiusIndependence.same_input_cross constantF _ _ v iv (exponential_input _ _ cv)
  exact .andI
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_refl _ _ (constant_regular _)) ev lo)
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ eq) (cross_refl _ _ (constant_regular _)) hi)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExponentialCaps
