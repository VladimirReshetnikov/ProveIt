import IPRADerivations.Analysis.GaussianBinetLaplaceExponential
import IPRADerivations.Analysis.GaussianGammaEulerShift
import IPRADerivations.Analysis.GaussianExponentialLinearRemainder

/-!
# A uniform forward step for the actual complex Laplace exponential

The input can be any canonical rational Gaussian exponent with
nonpositive real part. A small displacement with nonpositive real
part gives a squared spatial error and a uniform dyadic sampling
error. Both samples use their original exponential programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialPanel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameArithmetic (multiplyF multiplyData multiply_at multiplyModulus product_distance)
open GaussianNameEquivalence (cross_at point_at)
open GaussianRadiusExponentialName (input data name_regular sample_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (canonical positive_product qadd qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qsub_congr qadd_sub_cancel)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianReciprocalHorner (qmul_one_right)
open RationalArgmin (rationalLE)
open GaussianRationalSyntheticBounds (natCode)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

abbrev expoF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def sample (p q R : PTm n) : PTm n := ap2 expoF p (data R q)
def nonpositive (q : PTm n) : Fm PTm n := rationalLE (fstT q) (natCode zero)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p q R : PTm n) :
    Syn.subst σ (sample p q R) = sample (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ R) := by
  simp [sample]

theorem unit_bound (p q R : PTm n) (hq : Γ ⊢[PRAAx] input constantF R q)
    (hn : Γ ⊢[PRAAx] nonpositive q) :
    Γ ⊢[PRAAx] bounded (sample p q R) two one := by
  have hp := unit_positive (Γ := Γ) p
  exact bounded_radius_mono _ _ _ _ _ hp (le_refl one)
    (by ipra_le sl hp) (GaussianBinetLaplaceExponential.original_unit_bound q R p hq hn)

private theorem clock_error (p s q R : PTm n) (hps : Γ ⊢[PRAAx] le p s)
    (hq : Γ ⊢[PRAAx] input constantF R q) :
    Γ ⊢[PRAAx] distanceBounded (sample s q R) (sample p q R) two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have h := GaussianExponentialReference.unit_monotone hps
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs hp) hp
    (by ipra_le 𝔞(unit p)*sl h)
    (point_at expoF (data R q) s p (name_regular _ _ _ hq))

theorem product_sample (p x y R S T : PTm n)
    (hx : Γ ⊢[PRAAx] input constantF R x) (hy : Γ ⊢[PRAAx] input constantF S y)
    (hs : Γ ⊢[PRAAx] input constantF T (qadd x y))
    (hxn : Γ ⊢[PRAAx] nonpositive x) (hyn : Γ ⊢[PRAAx] nonpositive y) :
    Γ ⊢[PRAAx] distanceBounded (sample p (qadd x y) T) (qmul (sample p x R) (sample p y S)) (num 10) (unit p) := by
  let X := data R x
  let Y := data S y
  let L := multiplyModulus expoF expoF X Y
  let j := GaussianFastValueCut.exponent L p
  let W := ap2 (multiplyF expoF expoF) p (multiplyData expoF expoF X Y)
  have hp := unit_positive (Γ := Γ) p
  have cross := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent constantF constantF constantF
    R S T x y (qadd x y) hx hy hs (GaussianGammaEulerShift.constant_sum_cross x y)
  have d₁ : Γ ⊢[PRAAx] distanceBounded (sample p (qadd x y) T) W two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
      (le_of_eq_add (d := zero) (by ipra_ring))
      (cross_at _ _ _ _ p p (GaussianNameEquivalence.cross_symm _ _ _ _ cross))
  have read : Γ ⊢[PRAAx] W ≐ qmul (sample j x R) (sample j y S) :=
    (multiply_at expoF expoF X Y p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have later : Γ ⊢[PRAAx] le p j := le_add_right _ _
  have d₂ := distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (product_distance _ _ _ _ two two (unit p) two two hp
      (clock_error p j x R later hx) (clock_error p j y S later hy) (unit_bound j y S hy hyn) (unit_bound p x R hx hxn))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp d₁ d₂)

theorem step_error (p x y R T A B : PTm n)
    (hx : Γ ⊢[PRAAx] input constantF R x) (hs : Γ ⊢[PRAAx] input constantF T (qadd x y))
    (hxn : Γ ⊢[PRAAx] nonpositive x) (hyn : Γ ⊢[PRAAx] nonpositive y)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hy : Γ ⊢[PRAAx] bounded y A B) (hc : Γ ⊢[PRAAx] canonical y) :
    Γ ⊢[PRAAx] distanceBounded (qsub (sample p (qadd x y) T) (sample p x R))
      (qmul (sample p x R) y) (num 10*(B*B)+two*(A*A)*unit p) ((unit p)*(B*B)) := by
  let u := sample p x R
  let v := sample p y one
  let w := sample p (qadd x y) T
  let E := unit p
  let D := B*B
  have hp := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hB
  have hy₁ : Γ ⊢[PRAAx] bounded y one one :=
    bounded_radius_mono _ _ _ _ _ hB (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) hA) hy
  have hi := GaussianSignedNameExponentialOrder.constant_input y one hy₁
  have product := product_sample p x y R one T hx hi hs hxn hyn
  have first : Γ ⊢[PRAAx] distanceBounded (qsub w u) (qsub (qmul u v) u) (num 10) E :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp product (distance_refl_zero _ _ hp))
  have linear : Γ ⊢[PRAAx] distanceBounded v (qadd qone y) (A*A) D :=
    GaussianExponentialLinearRemainder.original_constant_exponential_linear_remainder y A B p hB hA hy hc
  have scaled := GaussianApproximateInverseDistance.multiply_distance u v (qadd qone y) two (A*A) D hD
    (unit_bound p x R hx hxn) linear
  have simplify : Γ ⊢[PRAAx] qsub (qmul u (qadd qone y)) u ≐ qmul u y :=
    (qsub_congr ((qmul_add u qone y).eqTrans (GaussianRationalSyntheticDivision.qadd_congr
      (qmul_one_right u (GaussianRadiusExponentialName.sample_canonical constantF R p x)) (.eqRefl _))) (.eqRefl _)).eqTrans
      (qadd_sub_cancel _ _ (qmul_canonical _ _))
  have second : Γ ⊢[PRAAx] distanceBounded (qsub (qmul u v) u) (qmul u y) (two*(A*A)) D :=
    distance_congr (.eqRefl _) simplify (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hD scaled (distance_refl_zero _ _ hD))
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hp hD first second

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialPanel
