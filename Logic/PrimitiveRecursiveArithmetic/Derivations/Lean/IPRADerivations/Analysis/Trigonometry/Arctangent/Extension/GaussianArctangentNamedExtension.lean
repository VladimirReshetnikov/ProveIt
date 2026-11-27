import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentClippedParameter
import IPRADerivations.Analysis.Trigonometry.Arctangent.Comparisons.GaussianArctangentForwardLipschitz
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialRepresentation

/-!
# The arctangent phase on arbitrary regular parameter names

The actual parameter sample is projected to its real coordinate and
clipped to the unit interval. The original partial arctangent is
then queried on the resulting numerator and denominator. Using p+2
for both queries covers the slope bound and the native quadrature error.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedExtension

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (point_at crossEquivalent cross_to_diagonal diagonal_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianRationalMetric (distanceBounded)
open RationalArithmetic (represents)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalValueBounds (radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (p : PTm n) : PTm n := p+two
def parameter (f : PR 2) (p x : PTm n) : PTm n := fstT (ap2 f (clock p) x)
def numerator (f : PR 2) (p x : PTm n) : PTm n := GaussianArctangentClippedParameter.numerator (parameter f p x)
def denominator (f : PR 2) (p x : PTm n) : PTm n := GaussianArctangentClippedParameter.denominator (parameter f p x)
def sample (f : PR 2) (p x : PTm n) : PTm n :=
  ap2 GaussianArctangentPartialQuadrature.nameF (clock p)
    (GaussianArctangentPartialQuadrature.data (numerator f p x) (denominator f p x))
def nameF (f : PR 2) : PR 2 := PTm.toPR (sample f (var 0) (var 1) : PTm 2)

ipra_subst clock
ipra_subst parameter
ipra_subst numerator
ipra_subst denominator
ipra_subst sample

theorem denominator_positive (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le one (denominator f p x) :=
  GaussianArctangentClippedParameter.denominator_positive _
theorem numerator_le (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le (numerator f p x) (denominator f p x) :=
  GaussianArctangentClippedParameter.numerator_le _

theorem sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p x ≐ sample f p x := by
  simpa [nameF,ap2] using toPR_eq (Γ := Γ) (sample f (var 0) (var 1) : PTm 2) ![p,x]

theorem parameter_specialization (f : PR 2) (p x A B : PTm n)
    (hAB : Γ ⊢[PRAAx] le A B) (hrep : Γ ⊢[PRAAx] represents (parameter f p x) (ZT.ofNat A) B) :
    Γ ⊢[PRAAx] numerator f p x*B ≐ A*denominator f p x :=
  GaussianArctangentClippedParameter.representation_clips_exactly _ _ _ hAB hrep

theorem parameter_represents_of_embedding (f : PR 2) (p x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] ap2 f (clock p) x ≐ RationalGaussianEmbedding.embed (fraction A B)) :
    Γ ⊢[PRAAx] represents (parameter f p x) (ZT.ofNat A) B := by
  have realPart : Γ ⊢[PRAAx] parameter f p x ≐ RationalArithmetic.recode (fraction A B) :=
    h.fstE
  exact scalar_congr realPart.eqSymm (.eqRefl _) (.eqRefl _)
    (RationalGaussianEmbedding.scalar_recode_represents _ _ _ (fraction_represents A B hB))

theorem partial_specialization (f : PR 2) (p x A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (hrep : Γ ⊢[PRAAx] represents (parameter f p x) (ZT.ofNat A) B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianArctangentPartialQuadrature.nameF GaussianArctangentPartialQuadrature.nameF
      (GaussianArctangentPartialQuadrature.data (numerator f p x) (denominator f p x))
      (GaussianArctangentPartialQuadrature.data A B) :=
  GaussianArctangentPartialRepresentation.representation_cross _ _ _ _ (denominator_positive f p x) hB
    (numerator_le f p x) (parameter_specialization f p x A B hAB hrep)

theorem partial_distance (f : PR 2) (p x A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B)
    (hrep : Γ ⊢[PRAAx] represents (parameter f p x) (ZT.ofNat A) B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p x)
      (ap2 GaussianArctangentPartialQuadrature.nameF (clock p) (GaussianArctangentPartialQuadrature.data A B))
      two (unit (clock p)) :=
  distance_congr (sample_at f p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (diagonal_at _ _ _ _ (clock p) (cross_to_diagonal _ _ _ _ (partial_specialization f p x A B hB hAB hrep)))

theorem unit_clock (p : PTm n) : Γ ⊢[PRAAx] unit (clock p) ≐ num 4*unit p :=
  (pw_add_numeral 2 2 p).eqTrans (mul_comm _ _)

private theorem scheduled_budget (p q : PTm n) :
    Γ ⊢[PRAAx] le (((unit (clock p)+unit (clock q))*(unit (clock p)*unit (clock q))+
      two*(unit (clock p)+unit (clock q))*(unit (clock p)*unit (clock q)))*(unit p*unit q))
      ((unit p+unit q)*((unit (clock p)*unit (clock q))*(unit (clock p)*unit (clock q)))) := by
  apply le_of_eq_add (d := (unit p+unit q)*(unit p*unit q)*(num 4*(unit (clock p)*unit (clock q))))
  have ep := natEq (unit_clock (Γ := Γ) p)
  have eq := natEq (unit_clock (Γ := Γ) q)
  apply deriveNat
  ipra_simps
  rw [ep,eq]
  ring

theorem sample_regularity (f : PR 2) (p q x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x) (sample f q x) (unit p+unit q) (unit p*unit q) := by
  let H := unit (clock p)+unit (clock q)
  let K := unit (clock p)*unit (clock q)
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ (unit_positive _) (unit_positive _)
  have raw : Γ ⊢[PRAAx] radius (parameter f p x) (parameter f q x) H K :=
    GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hK
      (point_at f x (clock p) (clock q) hf)
  have clipped := GaussianArctangentClippedParameter.value_radius _ _ H K raw
  have out := GaussianArctangentForwardLipschitz.forward_distance (clock p) (clock q)
    (numerator f p x) (denominator f p x) (numerator f q x) (denominator f q x) H K
    (denominator_positive f p x) (denominator_positive f q x) (numerator_le f p x) (numerator_le f q x) hK clipped
  exact distance_radius_mono _ _ _ _ _ _ (positive_product K K hK hK)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (scheduled_budget p q) out

theorem name_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (nameF f) x := by
  let a := Syn.shift (Syn.shift x)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f a := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift,a] using hf.shift.shift
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,a,p,q] using
    distance_congr (sample_at f p a).eqSymm (sample_at f q a).eqSymm
      (.eqRefl _) (.eqRefl _) (sample_regularity f p q a hs)

theorem actual_named_arctangent_extension_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (nameF f) (var 0) (var 1) ≐ sample f (var 0) (var 1)) :=
  closeUniv 2 (sample_at f _ _)

theorem actual_named_arctangent_extension_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ pointCN (nameF f) (var 0)) :=
  closeUniv 1 (.impI (name_regular f _ Prf.hyp0))

theorem actual_named_arctangent_extension_specialization_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ le (var 2) (var 3) ⟶
      represents (parameter f (var 0) (var 1)) (ZT.ofNat (var 2)) (var 3) ⟶
      distanceBounded (ap2 (nameF f) (var 0) (var 1))
        (ap2 GaussianArctangentPartialQuadrature.nameF (clock (var 0)) (GaussianArctangentPartialQuadrature.data (var 2) (var 3)))
        two (unit (clock (var 0)))) :=
  closeUniv 4 (.impI (.impI (.impI (partial_distance f _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedExtension
