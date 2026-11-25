import IPRADerivations.Analysis.GaussianExponentialReference
import IPRADerivations.Analysis.GaussianNameRingLaws
import IPRADerivations.Analysis.GaussianRadiusExponentialName

/-!
# Product observations with prescribed numerical bounds

The named multiplication clock may depend on the initial observations.
A proved uniform bound for each factor gives a numerical error that
is independent of the computed multiplication modulus.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedBoundedProductObservation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRootApproximationWitness (pointBounds)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def clock (f g : PR 2) (p x y : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus f g x y) p

theorem name_at (f g : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF f g) p (multiplyData f g x y) ≐ qmul (ap2 f (clock f g p x y) x) (ap2 g (clock f g p x y) y) :=
  (GaussianNameArithmetic.multiply_at f g x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem sample_bound_at (f g : PR 2) (p x y A B : PTm n)
    (ha : Γ ⊢[PRAAx] pointBounds f A x) (hb : Γ ⊢[PRAAx] pointBounds g B y) : Γ ⊢[PRAAx]
    bounded (ap2 (multiplyF f g) p (multiplyData f g x y)) (A*B) one :=
  GaussianRationalReciprocal.bound_congr (name_at f g p x y).eqSymm (.eqRefl _) (one_mul _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
      (GaussianRadiusExponentialName.bounded_samples_at f A x _ ha)
      (GaussianRadiusExponentialName.bounded_samples_at g B y _ hb))

theorem sample_bounds (f g : PR 2) (x y A B : PTm n)
    (ha : Γ ⊢[PRAAx] pointBounds f A x) (hb : Γ ⊢[PRAAx] pointBounds g B y) : Γ ⊢[PRAAx]
    pointBounds (multiplyF f g) (A*B) (multiplyData f g x y) := by
  refine .allI ?_
  have ha' : Γ.map Fm.shift ⊢[PRAAx] pointBounds f (Syn.shift A) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using ha.shift
  have hb' : Γ.map Fm.shift ⊢[PRAAx] pointBounds g (Syn.shift B) (Syn.shift y) := by
    simpa [Fm.shift,Syn.shift] using hb.shift
  simpa [pointBounds,Syn.shift] using sample_bound_at f g (var 0) (Syn.shift x) (Syn.shift y)
    (Syn.shift A) (Syn.shift B) ha' hb'

theorem later_sample_error (f : PR 2) (p t x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hpt : Γ ⊢[PRAAx] le p t) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f t x) (ap2 f p x) two (unit p) := by
  have grow : Γ ⊢[PRAAx] le (unit p) (unit t) := GaussianExponentialReference.unit_monotone hpt
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive p))
    (unit_positive p) (by ipra_le 𝔞 (unit p)*sl grow) (GaussianNameEquivalence.point_at f x t p hf)

theorem sample_error (f g : PR 2) (p x y A B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] pointBounds f A x) (hb : Γ ⊢[PRAAx] pointBounds g B y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF f g) p (multiplyData f g x y)) (qmul (ap2 f p x) (ap2 g p y))
      (two*(A+B)) (unit p) := by
  let t := clock f g p x y
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  exact distance_congr (name_at f g p x y).eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ two two (unit p) B A (unit_positive p)
      (later_sample_error f p t x hf ht) (later_sample_error g p t y hg ht)
      (GaussianRadiusExponentialName.bounded_samples_at g B y t hb)
      (GaussianRadiusExponentialName.bounded_samples_at f A x p ha))

end LeanProofs.IPRA.Analysis.GaussianNamedBoundedProductObservation
