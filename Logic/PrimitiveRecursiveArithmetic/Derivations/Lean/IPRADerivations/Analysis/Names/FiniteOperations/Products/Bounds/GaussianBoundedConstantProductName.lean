import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport

/-!
# A constant-product name with a supplied uniform numerical clock

The actual raw product a*f(p,x) is normalized at modulus A whenever the
constant a is bounded by A. Its computed observation clock depends only
on A and p, retaining exact product samples. Finite diagonal-envelope
elimination identifies it with the ordinary actual multiplication name.
Zero A and raw constant/input sample codes are allowed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedConstantProductName

open_ipra
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def constantF : PR 2 := PTm.toPR (var 1 : PTm 2)
def rawValue (f : PR 2) (p a x : PTm n) : PTm n := qmul a (ap2 f p x)
def rawData (a x : PTm n) : PTm n := pairT a x
def rawF (f : PR 2) : PR 2 := PTm.toPR (rawValue f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)
def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (A a x : PTm n) : PTm n := GaussianFastValueCut.nameData A (rawData a x)
def sample (f : PR 2) (p A a x : PTm n) : PTm n := ap2 (nameF f) p (data A a x)
def clock (p A : PTm n) : PTm n := GaussianFastValueCut.exponent A p
def input (f : PR 2) (A a x : PTm n) : Fm PTm n := pointCN f x ⋏ bounded a A one
def cost (f : PR 2) (A a x : PTm n) : PTm n := A+GaussianNameArithmetic.multiplyModulus constantF f a x+two
ipra_subst rawValue
ipra_subst rawData
ipra_subst data
ipra_subst clock
ipra_subst input
ipra_subst cost

theorem constant_at (p a : PTm n) : Γ ⊢[PRAAx] ap2 constantF p a ≐ a :=
  GaussianNameRingLaws.constant_parameter_at p a
theorem constant_regular (a : PTm n) : Γ ⊢[PRAAx] pointCN constantF a :=
  GaussianNameRingLaws.constant_parameter_regular a

theorem raw_at (f : PR 2) (p a x : PTm n) : Γ ⊢[PRAAx] ap2 (rawF f) p (rawData a x) ≐ rawValue f p a x := by
  simpa [rawF, rawData] using
    (toPR_pair_eq (Γ := Γ) (rawValue f (var 0) (var 1) (var 2)) p a x)

theorem raw_regularity (f : PR 2) (s t A a x : PTm n) (h : Γ ⊢[PRAAx] input f A a x) : Γ ⊢[PRAAx]
    distanceBounded (rawValue f s a x) (rawValue f t a x) (A*(unit s+unit t)) (unit s*unit t) :=
  bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ zero (unit s+unit t) (unit s*unit t) (GaussianNameBounds.U f x) A
      (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t))
      (GaussianRationalPowerDifference.distance_refl_zero _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t)))
      (GaussianNameEquivalence.point_at f x s t h.andE₁) (GaussianNameBounds.sample_bound f x s h.andE₁) h.andE₂)

theorem raw_name_regular (f : PR 2) (A a x : PTm n) (h : Γ ⊢[PRAAx] input f A a x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (rawF f) A (rawData a x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := distance_congr (raw_at f (var 1) _ _).eqSymm (raw_at f (var 0) _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (raw_regularity f (var 1) (var 0) _ _ _ hs)
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_rawData,unit] using bound

theorem name_regular (f : PR 2) (A a x : PTm n) (h : Γ ⊢[PRAAx] input f A a x) : Γ ⊢[PRAAx] pointCN (nameF f) (data A a x) :=
  GaussianFastValueCut.name_fast (rawF f) A (rawData a x) (raw_name_regular f A a x h)
theorem sample_at (f : PR 2) (p A a x : PTm n) : Γ ⊢[PRAAx] sample f p A a x ≐ qmul a (ap2 f (clock p A) x) :=
  (GaussianFastValueCut.name_at (rawF f) A (rawData a x) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at f (clock p A) a x)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem normalized_error (f : PR 2) (p A a x : PTm n) (h : Γ ⊢[PRAAx] input f A a x) : Γ ⊢[PRAAx]
    distanceBounded (sample f p A a x)
      (ap2 (GaussianNameArithmetic.multiplyF constantF f) p (GaussianNameArithmetic.multiplyData constantF f a x)) (cost f A a x) (unit p) := by
  have first := distance_congr (.eqRefl _) (raw_at f p a x) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample (rawF f) A (rawData a x) p (raw_name_regular f A a x h))
  have second := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p a) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF f a x p (constant_regular a) h.andE₁)
  exact bound_congr (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first (distance_symmetric _ _ _ _ (unit_positive p) second))

theorem diagonal_envelope (f : PR 2) (A a x : PTm n) (h : Γ ⊢[PRAAx] input f A a x) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal (nameF f) (GaussianNameArithmetic.multiplyF constantF f)
      (data A a x) (GaussianNameArithmetic.multiplyData constantF f a x) (cost f A a x) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift A) (Syn.shift a) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_data,subst_cost,
    GaussianNameArithmetic.subst_multiplyData,sample,unit] using
      normalized_error f (var 0) (Syn.shift A) (Syn.shift a) (Syn.shift x) hs

theorem ordinary_product_identity (f : PR 2) (A a x : PTm n) (h : Γ ⊢[PRAAx] input f A a x) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (GaussianNameArithmetic.multiplyF constantF f)
      (data A a x) (GaussianNameArithmetic.multiplyData constantF f a x) :=
  GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ _ (name_regular f A a x h)
    (GaussianNameArithmetic.multiply_fast constantF f a x (constant_regular a) h.andE₁) (diagonal_envelope f A a x h)

theorem actual_uniform_clock_constant_product_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))
theorem actual_uniform_clock_constant_product_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample f (var 0) (var 1) (var 2) (var 3) ≐ qmul (var 2) (ap2 f (clock (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (sample_at f _ _ _ _)
theorem actual_uniform_clock_is_ordinary_constant_product_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) (var 2) ⟶ crossEquivalent (nameF f) (GaussianNameArithmetic.multiplyF constantF f)
      (data (var 0) (var 1) (var 2)) (GaussianNameArithmetic.multiplyData constantF f (var 1) (var 2))) :=
  closeUniv 3 (.impI (ordinary_product_identity f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBoundedConstantProductName
