import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSquareCancellation
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference

/-!
# Recover the branch from equality of Gaussian named squares

An apartness certificate for the actual sum of the two names supplies
a lower bound for its late samples. Their literal sample sum is the
factor for rational square cancellation. An explicit observation rate
then gives equality of the original names at independent precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianNamedSquareBranch

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (add_sample unit_monotone)
open GaussianFastValueCut (exponent)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal diagonal_at point_at)
open GaussianNameRingLaws (equivalent_of_envelope multiply_sample_error)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalReciprocal (bound_congr bounded_product reciprocal reciprocal_identity qone)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianNameReciprocal (apart anchor R)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem rational_cancel (a b E K B : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hL : Γ ⊢[PRAAx] lower (qadd a b) one B)
    (h : Γ ⊢[PRAAx] distanceBounded (qmul a a) (qmul b b) E K) :
    Γ ⊢[PRAAx] distanceBounded a b (E*B) K := by
  let S := qadd a b
  let d := qsub a b
  let inv := reciprocal S
  have ib : Γ ⊢[PRAAx] bounded inv B one :=
    GaussianRationalLowerBounds.inverse_bound S one B (le_refl _) hB hL
  have si : Γ ⊢[PRAAx] qmul S inv ≐ qone :=
    reciprocal_identity S (GaussianNameReciprocal.lower_norm_positive S B hB hL)
  have hd : Γ ⊢[PRAAx] bounded (qmul d S) E K :=
    bound_congr (GaussianRationalSquareCancellation.difference_factorization a b) (.eqRefl _) (.eqRefl _) h
  have e : Γ ⊢[PRAAx] qmul (qmul d S) inv ≐ d :=
    (qmul_associative _ _ _).eqTrans ((qmul_congr (.eqRefl d) si).eqTrans
      (qmul_one_right d (GaussianRationalMetric.qsub_canonical a b)))
  exact bound_congr e (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ hK (le_refl _) hd ib)

def squareBudget (f g : PR 2) (x y : PTm n) : PTm n :=
  (((multiplyModulus f f x x+one)+two)+(multiplyModulus g g y y+one))

ipra_subst squareBudget

private theorem raw_squares (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) (multiplyF g g)
      (multiplyData f f x x) (multiplyData g g y y)) :
    Γ ⊢[PRAAx] distanceBounded (qmul (ap2 f p x) (ap2 f p x)) (qmul (ap2 g p y) (ap2 g p y))
      (squareBudget f g x y) (unit p) := by
  have pu := unit_positive (Γ := Γ) p
  have a := distance_symmetric _ _ _ _ pu (multiply_sample_error f f x x p hf hf)
  have b := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ hs)
  have c := multiply_sample_error g g y y p hg hg
  exact distance_triangle_same _ _ _ _ _ _ pu (distance_triangle_same _ _ _ _ _ _ pu a b) c

/-- Each original clock admits a checked error bound through one late sum
sample. The reciprocal factor is bounded by the explicit power of two R h. -/
theorem sample_distance (f g : PR 2) (x y h p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] apart (addF f g) h (addData x y))
    (hs : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) (multiplyF g g)
      (multiplyData f f x x) (multiplyData g g y y)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y)
      ((two+squareBudget f g x y*R h)+two) (unit p) := by
  let j := p+anchor h
  let k := exponent two j
  have hp := unit_positive (Γ := Γ) p
  have hk := unit_positive (Γ := Γ) k
  have pp : Γ ⊢[PRAAx] le p k := le_trans (le_add_right p (anchor h)) (le_add_right _ _)
  have grow := unit_monotone pp
  have lowerSum : Γ ⊢[PRAAx] lower (qadd (ap2 f k x) (ap2 g k y)) one (R h) :=
    GaussianRationalLowerBounds.lower_congr (add_sample f g x y j) (.eqRefl _) (.eqRefl _)
      (GaussianNameReciprocal.tail_lower (addF f g) h (addData x y) p (add_fast f g x y hf hg) ha)
  have raw := rational_cancel _ _ _ _ _ hk (GaussianNameReciprocal.R_positive h) lowerSum
    (raw_squares f g x y k hf hg hs)
  let A := squareBudget f g x y*R h
  have close : Γ ⊢[PRAAx] distanceBounded (ap2 f k x) (ap2 g k y) A (unit p) :=
    distance_radius_mono _ _ _ _ A (unit p) hk hp
      (le_congr (mul_comm (unit p) A) (mul_comm (unit k) A) (mul_le_mul_right A grow)) raw
  have den := GaussianRationalHorner.positive_product _ _ hp hk
  have cmp : Γ ⊢[PRAAx] le ((unit p+unit k)*unit p) (two*(unit p*unit k)) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (mul_le_mul_right (unit p) (add_le_add₂ grow (le_refl (unit k))))
  have left := distance_radius_mono _ _ _ _ two (unit p) den hp cmp (point_at f x p k hf)
  have right := distance_symmetric _ _ _ _ hp
    (distance_radius_mono _ _ _ _ two (unit p) den hp cmp (point_at g y p k hg))
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp left close) right

theorem equivalent_of_apart (f g : PR 2) (x y h : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] apart (addF f g) h (addData x y))
    (hs : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) (multiplyF g g)
      (multiplyData f f x x) (multiplyData g g y y)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  refine equivalent_of_envelope f g x y ((two+squareBudget f g x y*R h)+two) hf hg (.allI ?_)
  let sh := fun a : PTm n => Syn.shift a
  let Δ := Γ.map Fm.shift
  have f' : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift
  have g' : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hg.shift
  have a' : Δ ⊢[PRAAx] apart (addF f g) (sh h) (addData (sh x) (sh y)) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using ha.shift
  have s' : Δ ⊢[PRAAx] crossEquivalent (multiplyF f f) (multiplyF g g)
      (multiplyData f f (sh x) (sh x)) (multiplyData g g (sh y) (sh y)) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
  simpa only [Syn.shift,sh,PTm.subst_add,PTm.subst_mul,subst_squareBudget,
    GaussianNameReciprocal.subst_R,one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    using sample_distance f g (sh x) (sh y) (sh h) (var 0) f' g' a' s'

theorem actual_named_square_branch_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((pointCN f (var 0) ⋏ pointCN g (var 1)) ⟶
        apart (addF f g) (var 2) (addData (var 0) (var 1)) ⟶
        crossEquivalent (multiplyF f f) (multiplyF g g)
          (multiplyData f f (var 0) (var 0)) (multiplyData g g (var 1) (var 1)) ⟶
          crossEquivalent f g (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (.impI
    (equivalent_of_apart f g _ _ _ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedSquareBranch
