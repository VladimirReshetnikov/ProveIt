import IPRADerivations.Analysis.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.GaussianNamedReciprocalFrozenRate
import IPRADerivations.Analysis.GaussianBoundedInverseApartness

/-!
# The named one-step backward Gamma construction

For a named argument in the original right half-plane and an apartness
certificate for its difference from one, the computed inverse of that
difference multiplies the original named Gamma. The exact multiplication
recovers the original Gamma at the supplied positive argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaBackwardShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qzero)
open GaussianRationalMetric (qsub)
open GaussianRationalReciprocal (qone)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one_left)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameReciprocal (apart)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def negativeOne : PTm n := qsub qzero qone
abbrev minusOneF (f : PR 2) : PR 2 := addF f constantF
def minusOneData (x : PTm n) : PTm n := addData x negativeOne

def source (f : PR 2) (x A a : PTm n) : Fm PTm n :=
  GaussianNamedRightHalfPlane.source f x A ⋏ apart (minusOneF f) a (minusOneData x)

abbrev reciprocalF (f : PR 2) : PR 2 := GaussianNameReciprocal.nameF (minusOneF f)
def reciprocalData (x a : PTm n) : PTm n := GaussianNameReciprocal.nameData a (minusOneData x)

abbrev nameF (f : PR 2) : PR 2 := multiplyF (reciprocalF f) (GaussianNamedGamma.nameF f)
def data (f : PR 2) (x A a : PTm n) : PTm n :=
  multiplyData (reciprocalF f) (GaussianNamedGamma.nameF f) (reciprocalData x a) (GaussianNamedGamma.data x A)

@[simp] theorem subst_minusOneData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (minusOneData x) = minusOneData (Syn.subst σ x) := by simp [minusOneData,negativeOne]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A a : PTm n) :
    (source f x A a).subst σ = source f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ a) := by simp [source]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A a : PTm n) :
    Syn.subst σ (data f x A a) = data f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ a) := by simp [data,reciprocalData]

theorem minus_one_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (minusOneF f) p (minusOneData x) ≐
      qadd (ap2 f (GaussianEulerNamedShiftInput.clock p) x) negativeOne :=
  GaussianNamedGammaHalfShift.add_constant_at f x negativeOne p

theorem minus_one_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (minusOneF f) (minusOneData x) :=
  add_fast _ _ _ _ h (constant_regular _)

theorem reciprocal_input (f : PR 2) (x A a : PTm n) (hs : Γ ⊢[PRAAx] source f x A a) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input (minusOneF f) a (minusOneData x) :=
  .andI (minus_one_regular f x hs.andE₁.andE₁) hs.andE₂

theorem name_regular (f : PR 2) (x A a : PTm n) (hs : Γ ⊢[PRAAx] source f x A a) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x A a) :=
  multiply_fast _ _ _ _ (GaussianNameReciprocal.name_fast _ _ _ (reciprocal_input f x A a hs).andE₁ hs.andE₂)
    (GaussianNamedGamma.name_regular f x A hs.andE₁)

theorem shifted_product (f : PR 2) (x A a : PTm n) (hs : Γ ⊢[PRAAx] source f x A a) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (minusOneF f) (nameF f)) (GaussianNamedGamma.nameF f)
      (multiplyData (minusOneF f) (nameF f) (minusOneData x) (data f x A a)) (GaussianNamedGamma.data x A) := by
  let W := minusOneF f
  let I := reciprocalF f
  let G := GaussianNamedGamma.nameF f
  let w := minusOneData x
  let i := reciprocalData x a
  let g := GaussianNamedGamma.data x A
  have hw := minus_one_regular f x hs.andE₁.andE₁
  have hi := GaussianNameReciprocal.name_fast W a w hw hs.andE₂
  have hg := GaussianNamedGamma.name_regular f x A hs.andE₁
  have product := GaussianNameReciprocal.product_one W a w hw hs.andE₂
  have corrected := cross_trans (multiplyF W I) oneF oneF (multiplyData W I w i) w g product
    (GaussianBoundedInverseApartness.ones_equivalent w g)
  have transported := multiply_cross (multiplyF W I) oneF G G (multiplyData W I w i) g g g
    (multiply_fast W I w i hw hi) (one_fast g) hg hg corrected (cross_refl G g hg)
  have assoc := multiply_associative W I G w i g hw hi hg
  exact cross_trans (multiplyF W (nameF f)) (multiplyF (multiplyF W I) G) G _ _ _
    (cross_symm _ _ _ _ assoc)
    (cross_trans (multiplyF (multiplyF W I) G) (multiplyF oneF G) G _ _ _ transported (multiply_one_left G g hg))

theorem actual_named_backward_Gamma_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ crossEquivalent (multiplyF (minusOneF f) (nameF f))
        (GaussianNamedGamma.nameF f)
        (multiplyData (minusOneF f) (nameF f) (minusOneData (var 0)) (data f (var 0) (var 1) (var 2)))
        (GaussianNamedGamma.data (var 0) (var 1))) :=
  closeUniv 3 (.impI (shifted_product f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaBackwardShift
