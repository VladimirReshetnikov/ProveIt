import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFactorialTaylor
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFrozen
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalTaylorAllOrderRadius

/-!
# Disk independence of the named Barnes factorial Taylor evaluator

Freeze the same input observation for both disk choices after both
input clocks. The exact rational radius identity compares the two
factorial names at that point, and the late input rates pay for the
two original observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorRadius

open_ipra
open GaussianBarnesCanonicalNamedDemand (source native_source)
open GaussianBarnesCanonicalNamedFactorialTaylor
  (clock data frozenData late_rate nameF regular retains sample_at subst_data)
open GaussianBarnesCanonicalNamedFrozen (source_widen)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal cross_trans diagonal_at)
open GaussianNamedInverseRate (diagonal_rate independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF

private theorem diagonal_small (a b t : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F F a b one (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F t a) (ap2 F t b) (num 3) (unit t) := by
  have ht := unit_positive (Γ := Γ) t
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht ht) ht
    (le_of_eq_add (d := zero) (by ipra_ring)) (diagonal_rate F F a b one (unit t) t ht h)

theorem observations (f : PR 2) (p x R S e : PTm n)
    (hr : Γ ⊢[PRAAx] source f x R) (hs : Γ ⊢[PRAAx] source f x S) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R e)) (ap2 (nameF f) p (data x S e))
      (num 4) (unit p) := by
  let t := succ p
  let a := clock p R e
  let b := clock p S e
  let k := a+b
  let q := ap2 f k x
  let A := frozenData f a x R e
  let A' := frozenData f k x R e
  let B' := frozenData f k x S e
  let B := frozenData f b x S e
  have sameInput := cross_refl f x hr.andE₁
  have left := diagonal_small A A' t (late_rate f f t a k x x R e hr hr sameInput (le_refl a) (le_add_right a b))
  have right := diagonal_small B' B t (late_rate f f t k b x x S e hs hs sameInput (le_add_left b a) (le_refl b))
  have same : Γ ⊢[PRAAx] crossEquivalent F F A' B' :=
    GaussianBarnesCanonicalTaylorAllOrderRadius.retained_cross (rawGaussian q) R S (rawDen q) e e
      (native_source f k x R hr) (native_source f k x S hs) (retains e)
  have middle := diagonal_at F F A' B' t (cross_to_diagonal F F A' B' same)
  have ht := unit_positive (Γ := Γ) t
  have raw := distance_triangle_same _ _ _ _ _ _ ht
    (distance_triangle_same _ _ _ _ _ _ ht left middle) right
  have ht' : Γ ⊢[PRAAx] unit t ≐ two*unit p :=
    (pw_succ two p).eqTrans (mul_comm _ _)
  have fit : Γ ⊢[PRAAx] le ((num 3+two+num 3)*unit p) (num 4*unit t) := by
    refine le_of_eq_add (d := zero) ((congrMul (.eqRefl (num 4)) ht').eqTrans ?_)
    ipra_ring
  exact distance_congr (sample_at f p x R e).eqSymm (sample_at f p x S e).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ ht (unit_positive p) fit raw)

theorem independent_radii (f : PR 2) (x R S e : PTm n)
    (hr : Γ ⊢[PRAAx] source f x R) (hs : Γ ⊢[PRAAx] source f x S) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data x R e) (data x S e) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4) (regular f x R e hr) (regular f x S e hs)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have r : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift
  have s : Δ ⊢[PRAAx] source f (sh x) (sh S) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_data,PTm.subst_num,Syn.shift,sh,Δ] using
    observations f (var 0) (sh x) (sh R) (sh S) (sh e) r s

theorem proper (f g : PR 2) (x y R S e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y S)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R e) (data y S e) := by
  let W := R+S
  have hf' := source_widen f x R W hf (le_add_right R S)
  have hg' := source_widen g y S W hg (le_add_left S R)
  exact cross_trans _ _ _ _ _ _ (independent_radii f x R W e hf hf')
    (cross_trans _ _ _ _ _ _ (GaussianBarnesCanonicalNamedFactorialTaylor.proper f g x y W e hf' hg' he)
      (independent_radii g y W S e hg' hg))

theorem actual_named_Barnes_factorial_Taylor_radius_independent_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 1) ⋏ source f (var 0) (var 2)) ⟶
        crossEquivalent (nameF f) (nameF f) (data (var 0) (var 1) (var 3)) (data (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (independent_radii f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_named_Barnes_factorial_Taylor_different_disk_proper_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 3)) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2) (var 4)) (data (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (proper f g _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorRadius
