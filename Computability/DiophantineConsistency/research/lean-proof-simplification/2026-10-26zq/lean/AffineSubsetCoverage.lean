import DiophantineConsistency.ControllerResidueLift
import RestrictedSubsetSums

/-! A Boolean-free arithmetic subset theorem for the existing affine weights.
The cardinality upper bound changes from a < C0 to a ≤ C0. This file proves
no statement about safe physical placement or the final Diophantine equation.
The original coordinate lift and additive map are imported unchanged from
ProveIt commit 9f35798db4a63c25e435fca14d75931144657d7e. -/
namespace NewControllerProofs.AffineSubsetCoverage

open DiophantineConsistency.ControllerResidueLift
open DiophantineConsistency.ControllerOrbitTransport
open scoped BigOperators

theorem scaledCoordinate_one (C0 T : ℕ) :
    scaledCoordinate C0 T 1 = (C0 : ZMod (C0*T)) := by
  simpa using scaledCoordinate_intCast C0 T (1 : ℤ)

/-- Replace the zero cardinality representative by C0 and subtract one
from the quotient coordinate. This endpoint is required, not optional. -/
theorem exists_positive_coordinate {C0 T : ℕ} [NeZero C0] [NeZero T]
    (t : ZMod (C0*T)) :
    ∃ a : ℕ, 0 < a ∧ a ≤ C0 ∧ ∃ u : ZMod T,
      t = (a : ZMod (C0*T)) + scaledCoordinate C0 T u := by
  let phi : ZMod (C0*T) →+* ZMod C0 :=
    ZMod.castHom (dvd_mul_right C0 T) (ZMod C0)
  let a0 : ℕ := (phi t).val
  have ha0 : a0 < C0 := ZMod.val_lt (phi t)
  have hproject : phi t = (a0 : ZMod C0) := (ZMod.natCast_zmod_val (phi t)).symm
  obtain ⟨u, hu⟩ := exists_coordinate t a0 ha0 hproject
  have ht : t = (a0 : ZMod (C0*T)) + scaledCoordinate C0 T u := by
    simpa only [scaledCoordinate_val] using hu
  by_cases hzero : a0 = 0
  · refine ⟨C0, NeZero.pos C0, le_rfl, u-1, ?_⟩
    have ht0 : t = scaledCoordinate C0 T u := by simpa only [hzero, Nat.cast_zero, zero_add] using ht
    rw [ht0, map_sub, scaledCoordinate_one]
    abel
  · exact ⟨a0, Nat.pos_of_ne_zero hzero, ha0.le, u, ht⟩

/-- Every residue is reached by one actual subset of the affine orbit.
No prime, prime-power, coprime-cardinality, extra weight, or Boolean bit is
required. The coordinate-map injection and C0 < T remain explicit inputs. -/
theorem exists_subset_affine_target {C0 T : ℕ} [NeZero C0] [NeZero T]
    {α : Type*} [DecidableEq α] (hCT : C0 < T)
    (index : ZMod T → α) (hinj : Function.Injective index)
    (weight : α → ZMod (C0*T))
    (hw : ∀ z, weight (index z) =
      1 + (C0 : ZMod (C0*T)) * (z.val : ZMod (C0*T)))
    (t : ZMod (C0*T)) :
    ∃ a : ℕ, ∃ s : Finset α,
      0 < a ∧ a ≤ C0 ∧ s.card = a ∧ (∑ x ∈ s, weight x) = t := by
  obtain ⟨a, ha, haC, u, ht⟩ := exists_positive_coordinate t
  obtain ⟨s, hsCard, hsSum⟩ :=
    AdditionalSimplifications.RestrictedSubsetSums.exists_subset_card_sum
      ha (haC.trans_lt hCT) u
  refine ⟨a, s.image index, ha, haC, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, hsCard]
  · rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    have hw' (z : ZMod T) : weight (index z) = 1 + scaledCoordinate C0 T z := by
      rw [scaledCoordinate_val]
      exact hw z
    simp_rw [hw']
    rw [Finset.sum_add_distrib, Finset.sum_const, hsCard, ← map_sum, hsSum]
    simpa only [nsmul_one] using ht.symm

-- Composite modulus, nonunit cardinality: all eight target residues are
-- represented with one or two of the odd affine weights 1,3,5,7.
example (t : ZMod (2*4)) : ∃ a : ℕ, ∃ s : Finset (ZMod 4),
    0 < a ∧ a ≤ 2 ∧ s.card = a ∧
      (∑ x ∈ s, (1 + 2*(x.val : ZMod (2*4)))) = t :=
  exists_subset_affine_target (by decide) id Function.injective_id
    (fun x => 1 + 2*(x.val : ZMod (2*4))) (fun _ => rfl) t

#print axioms exists_positive_coordinate
#print axioms exists_subset_affine_target

end NewControllerProofs.AffineSubsetCoverage
