import DiophantineConsistency.ControllerIntervalSums

/-!
# Transporting constructed interval subsets through affine coordinates

The coordinate injection and its affine weight formula are explicit hypotheses.
This module constructs the target-dependent finite subset; it does not assert
that any particular power sequence has these orbit coordinates.
-/

namespace DiophantineConsistency.ControllerOrbitTransport

open ControllerIntervalSums
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

variable {T : ℕ} {α R : Type*} [DecidableEq α]

/-- The actual domain subset is the image of the explicitly constructed interval. -/
def targetSubset (e : ZMod T → α) (a : ℕ) (h : Nat.Coprime a T) (u : ZMod T) :
    Finset α := (targetInterval a h u).image e

theorem targetSubset_card [NeZero T] (e : ZMod T → α) (he : Function.Injective e)
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    (targetSubset e a h u).card = a := by
  rw [targetSubset,Finset.card_image_of_injective _ he,targetInterval_card a h ha u]

/-- No target-subset witness is supplied. An additive coordinate formula is
enough to transport the constructed interval, including wrap at zero. -/
theorem targetSubset_sum [NeZero T] [AddCommMonoid R]
    (e : ZMod T → α) (he : Function.Injective e) (weight : α → R)
    (b : R) (L : ZMod T →+ R) (hw : ∀ z, weight (e z) = b+L z)
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    (∑ x ∈ targetSubset e a h u, weight x) = a • b+L u := by
  rw [targetSubset,Finset.sum_image (fun _ _ _ _ hh => he hh)]
  simp_rw [hw]
  rw [Finset.sum_add_distrib,Finset.sum_const,targetInterval_card a h ha u,
    ← map_sum,targetInterval_sum a h ha u]

theorem exists_subset_affine_sum [NeZero T] [AddCommMonoid R]
    (e : ZMod T → α) (he : Function.Injective e) (weight : α → R)
    (b : R) (L : ZMod T →+ R) (hw : ∀ z, weight (e z) = b+L z)
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    ∃ s : Finset α, s.card = a ∧ (∑ x ∈ s, weight x) = a • b+L u :=
  ⟨targetSubset e a h u,targetSubset_card e he a h ha u,
    targetSubset_sum e he weight b L hw a h ha u⟩

/-- Multiplication by C0 descends from integers modulo T to integers modulo
C0*T. It remains defined for C0=0; then it is the zero map into ZMod0. -/
def scaledCoordinate (C0 T : ℕ) : ZMod T →+ ZMod (C0*T) :=
  ZMod.lift T ⟨(AddMonoidHom.mulLeft (C0 : ZMod (C0*T))).comp
      (Int.castAddHom (ZMod (C0*T))), by
    change (C0 : ZMod (C0*T))*((T : ℤ) : ZMod (C0*T)) = 0
    rw [Int.cast_natCast,← Nat.cast_mul,ZMod.natCast_self]⟩

theorem scaledCoordinate_intCast (C0 T : ℕ) (z : ℤ) :
    scaledCoordinate C0 T (z : ZMod T) = (C0 : ZMod (C0*T))*(z : ZMod (C0*T)) := by
  exact ZMod.lift_coe T _ z

theorem scaledCoordinate_val [NeZero T] (C0 : ℕ) (z : ZMod T) :
    scaledCoordinate C0 T z = (C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  simpa only [Int.cast_natCast] using scaledCoordinate_intCast C0 T (z.val : ℤ)

theorem scaledCoordinate_zero (T : ℕ) (z : ZMod T) : scaledCoordinate 0 T z = 0 := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
  simp only [scaledCoordinate_intCast,Nat.cast_zero,zero_mul]

/-- The exact ordinary affine residue, with no positivity requirement on C0. -/
theorem targetSubset_modular_sum [NeZero T]
    (C0 : ℕ) (e : ZMod T → α) (he : Function.Injective e)
    (weight : α → ZMod (C0*T))
    (hw : ∀ z, weight (e z) = 1+(C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)))
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    (∑ x ∈ targetSubset e a h u, weight x) =
      (a : ZMod (C0*T))+(C0 : ZMod (C0*T))*(u.val : ZMod (C0*T)) := by
  have hf (z : ZMod T) : weight (e z) = 1+scaledCoordinate C0 T z := by
    rw [scaledCoordinate_val]
    exact hw z
  simpa only [nsmul_one,scaledCoordinate_val] using
    targetSubset_sum e he weight 1 (scaledCoordinate C0 T) hf a h ha u

/-- Integer weights need only satisfy the affine coordinate formula modulo
C0*T; their ordinary sum then has the promised congruence. -/
theorem targetSubset_integer_sum [NeZero T]
    (C0 : ℕ) (e : ZMod T → α) (he : Function.Injective e) (weight : α → ℤ)
    (hw : ∀ z, (weight (e z) : ZMod (C0*T)) =
      1+(C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)))
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    (∑ x ∈ targetSubset e a h u, weight x) ≡
      (a : ℤ)+(C0 : ℤ)*(u.val : ℤ) [ZMOD (C0*T : ℕ)] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ (C0*T)).mp
  simpa only [Int.cast_sum,Int.cast_add,Int.cast_mul,Int.cast_natCast] using
    targetSubset_modular_sum C0 e he (fun x => (weight x : ZMod (C0*T))) hw a h ha u

theorem exists_subset_integer_sum [NeZero T]
    (C0 : ℕ) (e : ZMod T → α) (he : Function.Injective e) (weight : α → ℤ)
    (hw : ∀ z, (weight (e z) : ZMod (C0*T)) =
      1+(C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)))
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    ∃ s : Finset α, s.card = a ∧
      (∑ x ∈ s, weight x) ≡ (a : ℤ)+(C0 : ℤ)*(u.val : ℤ) [ZMOD (C0*T : ℕ)] :=
  ⟨targetSubset e a h u,targetSubset_card e he a h ha u,
    targetSubset_integer_sum C0 e he weight hw a h ha u⟩

end DiophantineConsistency.ControllerOrbitTransport
