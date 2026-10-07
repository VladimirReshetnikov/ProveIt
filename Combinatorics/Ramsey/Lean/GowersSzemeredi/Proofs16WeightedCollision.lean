import GowersSzemeredi.Proofs16MultilinearProduct

/-! Weighted collision energy with a support-sensitive Cauchy--Schwarz
bound. The weights may be arbitrary real numbers. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def weightedCollisionEnergy {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (f : X → Y) (w : X → Real) : Real :=
  ∑ a ∈ S, ∑ b ∈ S, if f a = f b then w a * w b else 0

/-- Collision energy is the sum of squared total weights in the fibres.
Only a finite set containing the image is needed. -/
theorem weightedCollisionEnergy_eq_sum_sq {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) (w : X → Real)
    (hmap : ∀ x ∈ S, f x ∈ T) :
    weightedCollisionEnergy S f w =
      ∑ y ∈ T, (∑ x ∈ S, if f x = y then w x else 0) ^ 2 := by
  classical
  symm
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : f a = f b
  · simp [← hab, hmap a ha]
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro y hy
    split_ifs with ha' hb' hb'
    · exact (hab (ha'.trans hb'.symm)).elim
    all_goals simp

/-- The squared total mass is bounded by the support cardinality times
collision energy, without any sign restriction on the original weights. -/
theorem weightedCollisionEnergy_mass_bound {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) (w : X → Real)
    (hmap : ∀ x ∈ S, f x ∈ T) :
    (∑ x ∈ S, w x) ^ 2 ≤ (T.card : Real) * weightedCollisionEnergy S f w := by
  classical
  have hsum : (∑ y ∈ T, ∑ x ∈ S, if f x = y then w x else 0) = ∑ x ∈ S, w x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simp [hmap x hx]
  have h := sq_sum_le_card_mul_sum_sq (s := T)
    (f := fun y => ∑ x ∈ S, if f x = y then w x else 0)
  rw [hsum, ← weightedCollisionEnergy_eq_sum_sq S T f w hmap] at h
  exact h

theorem weightedCollisionEnergy_nonneg {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (f : X → Y) (w : X → Real) :
    0 ≤ weightedCollisionEnergy S f w := by
  classical
  rw [weightedCollisionEnergy_eq_sum_sq S (S.image f) f w (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end LeanProofs.GowersSzemeredi
