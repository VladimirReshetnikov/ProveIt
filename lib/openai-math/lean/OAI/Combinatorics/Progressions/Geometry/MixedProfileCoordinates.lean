import OAI.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedProfileFromCoordinates {d : ℕ} {α : Type*} (x : Fin (d + 3) → α) :
    (Fin (d + 1) → α) × α :=
  (Fin.cons (x 0) (fun j => x j.succ.succ.succ), x 2)

def mixedProfileEquiv (d : ℕ) (α : Type*) :
    (((Fin (d + 1) → α) × α) × α) ≃ (Fin (d + 3) → α) where
  toFun t := Fin.cons (t.1.1 0) (Fin.cons t.2 (Fin.cons t.1.2 (Fin.tail t.1.1)))
  invFun x := (mixedProfileFromCoordinates x, x 1)
  left_inv := by
    rintro ⟨⟨t, u⟩, n⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        exact Fin.cases rfl (fun _ => rfl) i
      · rfl
    · rfl
  right_inv := by
    intro x
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun _ => rfl) k

theorem mixedProfileFromCoordinates_independent {d : ℕ} {α : Type*}
    (x y : Fin (d + 3) → α) (h : ∀ k, k ≠ 1 → x k = y k) :
    mixedProfileFromCoordinates x = mixedProfileFromCoordinates y := by
  have h1 : (1 : Fin (d + 3)).val = 1 := Fin.val_one (d + 1)
  have h2 : (2 : Fin (d + 3)).val = 2 := by
    change 2 % (d + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h 0 (by
        intro e
        have he := congrArg Fin.val e
        norm_num only [Fin.val_zero, h1] at he)
    · exact h j.succ.succ.succ (by
        intro e
        have he := congrArg Fin.val e
        simp only [Fin.val_succ, h1] at he
        omega)
  · exact h 2 (by
      intro e
      have he := congrArg Fin.val e
      norm_num only [h2, h1] at he)

theorem mixedProfileFromCoordinates_point {d N : ℕ} [NeZero N]
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    mixedProfileFromCoordinates (fun i => (mixedDifferencePoint t n i : ZMod N)) = t := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [mixedProfileFromCoordinates, mixedDifferencePoint, mixedDifferenceShifts]
  · change ((t.2.val : ℤ) : ZMod N) = t.2
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem mixedProfileEquiv_point {d N : ℕ}
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
    (fun i => ((mixedProfileEquiv d (ZMod N) (t, n) i).val : ℤ)) =
      mixedDifferencePoint t (n.val : ℤ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun _ => rfl) k

theorem mixedProfile_sum_cast {d N : ℕ} [NeZero N]
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
    ((∑ i, mixedDifferencePoint t (n.val : ℤ) i : ℤ) : ZMod N) =
      ∑ i, mixedProfileEquiv d (ZMod N) (t, n) i := by
  rw [← mixedProfileEquiv_point]
  simp only [Int.cast_sum, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem mixedProfile_average {d : ℕ} {α : Type*} [Fintype α]
    (F : (Fin (d + 3) → α) → ℂ) :
    (𝔼 x, F x) = 𝔼 t : (Fin (d + 1) → α) × α, 𝔼 n : α,
      F (mixedProfileEquiv d α (t, n)) := by
  calc
    _ = 𝔼 t : ((Fin (d + 1) → α) × α) × α, F (mixedProfileEquiv d α t) :=
      (Fintype.expect_equiv (mixedProfileEquiv d α) _ F (fun _ => rfl)).symm
    _ = _ := expect_prod_split _

theorem mixedProfile_card (d N : ℕ) [NeZero N] :
    Fintype.card ((Fin (d + 1) → ZMod N) × ZMod N) = N ^ (d + 2) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, pow_succ]

end Erdos3

end

end OAI
