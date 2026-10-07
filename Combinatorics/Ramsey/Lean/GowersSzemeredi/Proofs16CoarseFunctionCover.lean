import GowersSzemeredi.Proofs16BoundedChunks
import GowersSzemeredi.Proofs16GlobalGraphCover

/-! Uniform coarse covers for arbitrary functions on proper boxes.
These handle small scales in ambient-dimension lifting without discarding
any points or relying on the partial function's structure. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem Box.card_le_pow_of_axis_card_le {N k n : Nat} [NeZero N]
    (P : Box N k) (h : ∀ i, (P.axis i).carrier.card ≤ n) : P.carrier.card ≤ n ^ k := by
  classical
  have heq : P.carrier = Fintype.piFinset (fun i => (P.axis i).carrier) := by
    ext x
    simp [Box.carrier]
  rw [heq, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin k, n := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => h i)
    _ = _ := by simp

/-- Cells of side lengths two or three admit a uniform family of at most
3^k constant multilinear graphs, covering any function exactly. -/
theorem section16_coarse_function_cover {N k : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (hk : 0 < k) (hw : 2 ≤ P.width)
    (phi : Point N k → ZMod N) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin (3 ^ k) → Point N k → ZMod N,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper ∧ 2 ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → ∃ i, phi x = mu j i x := by
  classical
  obtain ⟨M, Q, hpart, hproper, haxes, _⟩ := P.bounded_partition hP hk 2 (by omega) hw
  have hcard (j : Fin M) : (Q j).carrier.card ≤ 3 ^ k := by
    apply (Q j).card_le_pow_of_axis_card_le
    intro i
    rw [(hproper j).1 i]
    have hh := (haxes j i).2
    omega
  let e := fun j : Fin M => (Q j).carrier.equivFin.symm
  let mu := fun j : Fin M => fun i : Fin (3 ^ k) => fun _x : Point N k =>
    if hi : (i : Nat) < (Q j).carrier.card then phi ((e j) ⟨i, hi⟩).val else 0
  refine ⟨M, Q, mu, hpart, hproper, fun j i => isMultilinear_constant _, ?_⟩
  intro j x hx
  let a := (e j).symm ⟨x, hx⟩
  let i : Fin (3 ^ k) := ⟨a.val, a.isLt.trans_le (hcard j)⟩
  refine ⟨i, ?_⟩
  have hi : (i : Nat) < (Q j).carrier.card := a.isLt
  dsimp only [mu]
  rw [dif_pos hi]
  have ha : (⟨i.val, hi⟩ : Fin (Q j).carrier.card) = a := rfl
  rw [ha]
  simp [a]

/-- Width targets at most one admit a single constant graph on each
singleton cell, with no exceptional points and in every positive dimension. -/
theorem section16_singleton_function_cover {N k : Nat} [NeZero N]
    (P : Box N k) (hk : 0 < k) (phi : Point N k → ZMod N) :
    ∃ M : Nat, ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin 1 → Point N k → ZMod N,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper ∧ (Q j).width = 1) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → ∃ i, phi x = mu j i x := by
  classical
  obtain ⟨M, x, hpart⟩ := box_singleton_partition P
  refine ⟨M, fun j => pointSingletonBox (x j), fun j _ _ => phi (x j), hpart,
    fun j => ⟨pointSingletonBox_isProper _, pointSingletonBox_width hk _⟩,
    fun _ _ => isMultilinear_constant _, ?_⟩
  intro j z hz
  have hz' : z = x j := by simpa using hz
  exact ⟨0, by rw [hz']⟩

end LeanProofs.GowersSzemeredi
