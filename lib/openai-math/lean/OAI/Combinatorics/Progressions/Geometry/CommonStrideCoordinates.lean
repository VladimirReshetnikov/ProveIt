import OAI.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
import OAI.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i => integerProgressionSupport (c i) m (H i))

theorem commonStrideBox_card {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) {m : ℕ} (hm : 0 < m) (H : I → ℕ) :
    (commonStrideBox c m H).card = ∏ i, H i := by
  simp only [commonStrideBox, Fintype.card_piFinset, card_integerProgressionSupport _ _ _ hm]

theorem commonStrideBox_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) {m : ℕ} (hm : 0 < m) (H : I → ℕ) (hH : ∀ i, 0 < H i) :
    (commonStrideBox c m H).Nonempty := by
  apply Fintype.piFinset_nonempty.mpr
  intro i
  apply Finset.card_pos.mp
  simpa only [card_integerProgressionSupport _ _ _ hm] using hH i

theorem affine_interval_eq_progression (r m a b : ℕ) :
    (Finset.Ico (a : ℤ) (b : ℤ)).image (fun x => (r : ℤ) + m * x) =
      integerProgressionSupport ((r : ℤ) + m * a) m (b - a) := by
  by_cases hab : a ≤ b
  · have he : (a : ℤ) + (b - a : ℕ) = b := by omega
    rw [integerProgressionSupport_reindex, he]
  · have hi : Finset.Ico (a : ℤ) (b : ℤ) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp [Nat.sub_eq_zero_of_le (by omega : b ≤ a), hi, integerProgressionSupport, translateSupport]

theorem commonStrideBox_eq_image {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) :
    commonStrideBox c m H = (integerBox H).image (fun x i => c i + (m : ℤ) * x i) := by
  simp only [commonStrideBox, integerProgressionSupport, translateSupport, Finset.image_image]
  exact Fintype.piFinset_image (fun i x => c i + (m : ℤ) * x) (fun i => Finset.Ico (0 : ℤ) (H i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def commonStridePoint {I : Type*} (c : I → ℤ) (m : ℕ) (x : I → ℤ) : I → ℤ :=
  fun i => c i + (m : ℤ) * x i

def commonStrideIndex {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ) : I → ℤ :=
  fun i => (y i - c i) / (m : ℤ)

theorem commonStrideIndex_point {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m) (x : I → ℤ) :
    commonStrideIndex c m (commonStridePoint c m x) = x := by
  funext i
  simp only [commonStrideIndex, commonStridePoint, add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)

theorem commonStridePoint_injective {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m) :
    Function.Injective (commonStridePoint c m) :=
  Function.LeftInverse.injective (commonStrideIndex_point c hm)

theorem commonStridePoint_mem {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) {x : I → ℤ} (hx : x ∈ integerBox H) :
    commonStridePoint c m x ∈ commonStrideBox c m H := by
  rw [commonStrideBox_eq_image]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem integerAffineMap_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    (a s x : I → ℤ) :
    integerAffineMap (fun i j => if i = j then s i else 0) a x = fun i => a i + s i * x i := by
  funext i
  simp [integerAffineMap, ite_mul]

end Erdos3

end

end OAI
