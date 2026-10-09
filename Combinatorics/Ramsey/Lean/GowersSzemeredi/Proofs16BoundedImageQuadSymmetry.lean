import GowersSzemeredi.Proofs16RelationWordImages

/-! The bounded-image quadruple family has the three abstract BSG
symmetries. These are automatic for the actual local-map defect and its
common domain; weak transitivity is a separate structural input. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem finite_image_neg_card {V H : Type*} [AddGroup H] [DecidableEq H]
    (D : Finset V) (f : V → H) :
    (D.image (fun y => -f y)).card = (D.image f).card := by
  have he : D.image (fun y => -f y) = (D.image f).image Neg.neg := by
    simp only [Finset.image_image, Function.comp_def]
  rw [he]
  exact Finset.card_image_of_injective _ neg_injective

theorem columnQuadImageRelation_symm1 {N M : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N) (r : Real)
    {a b c d : ZMod N} (h : ColumnQuadImageRelation T F r M a b c d) :
    ColumnQuadImageRelation T F r M c d a b := by
  have hdom : columnQuadCommonDomain T r c d a b = columnQuadCommonDomain T r a b c d := by
    ext y
    simp only [columnQuadCommonDomain, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hdef : columnQuadDefect F c d a b = fun y => -columnQuadDefect F a b c d y := by
    funext y
    unfold columnQuadDefect
    ring
  unfold ColumnQuadImageRelation at h ⊢
  rw [hdom, hdef, finite_image_neg_card]
  exact h

theorem columnQuadImageRelation_symm2 {N M : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N) (r : Real)
    {a b c d : ZMod N} (h : ColumnQuadImageRelation T F r M a b c d) :
    ColumnQuadImageRelation T F r M b a d c := by
  have hdom : columnQuadCommonDomain T r b a d c = columnQuadCommonDomain T r a b c d := by
    ext y
    simp only [columnQuadCommonDomain, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hdef : columnQuadDefect F b a d c = fun y => -columnQuadDefect F a b c d y := by
    funext y
    unfold columnQuadDefect
    ring
  unfold ColumnQuadImageRelation at h ⊢
  rw [hdom, hdef, finite_image_neg_card]
  exact h

theorem columnQuadImageRelation_symm3 {N M : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N) (r : Real)
    {a b c d : ZMod N} (h : ColumnQuadImageRelation T F r M a b c d) :
    ColumnQuadImageRelation T F r M a c b d := by
  have hdom : columnQuadCommonDomain T r a c b d = columnQuadCommonDomain T r a b c d := by
    ext y
    simp only [columnQuadCommonDomain, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hdef : columnQuadDefect F a c b d = columnQuadDefect F a b c d := by
    funext y
    unfold columnQuadDefect
    ring
  unfold ColumnQuadImageRelation at h ⊢
  rw [hdom, hdef]
  exact h

/-- The concrete relation levels use powers of one image bound. -/
def boundedImageQuadFamily {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N)
    (r : Real) (M : Nat) (i : Nat) (a b c d : ZMod N) : Prop :=
  ColumnQuadImageRelation T F r (M^i) a b c d

theorem boundedImageQuadFamily_symmetries {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N)
    (r : Real) (M : Nat) :
    (∀ i a b c d, boundedImageQuadFamily T F r M i a b c d →
      boundedImageQuadFamily T F r M i c d a b) ∧
    (∀ i a b c d, boundedImageQuadFamily T F r M i a b c d →
      boundedImageQuadFamily T F r M i b a d c) ∧
    (∀ i a b c d, boundedImageQuadFamily T F r M i a b c d →
      boundedImageQuadFamily T F r M i a c b d) := by
  exact ⟨fun _ _ _ _ _ h => columnQuadImageRelation_symm1 T F r h,
    fun _ _ _ _ _ h => columnQuadImageRelation_symm2 T F r h,
    fun _ _ _ _ _ h => columnQuadImageRelation_symm3 T F r h⟩

end LeanProofs.GowersSzemeredi
