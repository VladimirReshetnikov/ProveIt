import GowersSzemeredi.Proofs16MultilinearProduct
import GowersSzemeredi.Proofs13CommonStepCover

/-! Translation preserves proper boxes, partitions, and all quantitative
multiple-linearity controls. This transports the all-ones vertex graph back
to a subgraph of the original relation in the closing induction.

`MultiplyLinear.translate` and `MultiplyLinearFunction.translate` are in
`Proofs16TranslationsSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem IsMultilinear.translate {N k : Nat} [NeZero N] [Fact N.Prime]
    {phi : Point N k → ZMod N} (h : IsMultilinear phi) (t : Point N k) :
    IsMultilinear (fun x => phi (x + t)) := by
  apply isMultilinear_of_coordinate_linear
  intro y j
  obtain ⟨a, b, hab⟩ := h.linearOn_coordinate (y + t) j
  refine ⟨a, a * t j + b, fun x _ => ?_⟩
  have heq : replaceCoordinate y j x + t = replaceCoordinate (y + t) j (x + t j) := by
    funext i
    by_cases hi : i = j
    · subst i; simp [replaceCoordinate]
    · simp [replaceCoordinate, Function.update_of_ne hi]
  change phi (replaceCoordinate y j x + t) = _
  rw [heq]
  have hh := hab (x + t j) (Finset.mem_univ _)
  change phi (replaceCoordinate (y + t) j (x + t j)) = _ at hh
  rw [hh]
  ring

def Box.translate {N k : Nat} (P : Box N k) (t : Point N k) : Box N k where
  axis i := (P.axis i).translateBy (t i)
  commonDiff := P.commonDiff
  axis_step i := P.axis_step i

theorem Box.IsProper.translate {N k : Nat} {P : Box N k}
    (h : P.IsProper) (t : Point N k) : (P.translate t).IsProper :=
  fun i => (P.axis i).translateBy_isProper (t i) (h i)

@[simp] theorem Box.translate_mem_carrier {N k : Nat} [NeZero N]
    (P : Box N k) (t x : Point N k) :
    x + t ∈ (P.translate t).carrier ↔ x ∈ P.carrier := by
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    Box.translate, ModAP.translateBy_carrier, translateFinset, Pi.add_apply]
  apply forall_congr'
  intro i
  simpa only [add_comm] using (add_right_injective (t i)).mem_finset_image (s := (P.axis i).carrier) (a := x i)

@[simp] theorem Box.translate_width {N k : Nat} (P : Box N k) (t : Point N k) :
    (P.translate t).width = P.width := by
  simp [Box.width, Box.translate, ModAP.translateBy]

theorem Box.translate_carrier {N k : Nat} [NeZero N] (P : Box N k) (t : Point N k) :
    (P.translate t).carrier = P.carrier.image (fun x => x + t) := by
  ext x
  obtain ⟨y, rfl⟩ := (Equiv.addRight t).surjective x
  change y + t ∈ (P.translate t).carrier ↔ y + t ∈ _
  rw [Box.translate_mem_carrier]
  exact ((add_left_injective t).mem_finset_image).symm

@[simp] theorem Box.translate_card {N k : Nat} [NeZero N] (P : Box N k) (t : Point N k) :
    (P.translate t).carrier.card = P.carrier.card := by
  rw [Box.translate_carrier, Finset.card_image_of_injective _ (add_left_injective t)]

@[simp] theorem Box.translate_neg {N k : Nat} (P : Box N k) (t : Point N k) :
    (P.translate t).translate (-t) = P := by
  cases P
  simp only [Box.translate, ModAP.translateBy]
  congr 1
  funext i
  simp

@[simp] theorem Box.translate_neg' {N k : Nat} (P : Box N k) (t : Point N k) :
    (P.translate (-t)).translate t = P := by
  simpa using P.translate_neg (-t)

theorem IsBoxPartition.translate {N k m : Nat} [NeZero N]
    {Q : Fin m → Box N k} {P : Box N k} (h : IsBoxPartition Q P) (t : Point N k) :
    IsBoxPartition (fun j => (Q j).translate t) (P.translate t) := by
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := (Equiv.addRight t).surjective x
    change y + t ∈ (P.translate t).carrier ↔ ∃ i, y + t ∈ ((Q i).translate t).carrier
    simpa only [Box.translate_mem_carrier] using h.1 y
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨z, rfl⟩ := (Equiv.addRight t).surjective x
    exact Finset.disjoint_left.mp (h.2 i j hij)
      ((Box.translate_mem_carrier _ _ _).mp hx) ((Box.translate_mem_carrier _ _ _).mp hy)

end LeanProofs.GowersSzemeredi
