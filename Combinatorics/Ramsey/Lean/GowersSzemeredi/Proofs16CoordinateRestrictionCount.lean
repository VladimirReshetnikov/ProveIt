import GowersSzemeredi.Proofs16ShiftAnchorMaps

/-! Prescribing values at distinct coordinates leaves exactly the
functions on the complementary coordinates. This supplies the counting
measure needed for one globally consistent choice of anchors. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coordinateRestrictionFiberEquiv {I J V : Type*} (a : J → I) (ha : Function.Injective a) (v : J → V) :
    {f : I → V // ∀ j, f (a j) = v j} ≃ ({i : I // i ∉ Set.range a} → V) where
  toFun f i := f.val i.val
  invFun u := ⟨fun i => if h : i ∈ Set.range a then v (Classical.choose h) else u ⟨i,h⟩,by
    intro j
    dsimp only
    have hj : a j ∈ Set.range a := ⟨j,rfl⟩
    rw [dif_pos hj]
    exact congrArg v (ha (Classical.choose_spec hj))⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    dsimp only
    by_cases hi : i ∈ Set.range a
    · rw [dif_pos hi]
      have h := f.property (Classical.choose hi)
      rw [Classical.choose_spec hi] at h
      exact h.symm
    · rw [dif_neg hi]
  right_inv u := by
    funext i
    dsimp only
    rw [dif_neg i.property]

theorem coordinate_restriction_fiber_card {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype V]
    (a : J → I) (ha : Function.Injective a) (v : J → V) :
    ((Finset.univ : Finset (I → V)).filter fun f => ∀ j, f (a j) = v j).card =
      Fintype.card V ^ (Fintype.card I-Fintype.card J) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (coordinateRestrictionFiberEquiv a ha v),Fintype.card_fun,
    Fintype.card_subtype_compl]
  rw [← Fintype.card_congr (Equiv.ofInjective a ha)]

/-- Multiplication by the number of assignments on the prescribed
coordinates recovers the number of all functions, with no division. -/
theorem coordinate_restriction_fiber_balance {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype V]
    (a : J → I) (ha : Function.Injective a) (v : J → V) :
    (((Finset.univ : Finset (I → V)).filter fun f => ∀ j, f (a j) = v j).card) *
      Fintype.card V ^ Fintype.card J = Fintype.card (I → V) := by
  rw [coordinate_restriction_fiber_card a ha v,← pow_add,
    Nat.sub_add_cancel (Fintype.card_le_of_injective a ha),Fintype.card_fun]

end LeanProofs.GowersSzemeredi
