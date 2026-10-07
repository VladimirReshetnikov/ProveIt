import GowersSzemeredi.Proofs13FejerSurvival

/-! When the only simultaneous relations are diagonal frequency pairs, the
mean Fejer survival is exactly the zero-frequency contribution. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem fejerRelation_count_diagonal {N L : Nat}
    {I : Type*} [Fintype I] [DecidableEq I] (phi feature : I → ZMod N)
    (hvalid : ∀ v : I → Fin L × Fin L,
      (fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) ↔
        ∀ i, (v i).1 = (v i).2) :
    countWhere (fun v : I → Fin L × Fin L =>
      fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) = L ^ Fintype.card I := by
  classical
  let V := {v : I → Fin L × Fin L //
    fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0}
  let e : V ≃ (I → Fin L) :=
    { toFun := fun v i => (v.1 i).1
      invFun := fun w => ⟨fun i => (w i, w i), (hvalid _).mpr (fun _ => rfl)⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext i
        exact Prod.ext rfl ((hvalid v.1).mp v.2 i)
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card V := by
      simp only [V, countWhere, Fintype.card_subtype]
      congr 1
      ext v
      simp
    _ = Fintype.card (I → Fin L) := Fintype.card_congr e
    _ = _ := by simp

theorem fejer_kernel_mean_diagonal {N L : Nat} [NeZero N]
    {I : Type*} [Fintype I] [DecidableEq I]
    (hL : 0 < L) (phi feature : I → ZMod N)
    (hvalid : ∀ v : I → Fin L × Fin L,
      (fejerPairRelation v phi = 0 ∧ fejerPairRelation v feature = 0) ↔
        ∀ i, (v i).1 = (v i).2) :
    (𝔼 c : ZMod N × ZMod N,
      ∏ i, finiteFejerKernel L (c.1 * phi i + c.2 * feature i)) =
        ((L : Real)⁻¹) ^ Fintype.card I := by
  have hLr : (L : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  rw [finiteFejerKernel_mean_product_real, fejerRelation_count_diagonal phi feature hvalid, Nat.cast_pow]
  rw [← mul_pow]
  congr 1
  field_simp

end LeanProofs.GowersSzemeredi
