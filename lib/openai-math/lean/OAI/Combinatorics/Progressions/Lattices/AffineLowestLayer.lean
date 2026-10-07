import OAI.Combinatorics.Progressions.Estimates.DependentPatchValue

namespace OAI

section

namespace Erdos3

namespace TriangularSlots

variable {D : ℕ}

noncomputable def affineBlock (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : ∀ i j, i ≤ j → M i j = 0) (P : Fin D → ℝ) : TriangularSlots D where
  center x := P + M.mulVec (x - P)
  lower i x y hxy := by
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j < i
    · simp only [Pi.sub_apply, hxy j hji]
    · simp [hM i j (le_of_not_gt hji)]

theorem affineBlock_residual (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : ∀ i j, i ≤ j → M i j = 0) (P : Fin D → ℝ) (b : Fin D → ℤ) :
    (affineBlock M hM P).residual b = (1 - M).mulVec ((fun i => (b i : ℝ)) - P) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp only [residual, affineBlock, Pi.sub_apply, Pi.add_apply]
  ring

end TriangularSlots

def shiftedIntegerBlock {T : Type*} {D : ℕ} (I : T → Fin D → ℤ)
    (t₀ : T) (b₀ : Fin D → ℤ) (t : T) : Fin D → ℤ := b₀ + I t - I t₀

@[simp] theorem shiftedIntegerBlock_at_base {T : Type*} {D : ℕ}
    (I : T → Fin D → ℤ) (t₀ : T) (b₀ : Fin D → ℤ) :
    shiftedIntegerBlock I t₀ b₀ t₀ = b₀ := by simp [shiftedIntegerBlock]

theorem affine_residual_shift_identity {T : Type*} {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ) (t₀ t : T) (b₀ : Fin D → ℤ) :
    (TriangularSlots.affineBlock M hM (P t)).residual (shiftedIntegerBlock I t₀ b₀ t) -
      (TriangularSlots.affineBlock M hM (P t₀)).residual b₀ =
    -(1 - M).mulVec ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ))) := by
  rw [TriangularSlots.affineBlock_residual, TriangularSlots.affineBlock_residual,
    ← Matrix.mulVec_sub, ← Matrix.mulVec_neg]
  congr 1
  ext i
  simp only [shiftedIntegerBlock, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Int.cast_sub, Int.cast_add]
  ring

theorem affine_residual_shift_dist {T : Type*} {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ) (t₀ t : T) (b₀ : Fin D → ℤ) :
    dist ((TriangularSlots.affineBlock M hM (P t)).residual (shiftedIntegerBlock I t₀ b₀ t))
      ((TriangularSlots.affineBlock M hM (P t₀)).residual b₀) =
    ‖(1 - M).mulVec ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ)))‖ := by
  rw [dist_eq_norm, affine_residual_shift_identity, norm_neg]

theorem freeze_affine_lowest_layer {T : Type*} {D E : ℕ}
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : ∀ i j, i ≤ j → M i j = 0)
    (P : T → Fin D → ℝ) (I : T → Fin D → ℤ)
    (B : T → (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (t₀ : T) (b₀ : Fin D → ℤ) {ε : ℝ}
    (hbase : ∀ i, |(TriangularSlots.affineBlock M hM (P t₀)).residual b₀ i| ≤ 1 / 4)
    (hε : ε < 1 / 12)
    (hosc : ∀ t, ‖(1 - M).mulVec
      ((P t - fun i => (I t i : ℝ)) - (P t₀ - fun i => (I t₀ i : ℝ)))‖ ≤ ε) :
    ∀ t, dist (((TriangularSlots.affineBlock M hM (P t)).append (B t)).patchValue Φ)
      ((B t (fun i => (shiftedIntegerBlock I t₀ b₀ t i : ℝ))).patchValue
        (Φ.freeze ((TriangularSlots.affineBlock M hM (P t₀)).residual b₀))) ≤ Φ.lip * ε := by
  intro t
  apply TriangularSlots.patchValue_freeze_prefix _ _ Φ _ _ hbase hε
  rw [affine_residual_shift_dist]
  exact hosc t

end Erdos3

end

end OAI
