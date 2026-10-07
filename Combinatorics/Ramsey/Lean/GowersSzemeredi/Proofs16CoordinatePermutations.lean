import GowersSzemeredi.Proofs16FaceInduction

/-! Coordinate permutations preserve multilinear polynomials, proper boxes,
their widths, and box partitions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Reindex coordinates by precomposition. -/
def coordinateReindex {k : Nat} {A : Type*} (e : Fin k ≃ Fin k) :
    (Fin k → A) ≃ (Fin k → A) where
  toFun x i := x (e i)
  invFun x i := x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

@[simp] theorem coordinateReindex_apply {k : Nat} {A : Type*}
    (e : Fin k ≃ Fin k) (x : Fin k → A) (i : Fin k) :
    LeanProofs.GowersSzemeredi.coordinateReindex e x i = x (e i) := rfl

@[simp] theorem coordinateReindex_symm_apply {k : Nat} {A : Type*}
    (e : Fin k ≃ Fin k) (x : Fin k → A) :
    LeanProofs.GowersSzemeredi.coordinateReindex e.symm (LeanProofs.GowersSzemeredi.coordinateReindex e x) = x := by funext i; simp

theorem IsMultilinear.coordinateReindex {N k : Nat} {mu : Point N k → ZMod N}
    (h : IsMultilinear mu) (e : Fin k ≃ Fin k) :
    IsMultilinear (fun x => mu (LeanProofs.GowersSzemeredi.coordinateReindex e x)) := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨fun b => c (LeanProofs.GowersSzemeredi.coordinateReindex e b), ?_⟩
  intro x
  dsimp only
  rw [hc, ← (LeanProofs.GowersSzemeredi.coordinateReindex (A := Bool) e).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact e.prod_comp (fun i => if b i then x i else 1)

def Box.coordinateReindex {N k : Nat} (P : Box N k) (e : Fin k ≃ Fin k) : Box N k where
  axis i := P.axis (e i)
  commonDiff := P.commonDiff
  axis_step i := P.axis_step (e i)

theorem Box.IsProper.coordinateReindex {N k : Nat} {P : Box N k}
    (h : P.IsProper) (e : Fin k ≃ Fin k) : (P.coordinateReindex e).IsProper :=
  fun i => h (e i)

@[simp] theorem Box.coordinateReindex_mem_carrier {N k : Nat} [NeZero N]
    (P : Box N k) (e : Fin k ≃ Fin k) (x : Point N k) :
    LeanProofs.GowersSzemeredi.coordinateReindex e x ∈ (P.coordinateReindex e).carrier ↔
      x ∈ P.carrier := by
  classical
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    Box.coordinateReindex, coordinateReindex_apply]
  exact (e.surjective.forall (p := fun i => x i ∈ (P.axis i).carrier)).symm

theorem Box.coordinateReindex_carrier {N k : Nat} [NeZero N]
    (P : Box N k) (e : Fin k ≃ Fin k) :
    (P.coordinateReindex e).carrier = P.carrier.image (LeanProofs.GowersSzemeredi.coordinateReindex e) := by
  classical
  ext x
  obtain ⟨y, rfl⟩ := (LeanProofs.GowersSzemeredi.coordinateReindex e).surjective x
  rw [Box.coordinateReindex_mem_carrier]
  exact ((LeanProofs.GowersSzemeredi.coordinateReindex e).injective.mem_finset_image).symm

@[simp] theorem Box.coordinateReindex_card {N k : Nat} [NeZero N]
    (P : Box N k) (e : Fin k ≃ Fin k) : (P.coordinateReindex e).carrier.card = P.carrier.card := by
  rw [Box.coordinateReindex_carrier]
  exact Finset.card_image_of_injective _ (LeanProofs.GowersSzemeredi.coordinateReindex e).injective

@[simp] theorem Box.coordinateReindex_width {N k : Nat}
    (P : Box N k) (e : Fin k ≃ Fin k) : (P.coordinateReindex e).width = P.width := by
  classical
  have himage : Finset.univ.image (fun i => (P.axis (e i)).length) =
      Finset.univ.image (fun i => (P.axis i).length) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact (e.surjective.exists (p := fun i => (P.axis i).length = n)).symm
  unfold Box.width
  split_ifs with hk
  · rfl
  · simp only [Box.coordinateReindex, himage]

theorem IsBoxPartition.coordinateReindex {N k m : Nat} [NeZero N]
    {Q : Fin m → Box N k} {P : Box N k} (h : IsBoxPartition Q P)
    (e : Fin k ≃ Fin k) :
    IsBoxPartition (fun j => (Q j).coordinateReindex e) (P.coordinateReindex e) := by
  classical
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := (LeanProofs.GowersSzemeredi.coordinateReindex e).surjective x
    simpa only [Box.coordinateReindex_mem_carrier] using h.1 y
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y, rfl⟩ := (LeanProofs.GowersSzemeredi.coordinateReindex e).surjective x
    exact Finset.disjoint_left.mp (h.2 i j hij)
      ((Box.coordinateReindex_mem_carrier _ _ _).mp hx)
      ((Box.coordinateReindex_mem_carrier _ _ _).mp hy)

end LeanProofs.GowersSzemeredi
