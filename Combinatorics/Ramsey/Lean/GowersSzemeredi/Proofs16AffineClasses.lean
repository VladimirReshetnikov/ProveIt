import GowersSzemeredi.Proofs16ClassDeletion

/-! # Disjoint affine classes from a fibrewise graph cover -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Assign each covered point to one of its covering graphs. The resulting
classes form a disjoint partition, even when the graphs overlap. -/
theorem finite_graph_cover_partition {X Y : Type*} [DecidableEq X]
    {q : Nat} (hq : 0 < q) (B : Finset X) (f : X → Y) (ell : Fin q → X → Y)
    (hcover : ∀ x ∈ B, ∃ i, f x = ell i x) :
    ∃ C : Fin q → Finset X, IsPartition C B ∧
      ∀ i x, x ∈ C i → f x = ell i x := by
  let label : X → Fin q := fun x => if hx : x ∈ B then (hcover x hx).choose else ⟨0, hq⟩
  refine ⟨fun i => B.filter (fun x => label x = i),
    ⟨fun x => ⟨fun hx => ⟨label x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩,
      fun ⟨_, hi⟩ => (Finset.mem_filter.mp hi).1⟩,
    fun i j hij => Finset.disjoint_left.mpr fun x hi hj =>
      bne_iff_ne.mp hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)⟩,
    fun i x hx => ?_⟩
  obtain ⟨hxB, rfl⟩ := Finset.mem_filter.mp hx
  simpa only [label, dif_pos hxB] using (hcover x hxB).choose_spec

/-- The same construction works on a finite column space embedded in the
field, as required for a progression J smaller than the full modulus. -/
theorem affine_column_cover_partition {N q : Nat} [NeZero N]
    {α : Type*} [DecidableEq α] (coord : α → ZMod N)
    (hq : 0 < q) (B : Finset α) (f : α → ZMod N)
    (ell : Fin q → ZMod N → ZMod N) (hell : ∀ i, LinearOn Finset.univ (ell i))
    (hcover : ∀ x ∈ B, ∃ i, f x = ell i (coord x)) :
    ∃ C : Fin q → Finset α, IsPartition C B ∧
      ∀ i, ∃ a b : ZMod N, ∀ x ∈ C i, f x = a * coord x + b := by
  obtain ⟨C, hpart, hC⟩ :=
    finite_graph_cover_partition hq B f (fun i x => ell i (coord x)) hcover
  refine ⟨C, hpart, ?_⟩
  intro i
  obtain ⟨a, b, hab⟩ := hell i
  exact ⟨a, b, fun x hx => (hC i x hx).trans (hab (coord x) (Finset.mem_univ _))⟩

end LeanProofs.GowersSzemeredi
