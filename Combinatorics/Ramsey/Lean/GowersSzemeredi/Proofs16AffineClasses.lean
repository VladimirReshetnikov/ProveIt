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
  classical
  let label : X → Fin q := fun x =>
    if hx : x ∈ B then (hcover x hx).choose else ⟨0, hq⟩
  let C : Fin q → Finset X := fun i => B.filter (fun x => label x = i)
  refine ⟨C, ⟨?_, ?_⟩, ?_⟩
  · intro x
    constructor
    · intro hx
      exact ⟨label x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_filter.mp hi).1
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    have hei := (Finset.mem_filter.mp hi).2
    have hej := (Finset.mem_filter.mp hj).2
    exact (bne_iff_ne.mp hij) (hei.symm.trans hej)
  · intro i x hx
    obtain ⟨hxB, hlabel⟩ := Finset.mem_filter.mp hx
    have hchosen : f x = ell (label x) x := by
      dsimp [label]
      rw [dif_pos hxB]
      exact (hcover x hxB).choose_spec
    simpa only [hlabel] using hchosen

/-- Every fibrewise affine graph cover can be partitioned into affine
classes without increasing the number of graphs. -/
theorem affine_graph_cover_partition {N q : Nat} [NeZero N]
    (hq : 0 < q) (B : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (ell : Fin q → ZMod N → ZMod N) (hell : ∀ i, LinearOn Finset.univ (ell i))
    (hcover : ∀ x ∈ B, ∃ i, f x = ell i x) :
    ∃ C : Fin q → Finset (ZMod N), IsPartition C B ∧ ∀ i, LinearOn (C i) f := by
  obtain ⟨C, hpart, hC⟩ := finite_graph_cover_partition hq B f ell hcover
  refine ⟨C, hpart, ?_⟩
  intro i
  obtain ⟨a, b, hab⟩ := hell i
  exact ⟨a, b, fun x hx => (hC i x hx).trans (hab x (Finset.mem_univ _))⟩

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
