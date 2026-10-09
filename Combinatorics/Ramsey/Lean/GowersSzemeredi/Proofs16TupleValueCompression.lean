import GowersSzemeredi.Proofs16GlobalColumnTupleClasses

/-! Exact tuple classes bound the number of values at any point common
to the retained column domains. No common spectrum for all models is used. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem finite_class_value_image_card_le {I H K : Type*} [Inhabited H] [DecidableEq H]
    (A : Finset I) (J : Finset K) (f : I → H) (classOf : I → K)
    (hclass : ∀ a ∈ A, classOf a ∈ J)
    (hvalue : ∀ a ∈ A, ∀ b ∈ A, classOf a = classOf b → f a = f b) :
    (A.image f).card ≤ J.card := by
  let value : K → H := fun j => if hj : ∃ a ∈ A, classOf a = j then f hj.choose else default
  have hcover : ∀ a ∈ A, value (classOf a) = f a := by
    intro a ha
    have hex : ∃ b ∈ A, classOf b = classOf a := ⟨a, ha, rfl⟩
    dsimp only [value]
    rw [dif_pos hex]
    exact hvalue hex.choose hex.choose_spec.1 a ha hex.choose_spec.2
  have hsub : A.image f ⊆ J.image value := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨classOf a, hclass a ha, hcover a ha⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem columnAnchorFibre_mono {N k : Nat} [NeZero N]
    {V P : Finset (ZMod N)} (hVP : V ⊆ P) (c : ZMod N) :
    columnAnchorFibre V k c ⊆ columnAnchorFibre P k c := by
  intro a ha
  obtain ⟨_, hV, hvalue⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => hVP (hV x hx), hvalue⟩

/-- The tuple values at a common point occupy at most one value per class. -/
theorem column_tuple_value_image_card_le {N k : Nat} [NeZero N]
    (P V : Finset (ZMod N)) (hVP : V ⊆ P) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (t : Real) (y c : ZMod N)
    (J : Finset (ColumnAnchorTuple N k)) (classOf : ColumnAnchorTuple N k → ColumnAnchorTuple N k)
    (hclass : ∀ a ∈ columnAnchorFibre P k c, classOf a ∈ J)
    (hpair : ∀ a ∈ columnAnchorFibre P k c, ∀ b ∈ columnAnchorFibre P k c,
      classOf a = classOf b → ColumnListIdentity T L t (columnAnchorList a) (columnAnchorList b))
    (hy : ∀ x ∈ V, y ∈ bohr (T x) t) :
    ((columnAnchorFibre V k c).image
      (fun a => columnAnchorEval (fun x => L x y) (columnAnchorList a))).card ≤ J.card := by
  apply finite_class_value_image_card_le _ J _ classOf
    (fun a ha => hclass a (columnAnchorFibre_mono hVP c ha))
  intro a ha b hb heq
  exact hpair a (columnAnchorFibre_mono hVP c ha) b (columnAnchorFibre_mono hVP c hb) heq y
    (fun x hx => hy x ((Finset.mem_filter.mp ha).2.1 x hx))
    (fun x hx => hy x ((Finset.mem_filter.mp hb).2.1 x hx))

end LeanProofs.GowersSzemeredi
