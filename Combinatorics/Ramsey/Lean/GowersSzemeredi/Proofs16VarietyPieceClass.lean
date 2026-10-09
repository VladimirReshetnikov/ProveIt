import GowersSzemeredi.Proofs16JointVarietyCapBound
import GowersSzemeredi.Proofs16PartJSlices

/-! Variety pieces as a class of partial functions on two-dimensional
points. Finite families of class members have the joint polynomial cover.
The empty member permits uniform padding of extracted families.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem isVarietyPiece_empty {N : Nat} [NeZero N] (D : Nat) (c : Real)
    (hB : 0 ≤ milicevicBound D c) (phi : ZMod N × ZMod N → ZMod N) :
    IsVarietyPiece D c phi ∅ := by
  refine ⟨∅, ∅, 0, (fun i => Fin.elim0 i), Real.exp (-milicevicBound D c),
    0, 0, (fun _ => 0), ?_, ?_, ?_, le_rfl, ?_, ?_, ?_⟩
  · simpa using hB
  · simpa using hB
  · simpa using hB
  · intro i
    exact Fin.elim0 i
  · constructor <;> intros <;> simp
  · simp

/-- The variety-piece class in the coordinates used by the slice lift. -/
def section16VarietyPieceClass (N D : Nat) [NeZero N] (c : Real) :
    Set (Finset (Point N 2) × (Point N 2 → ZMod N)) :=
  {E | IsVarietyPiece D c (fun q => E.2 (pairPoint q)) (E.1.image fun x => (x 0, x 1))}

theorem IsVarietyPiece.mem_section16VarietyPieceClass {N D : Nat} [NeZero N]
    {c : Real} {A : Finset (ZMod N × ZMod N)} {phi : ZMod N × ZMod N → ZMod N}
    (h : IsVarietyPiece D c phi A) :
    (A.image pairPoint, fun x => phi (x 0, x 1)) ∈ section16VarietyPieceClass N D c := by
  simpa [section16VarietyPieceClass, Finset.image_image, Function.comp_def, pairPoint] using h

theorem empty_mem_section16VarietyPieceClass {N : Nat} [NeZero N] (D : Nat) (c : Real)
    (hB : 0 ≤ milicevicBound D c) :
    (∅, fun _ => 0) ∈ section16VarietyPieceClass N D c := by
  simpa [section16VarietyPieceClass] using isVarietyPiece_empty (N := N) D c hB (fun _ => 0)

/-- The statement of `exists_variety_piece_class_cover` at fixed constants. -/
def VarietyPieceClassCoverAt (C p : Nat) : Prop :=
  ∀ (N n D : Nat) [NeZero N] [Fact N.Prime] (c : Real), 0 < c → c ≤ 1 →
    ∀ E : Fin n → Finset (Point N 2) × (Point N 2 → ZMod N),
      (∀ i, E i ∈ section16VarietyPieceClass N D c) →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
      Gamma ⊆ section16FinsetUnion (fun i => partialGraph (E i).1 (E i).2) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16PolynomialJointVarietyExponent C p n D c) Gamma

/-- `exists_variety_piece_class_cover` at the constants of its input. -/
theorem varietyPieceClassCoverAt_of {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hcover : PolynomialVarietyPieceFamilyCoverAt C p) : VarietyPieceClassCoverAt C p := by
  classical
  unfold VarietyPieceClassCoverAt
  intro N n D _ _ c hc hc1 E hE Gamma hGamma
  apply (hcover N n D c hc hc1
    (fun i => (E i).1.image fun x : Point N 2 => (x 0, x 1))
    (fun i q => (E i).2 (pairPoint q)) (fun i => hE i)
    (fun i => partialGraph (E i).1 (E i).2) ?_).subset hGamma
  intro i z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨Finset.mem_image_of_mem _ hx, ?_⟩
  change (E i).2 x = (E i).2 (pairPoint (x 0, x 1))
  rw [pairPoint_coords]

/-- Arbitrary subrelations of finite unions of class members inherit the
same polynomial controls. No structure-extraction hypothesis occurs. -/
theorem exists_variety_piece_class_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N n D : Nat) [NeZero N] [Fact N.Prime] (c : Real), 0 < c → c ≤ 1 →
    ∀ E : Fin n → Finset (Point N 2) × (Point N 2 → ZMod N),
      (∀ i, E i ∈ section16VarietyPieceClass N D c) →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
      Gamma ⊆ section16FinsetUnion (fun i => partialGraph (E i).1 (E i).2) →
      MultiplyLinearWith (fun _ => 9 * n)
        (fun _ => section16PolynomialJointVarietyExponent C p n D c) Gamma := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_polynomial_variety_piece_family_cover
  exact ⟨C, p, hC, hp, varietyPieceClassCoverAt_of hC hp hcover⟩

end LeanProofs.GowersSzemeredi
