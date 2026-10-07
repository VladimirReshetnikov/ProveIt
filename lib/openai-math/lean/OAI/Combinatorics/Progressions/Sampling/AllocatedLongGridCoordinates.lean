import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

def allocatedLongIntegerCoordinate : output → Prop
  | ⟨⟨⟨_, .inl _⟩, _⟩, _⟩ => False
  | ⟨⟨⟨_, .inr _⟩, _⟩, _⟩ => True

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}

def allocatedLongIntegerSelect : integerOutput ↪ output :=
  ⟨Subtype.val, Subtype.val_injective⟩

omit [∀ j, Fintype (O j)] in
theorem allocatedLongIntegerSelect_range (q : output) :
    q ∈ Set.range (allocatedLongIntegerSelect B U basis S (O := O)) ↔
      allocatedLongIntegerCoordinate B U basis S q := by
  constructor
  · rintro ⟨z, hz⟩
    exact hz ▸ z.property
  · intro hq
    exact ⟨⟨q, hq⟩, rfl⟩

def allocatedLongRealIndex (j : Fin m) (i : I j)
    (ha : ¬grid ⟨j, .inl i⟩) (o : O j) :
    UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) :=
  ⟨⟨⟨⟨j, .inl i⟩, ha⟩, o⟩, by
    rw [allocatedLongIntegerSelect_range]
    exact fun h => h⟩

def allocatedLongIntegerIndex (j : Fin m) (i : Fin (n j))
    (ha : ¬grid ⟨j, .inr i⟩) (o : O j) : integerOutput :=
  ⟨⟨⟨⟨j, .inr i⟩, ha⟩, o⟩, True.intro⟩

noncomputable def allocatedLongCoordinateScale : output → ℝ
  | ⟨⟨⟨_, .inl _⟩, _⟩, _⟩ => 1
  | ⟨⟨⟨j, .inr i⟩, _⟩, _⟩ => (basisAxisScale (basis j) i : ℝ)

noncomputable def allocatedLongLatticeScale (q : integerOutput) : ℝ :=
  allocatedLongCoordinateScale B U basis S q.val

noncomputable def allocatedLongRowsFromGrid
    (v : UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ)
    (k : integerOutput → ℤ) : AllocatedLongJetRows B U basis S O
  | ⟨⟨j, .inl i⟩, ha⟩ => fun o => v (allocatedLongRealIndex B U basis S j i ha o)
  | ⟨⟨j, .inr i⟩, ha⟩ => fun o => k (allocatedLongIntegerIndex B U basis S j i ha o)

theorem allocatedLongRowsFromGrid_realCoordinates
    (v : UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ)
    (k : integerOutput → ℤ) :
    allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k) =
      selectedCoefficientEquiv (allocatedLongIntegerSelect B U basis S (O := O)) ℝ
        (v, rectangularLatticePoint (fun _ => 0) (allocatedLongLatticeScale B U basis S) k) := by
  apply selectedCoefficientEquiv_eq_of_coordinates
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · rfl
    · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · exact False.elim hq
    · change (k (allocatedLongIntegerIndex B U basis S j i ha o) : ℝ) /
        (basisAxisScale (basis j) i : ℝ) =
        ((k (allocatedLongIntegerIndex B U basis S j i ha o) : ℝ) - 0) /
          (basisAxisScale (basis j) i : ℝ)
      rw [sub_zero]

end Erdos3.VectorPolynomial

end

end OAI
