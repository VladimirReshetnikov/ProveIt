import OAI.Combinatorics.Progressions.Lattices.CubeResidueSupport

namespace OAI

section

namespace Erdos3

def shiftScalarCube {I : Type*} (c : ℤ) (x : Option I → ℤ) : Option I → ℤ
  | none => c + x none
  | some i => x (some i)

def shiftScalarCubeResidues {I : Type*} (c : ℤ) (m : Option I → ℕ)
    (r : ∀ i, ZMod (m i)) : ∀ i, ZMod (m i)
  | none => r none - (c : ZMod (m none))
  | some i => r (some i)

theorem shiftScalarCube_value {I : Type*} [Fintype I]
    (c : ℤ) (x : Option I → ℤ) (t : Finset I) :
    integerScalarCubeValue (shiftScalarCube c x) t = c + integerScalarCubeValue x t := by
  simp only [integerScalarCubeValue, shiftScalarCube, add_assoc]

theorem shiftScalarCube_residues_iff {I : Type*} (c : ℤ) (m : Option I → ℕ)
    (r : ∀ i, ZMod (m i)) (x : Option I → ℤ) :
    (∀ i, ((shiftScalarCube c x i : ℤ) : ZMod (m i)) = r i) ↔
      ∀ i, ((x i : ℤ) : ZMod (m i)) = shiftScalarCubeResidues c m r i := by
  constructor
  · intro h i
    cases i with
    | none => simpa [shiftScalarCube, shiftScalarCubeResidues, eq_sub_iff_add_eq, add_comm] using h none
    | some i => exact h (some i)
  · intro h i
    cases i with
    | none => simpa [shiftScalarCube, shiftScalarCubeResidues, eq_sub_iff_add_eq, add_comm] using h none
    | some i => exact h (some i)

def supportedCubeCoordinates {q : ℕ} (p : (Fin q → ℤ) × ℤ) : Option (Fin q) → ℤ
  | none => p.2
  | some i => p.1 i

def supportedIntervalTranslateEquiv (q K : ℕ) (c : ℤ) :
    SupportedCube q (Set.Ico (0 : ℤ) (K : ℤ)) ≃
      SupportedCube q (Set.Ico c (c + K)) where
  toFun p := ⟨(p.val.1, c + p.val.2), fun ω => by
    have h := p.property ω
    change 0 ≤ p.val.2 + cubeShift p.val.1 ω ∧ p.val.2 + cubeShift p.val.1 ω < K at h
    change c ≤ c + p.val.2 + cubeShift p.val.1 ω ∧
      c + p.val.2 + cubeShift p.val.1 ω < c + K
    constructor <;> omega⟩
  invFun p := ⟨(p.val.1, p.val.2 - c), fun ω => by
    have h := p.property ω
    change c ≤ p.val.2 + cubeShift p.val.1 ω ∧ p.val.2 + cubeShift p.val.1 ω < c + K at h
    change 0 ≤ p.val.2 - c + cubeShift p.val.1 ω ∧
      p.val.2 - c + cubeShift p.val.1 ω < K
    constructor <;> omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp

noncomputable def shiftedScalarCubeEquiv (q K : ℕ) (c : ℤ) :
    ↥(integerScalarCubeSet (Fin q) K) ≃ SupportedCube q (Set.Ico c (c + K)) :=
  (integerScalarCubeEquiv q K).trans (supportedIntervalTranslateEquiv q K c)

theorem shiftedScalarCubeEquiv_coordinates (q K : ℕ) (c : ℤ)
    (x : ↥(integerScalarCubeSet (Fin q) K)) :
    supportedCubeCoordinates (shiftedScalarCubeEquiv q K c x).val =
      shiftScalarCube c (fun i => (x.val i : ℤ)) := by
  funext i
  cases i <;> rfl

end Erdos3

end

end OAI
