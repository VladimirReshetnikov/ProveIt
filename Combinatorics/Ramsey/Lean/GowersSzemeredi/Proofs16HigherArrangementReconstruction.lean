import GowersSzemeredi.Proofs16MappedQuadrupleCount

/-! Four matched anchor quadruples with additive shifts reconstruct a
higher arrangement without losing their individual column values. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementOfAnchorQuadruples {N : Nat} (q : Fin 4 → Fin 4 → ZMod N) :
    HigherArrangementParameter N :=
  ((q 0 0-q 0 1,![q 1 0-q 1 1,q 2 0-q 2 1,q 1 1,q 2 1,q 3 1,
    q 0 3,q 1 3,q 2 3,q 3 3]),q 0 1)

theorem higherArrangementAnchorQuadruple_eq {N : Nat} (p : HigherArrangementParameter N)
    (j : Fin 4) : higherArrangementAnchorQuadruple p j =
      ![(higherArrangementAnchorValues p j).1+higherArrangementShifts p j,
        (higherArrangementAnchorValues p j).1,
        (higherArrangementAnchorValues p j).2+higherArrangementShifts p j,
        (higherArrangementAnchorValues p j).2] := by
  fin_cases j <;> rfl

theorem higherArrangementOfAnchorQuadruples_shifts {N : Nat}
    (q : Fin 4 → Fin 4 → ZMod N)
    (hshift : (q 0 0-q 0 1)+(q 1 0-q 1 1) = (q 2 0-q 2 1)+(q 3 0-q 3 1))
    (j : Fin 4) : higherArrangementShifts (higherArrangementOfAnchorQuadruples q) j = q j 0-q j 1 := by
  fin_cases j
  · rfl
  · rfl
  · rfl
  · change (q 0 0-q 0 1)+(q 1 0-q 1 1)-(q 2 0-q 2 1) = q 3 0-q 3 1
    linear_combination hshift

theorem higherArrangementOfAnchorQuadruples_values {N : Nat}
    (q : Fin 4 → Fin 4 → ZMod N) (j : Fin 4) :
    higherArrangementAnchorValues (higherArrangementOfAnchorQuadruples q) j = (q j 1,q j 3) := by
  fin_cases j <;> rfl

theorem higherArrangementOfAnchorQuadruples_reconstruct {N : Nat}
    (q : Fin 4 → Fin 4 → ZMod N) (hquad : ∀ j, q j 0-q j 1 = q j 2-q j 3)
    (hshift : (q 0 0-q 0 1)+(q 1 0-q 1 1) = (q 2 0-q 2 1)+(q 3 0-q 3 1))
    (j : Fin 4) : higherArrangementAnchorQuadruple (higherArrangementOfAnchorQuadruples q) j = q j := by
  rw [higherArrangementAnchorQuadruple_eq,higherArrangementOfAnchorQuadruples_shifts q hshift,
    higherArrangementOfAnchorQuadruples_values]
  funext i
  fin_cases i
  · change q j 1+(q j 0-q j 1) = q j 0
    ring
  · rfl
  · change q j 3+(q j 0-q j 1) = q j 2
    linear_combination hquad j
  · rfl

theorem higherArrangement_endpoints_mem_of_anchor_quadruples {N : Nat}
    (W : Finset (ZMod N)) (p : HigherArrangementParameter N)
    (h : ∀ j i, higherArrangementAnchorQuadruple p j i ∈ W) :
    ∀ i, higherArrangementEndpoints p i ∈ W := by
  intro i
  fin_cases i
  · exact h 0 0
  · exact h 0 1
  · exact h 1 0
  · exact h 1 1
  · exact h 2 0
  · exact h 2 1
  · exact h 3 0
  · exact h 3 1
  · exact h 0 2
  · exact h 0 3
  · exact h 1 2
  · exact h 1 3
  · exact h 2 2
  · exact h 2 3
  · exact h 3 2
  · exact h 3 3

end LeanProofs.GowersSzemeredi
