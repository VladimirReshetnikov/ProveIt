import GowersSzemeredi.Proofs16AffineTupleRows
import GowersSzemeredi.Proofs16RobustRowFilling

/-! Reindex arbitrary finite frequency tuples for the existing pattern
row-filling theorems, preserving the actual frequency sets and graph. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The additive-quadruple formulation is the standard order-two Freiman
homomorphism property, including on empty domains. -/
theorem IsFreimanLinearOn.freimanHom {N : Nat} {B : Finset (ZMod N)} {L : ZMod N → ZMod N}
    (h : IsFreimanLinearOn B L) : FreimanHom 2 B L := by
  apply isAddFreimanHom_two.mpr
  refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
  intro a ha b hb c hc d hd heq
  exact h a b c d ha hb hc hd heq

def tuplePatternMaps {N : Nat} {κ : Type*} [Fintype κ] (L : κ → ZMod N → ZMod N) :
    Fin (Fintype.card κ) → ZMod N → ZMod N :=
  fun i => L ((Fintype.equivFin κ).symm i)

def tuplePatternIndices (k : Nat) : Fin 4 → Finset (Fin k) := fun _ => Finset.univ

/-- Reindexing retains exactly the varying frequencies, without padding. -/
theorem tuplePattern_frequencies {N : Nat} {κ : Type*} [Fintype κ]
    (L : κ → ZMod N → ZMod N) (y : ZMod N) :
    varyingPatternFrequencies (tuplePatternMaps L) (tuplePatternIndices (Fintype.card κ)) y =
      Finset.univ.image (fun j => L j y) := by
  ext z
  simp only [varyingPatternFrequencies, tuplePatternIndices, Finset.union_self,
    Finset.mem_image, Finset.mem_univ, true_and, tuplePatternMaps]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(Fintype.equivFin κ).symm i, hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨Fintype.equivFin κ j, by simpa using hj⟩

/-- The pattern and tuple graph indicators coincide pointwise. -/
theorem tuplePattern_edgeIndicator {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    (L : κ → ZMod N → ZMod N) (eta : Real) {F C : Finset (ZMod N)} (x : ↥F) (y : ↥C) :
    edgeIndicator (patternEdge (tuplePatternMaps L) (tuplePatternIndices (Fintype.card κ)) eta) x y =
      if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) eta then (1 : Real) else 0 := by
  unfold edgeIndicator patternEdge
  rw [tuplePattern_frequencies]
  by_cases h : (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) eta <;> simp [h]

end LeanProofs.GowersSzemeredi
