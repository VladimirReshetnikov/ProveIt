import GowersSzemeredi.Proofs16HigherEscapingFrequencySelection
import GowersSzemeredi.Proofs16HigherArrangementCommonPairMaps
import GowersSzemeredi.Proofs16SmallImageRelations

/-! Relate sixteen-column frequency data to the eleven-parameter
arrangement model and identify the Bohr unions with column intersections. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mem_bohr_higherLeftFrequencies {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (p : Fin 16 → ZMod N) (rho : Real) (x : ZMod N) :
    x ∈ bohr (higherLeftFrequencies T p) rho ↔ ∀ i : Fin 8, x ∈ bohr (T (p (Fin.castAdd 8 i))) rho :=
  mem_bohr_family_union _ rho x

theorem mem_bohr_higherRightFrequencies {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (p : Fin 16 → ZMod N) (rho : Real) (x : ZMod N) :
    x ∈ bohr (higherRightFrequencies T p) rho ↔ ∀ i : Fin 8, x ∈ bohr (T (p (Fin.natAdd 8 i))) rho :=
  mem_bohr_family_union _ rho x

theorem higherFrequencyEquation_endpoints_iff {N : Nat}
    (f : Fin 16 → ZMod N → ZMod N) (p : HigherArrangementParameter N) :
    HigherFrequencyEquation (fun i => f i (higherArrangementEndpoints p i)) ↔ HigherArrangementEquation f p := Iff.rfl

theorem higherLeftFrequencyValue_endpoints_eq {N : Nat}
    (f : Fin 16 → ZMod N → ZMod N) (p : HigherArrangementParameter N) :
    higherLeftFrequencyValue (fun i => f i (higherArrangementEndpoints p i)) =
      ∑ j : Fin 4, higherArrangementPairValue f p (Fin.castAdd 4 j) := by
  rw [Fin.sum_univ_four]
  rfl

def higherLeftPairMapValue {N : Nat} (theta : Fin 8 → PairFrequencyMap N)
    (p : HigherArrangementParameter N) : ZMod N :=
  ∑ j : Fin 4, (theta (Fin.castAdd 4 j)).toFun (higherArrangementPairDifference p (Fin.castAdd 4 j))

theorem higherLeftPairMapValue_eq_frequency {N : Nat}
    (f : Fin 16 → ZMod N → ZMod N) (theta : Fin 8 → PairFrequencyMap N)
    (p : HigherArrangementParameter N)
    (hvalue : ∀ j, (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j) :
    higherLeftPairMapValue theta p = higherLeftFrequencyValue (fun i => f i (higherArrangementEndpoints p i)) := by
  unfold higherLeftPairMapValue
  simp_rw [hvalue]
  exact (higherLeftFrequencyValue_endpoints_eq f p).symm

end LeanProofs.GowersSzemeredi
