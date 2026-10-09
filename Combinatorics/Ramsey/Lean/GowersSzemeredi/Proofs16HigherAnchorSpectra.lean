import GowersSzemeredi.Proofs16SelectedColumnExtensions
import GowersSzemeredi.Proofs16JointFrequencySelection

/-! Rewrite the sixteen-column containment as a common sum domain for
four pairs of anchor maps. The selected Bohr domain has the same union. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higherLeftFrequencies_eq_pair_union {N : Nat}
    (T : ZMod N → Finset (ZMod N)) (p : HigherArrangementParameter N) :
    higherLeftFrequencies T (higherArrangementEndpoints p) =
      Finset.univ.biUnion (fun j : Fin 4 => columnDifferenceSpectrum T
        (higherArrangementEndpointPair p (Fin.castAdd 4 j))) := by
  ext x
  simp [higherLeftFrequencies,eightFrequencyUnion,columnDifferenceSpectrum,
    higherArrangementEndpointPair,higherArrangementPairLeft,higherArrangementPairRight,
    Fin.exists_fin_succ,Fin.succ,Fin.castAdd,or_assoc]

theorem higherRightFrequencies_eq_pair_union {N : Nat}
    (T : ZMod N → Finset (ZMod N)) (p : HigherArrangementParameter N) :
    higherRightFrequencies T (higherArrangementEndpoints p) =
      Finset.univ.biUnion (fun j : Fin 4 => columnDifferenceSpectrum T
        (higherArrangementEndpointPair p (Fin.natAdd 4 j))) := by
  ext x
  simp [higherRightFrequencies,eightFrequencyUnion,columnDifferenceSpectrum,
    higherArrangementEndpointPair,higherArrangementPairLeft,higherArrangementPairRight,
    Fin.exists_fin_succ,Fin.succ,Fin.natAdd,or_assoc]

theorem higherSelectedPairFrequencies_eq_anchor_union {N : Nat}
    (F : (ZMod N × ZMod N) → Finset (ZMod N)) (p : HigherArrangementParameter N) :
    higherSelectedPairFrequencies F p = Finset.univ.biUnion (fun j : Fin 4 =>
      F (higherArrangementEndpointPair p (Fin.castAdd 4 j)) ∪
      F (higherArrangementEndpointPair p (Fin.natAdd 4 j))) := by
  ext x
  simp [higherSelectedPairFrequencies,Fin.exists_fin_succ,Fin.succ,Fin.castAdd,Fin.natAdd]
  tauto

end LeanProofs.GowersSzemeredi
