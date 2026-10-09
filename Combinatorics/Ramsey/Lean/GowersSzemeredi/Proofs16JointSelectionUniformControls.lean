import GowersSzemeredi.Proofs16JointFrequencySelection

/-! The finite list of nine possible controls gives uniform progression
rank and positive density bounds without a monotonicity assumption. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def jointControlParameter (delta : Real) (d : Nat) (r : Real) (i : Fin 9) : Real :=
  Fin.cases (escapingFreimanDensity delta d r)
    (fun j : Fin 8 => (higherArrangementPairDensity (higherEscapeCoordinateDensity delta d r) j)^2) i

def jointMapRank (delta : Real) (d : Nat) (r : Real) : Nat :=
  Finset.univ.sup fun i : Fin 9 => commonDifferenceRank (jointControlParameter delta d r i)+1

def jointMapDensity (delta : Real) (d : Nat) (r : Real) : Real :=
  Finset.univ.inf' Finset.univ_nonempty fun i : Fin 9 =>
    commonDifferenceProgressionDensity (jointControlParameter delta d r i)

theorem jointMapDensity_pos (delta : Real) (d : Nat) (r : Real) : 0 < jointMapDensity delta d r := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i _
  exact commonDifferenceProgressionDensity_pos _

theorem PairFrequencyMap.JointControlled.control_index {N d : Nat} (g : PairFrequencyMap N)
    {delta r : Real} (h : g.JointControlled delta d r) :
    ∃ i : Fin 9, g.Controlled (jointControlParameter delta d r i) := by
  rcases h with h | ⟨n,hn,h⟩
  · exact ⟨0,h⟩
  · exact ⟨(⟨n,hn⟩ : Fin 8).succ,h⟩

theorem PairFrequencyMap.JointControlled.uniform_bounds {N d : Nat} (g : PairFrequencyMap N)
    {delta r : Real} (h : g.JointControlled delta d r) :
    g.progression.rank ≤ jointMapRank delta d r ∧ g.progression.Proper ∧
      jointMapDensity delta d r*N ≤ (g.progression.carrier.card : Real) ∧
      FreimanHom 2 g.domain g.toFun := by
  obtain ⟨i,hi⟩ := PairFrequencyMap.JointControlled.control_index g h
  have hrank : commonDifferenceRank (jointControlParameter delta d r i)+1 ≤ jointMapRank delta d r :=
    Finset.le_sup (f := fun j : Fin 9 => commonDifferenceRank (jointControlParameter delta d r j)+1)
      (Finset.mem_univ i)
  have hmass : jointMapDensity delta d r ≤ commonDifferenceProgressionDensity (jointControlParameter delta d r i) :=
    Finset.inf'_le (fun j : Fin 9 => commonDifferenceProgressionDensity (jointControlParameter delta d r j))
      (Finset.mem_univ i)
  exact ⟨hi.1.trans hrank,hi.2.1,
    (mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg N)).trans hi.2.2.1,hi.2.2.2⟩

end LeanProofs.GowersSzemeredi
