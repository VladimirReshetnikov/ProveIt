import GowersSzemeredi.Proofs13FejerArrangementCounts

/-! Discharge the Fejer selection structural hypotheses for catalogue
arrangements outside the explicitly bounded exceptional family. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def fejerArrangementPositive (j : Option (Fin 15) × Bool) : Bool :=
  decide ((finSuccEquivLast.symm j.1 : Fin 16).val < 8) == j.2

theorem fejerArrangementPositive_coefficient {N : Nat} (j : Option (Fin 15) × Bool) :
    (if fejerArrangementPositive j then 1 else -1 : ZMod N) =
      balancedFeatureCoefficient fejerArrangementFreeSign j := by
  rcases j with ⟨j, b⟩
  obtain ⟨i, rfl⟩ := (finSuccEquivLast : Fin 16 ≃ Option (Fin 15)).surjective j
  rw [fejerArrangementCoefficient_reindex]
  by_cases hi : i.val < 8 <;> cases b <;>
    simp [fejerArrangementPositive, fejerArrangementSign, hi]

theorem fejerArrangement_regular_injective {N L : Nat} [NeZero N] [Fact N.Prime]
    (hL : 2 ≤ L) (R : FejerBalancedArrangement N)
    (hregular : R ∉ fejerExceptionalArrangements (L := L)) :
    Function.Injective (fejerArrangementVertex R.1) := by
  classical
  have hr : ¬ fejerFeatureExceptional (L := L) fejerArrangementFreeSign
      (fejerArrangementEncode R.1) := by
    simpa [fejerExceptionalArrangements] using hregular
  rw [fejerArrangementVertex_encode R.1 R.2]
  exact fejerFeature_regular_injective hL fejerArrangementFreeSign fejerArrangementFreeSign_ne_zero
    (fun i => R.1.x i.castSucc) (fun j => R.1.y (finSuccEquivLast.symm j)) R.1.height hr

theorem fejerArrangement_regular_diagonal {N L : Nat} [NeZero N] [Fact N.Prime]
    (hLN : L ≤ N) (R : FejerBalancedArrangement N) (phi : Pair N → ZMod N)
    (hregular : R ∉ fejerExceptionalArrangements (L := L)) (hbad : ¬ R.1.IsRespected phi) :
    ∀ v : (Option (Fin 15) × Bool) → Fin L × Fin L,
      (fejerPairRelation v (phi ∘ fejerArrangementVertex R.1) = 0 ∧
        fejerPairRelation v ((fun z => z.1 * z.2) ∘ fejerArrangementVertex R.1) = 0) ↔
        ∀ j, (v j).1 = (v j).2 := by
  classical
  have hr : ¬ fejerFeatureExceptional (L := L) fejerArrangementFreeSign
      (fejerArrangementEncode R.1) := by
    simpa [fejerExceptionalArrangements] using hregular
  have hp : (∑ j, balancedFeatureCoefficient fejerArrangementFreeSign j *
      phi (fejerArrangementVertex R.1 j)) ≠ 0 :=
    fun h => hbad ((fejerArrangement_respected_iff R.1 phi).mpr h)
  rw [fejerArrangementVertex_encode R.1 R.2] at hp ⊢
  exact fejerFeature_regular_diagonal hLN fejerArrangementFreeSign fejerArrangementFreeSign_ne_zero
    (fun i => R.1.x i.castSucc) (fun j => R.1.y (finSuccEquivLast.symm j)) R.1.height phi hr hp

end LeanProofs.GowersSzemeredi
