import GowersSzemeredi.Proofs13FejerArrangementParameters

/-! The labels in the polynomial parameterization are exactly the lower
and upper endpoints in the catalogue arrangement definition. Signed phase
vanishing is exactly the catalogue's respected-arrangement predicate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def fejerArrangementVertex {N : Nat} (R : DArrangement N 8)
    (j : Option (Fin 15) × Bool) : ZMod N × ZMod N :=
  (R.x (finSuccEquivLast.symm j.1), R.y (finSuccEquivLast.symm j.1) + if j.2 then R.height else 0)

theorem fejerArrangementVertex_decode {N : Nat} (z : FejerArrangementParameters N) :
    fejerArrangementVertex (fejerArrangementDecode z) =
      balancedFeatureVertex fejerArrangementFreeSign
        (fun j => z (some (Sum.inl j))) (fun j => z (some (Sum.inr j))) (z none) := by
  funext j
  simp [fejerArrangementVertex, fejerArrangementDecode, balancedFeatureVertex,
    DArrangement.x, DArrangement.y, DArrangement.height]

theorem fejerArrangementVertex_encode {N : Nat} (R : DArrangement N 8)
    (hR : IsAdditiveTuple R.x) :
    fejerArrangementVertex R = balancedFeatureVertex fejerArrangementFreeSign
      (fun i => R.x i.castSucc) (fun j => R.y (finSuccEquivLast.symm j)) R.height := by
  have ht := fejerArrangementVertex_decode (fejerArrangementEncode R)
  rw [fejerArrangementDecode_encode R hR] at ht
  exact ht

theorem fejerArrangementCoefficient_reindex {N : Nat} (i : Fin 16) (b : Bool) :
    balancedFeatureCoefficient (fejerArrangementFreeSign (N := N)) (finSuccEquivLast i, b) =
      if b then fejerArrangementSign i else -fejerArrangementSign i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hi : finSuccEquivLast (15 : Fin 16) = none := finSuccEquivLast_last
    cases b <;> simp [balancedFeatureCoefficient, balancedRelationCoefficient, fejerArrangementSign, hi]
  · cases b <;> simp [balancedFeatureCoefficient, balancedRelationCoefficient,
      fejerArrangementFreeSign]

theorem fejerArrangement_phase_sum {N : Nat} (R : DArrangement N 8)
    (phi : ZMod N × ZMod N → ZMod N) :
    (∑ j, balancedFeatureCoefficient fejerArrangementFreeSign j * phi (fejerArrangementVertex R j)) =
      ∑ i : Fin 16, fejerArrangementSign i *
        (phi (R.x i, R.y i + R.height) - phi (R.x i, R.y i)) := by
  rw [Fintype.sum_prod_type]
  rw [← (finSuccEquivLast : Fin 16 ≃ Option (Fin 15)).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fejerArrangementCoefficient_reindex, Fintype.sum_bool,
    if_true, Bool.false_eq_true, if_false, fejerArrangementVertex,
    Equiv.symm_apply_apply, add_zero]
  ring

theorem fejerArrangement_respected_iff {N : Nat} (R : DArrangement N 8)
    (phi : ZMod N × ZMod N → ZMod N) :
    R.IsRespected phi ↔
      ∑ j, balancedFeatureCoefficient fejerArrangementFreeSign j * phi (fejerArrangementVertex R j) = 0 := by
  rw [fejerArrangement_phase_sum]
  exact fejerArrangement_additive_iff _

theorem fejerArrangement_feature_sum {N : Nat} (R : DArrangement N 8)
    (hR : IsAdditiveTuple R.x) :
    ∑ j, balancedFeatureCoefficient fejerArrangementFreeSign j *
      ((fejerArrangementVertex R j).1 * (fejerArrangementVertex R j).2) = 0 := by
  have hs := (fejerArrangement_additive_iff R.x).mp hR
  rw [fejerArrangement_phase_sum R (fun z => z.1 * z.2)]
  calc
    (∑ i : Fin 16, fejerArrangementSign i * (R.x i * (R.y i + R.height) - R.x i * R.y i)) =
        (∑ i : Fin 16, fejerArrangementSign i * R.x i) * R.height := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hs, zero_mul]

theorem fejerArrangement_carrier_iff {N : Nat} (R : DArrangement N 8)
    (hR : IsAdditiveTuple R.x) (U : Finset (ZMod N × ZMod N)) :
    Finset.univ.image (fejerArrangementVertex R) ⊆ U ↔ R.IsIn U := by
  classical
  constructor
  · intro hsub
    refine ⟨hR, ?_⟩
    intro i
    have hl := hsub (Finset.mem_image.mpr ⟨(finSuccEquivLast i, false), Finset.mem_univ _, rfl⟩)
    have hu := hsub (Finset.mem_image.mpr ⟨(finSuccEquivLast i, true), Finset.mem_univ _, rfl⟩)
    simpa [fejerArrangementVertex] using And.intro hl hu
  · rintro ⟨_, hmem⟩ z hz
    obtain ⟨⟨j, b⟩, _, rfl⟩ := Finset.mem_image.mp hz
    cases b
    · simpa [fejerArrangementVertex] using (hmem (finSuccEquivLast.symm j)).1
    · simpa [fejerArrangementVertex] using (hmem (finSuccEquivLast.symm j)).2

end LeanProofs.GowersSzemeredi
