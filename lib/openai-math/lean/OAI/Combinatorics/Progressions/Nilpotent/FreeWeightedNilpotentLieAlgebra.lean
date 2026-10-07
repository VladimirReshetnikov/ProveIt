import OAI.Combinatorics.Progressions.Estimates.FreeWeightedLayerBounds

namespace OAI

section

namespace Erdos3

def FreeWeightedNilpotentLieAlgebra (X : Type*) (s : ℕ) (w : X → ℕ) :=
  FreeNilpotentLieAlgebra X s ⧸ FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) (s : ℕ) (w : X → ℕ)

noncomputable instance instLieRing : LieRing (FreeWeightedNilpotentLieAlgebra X s w) :=
  inferInstanceAs (LieRing (FreeNilpotentLieAlgebra X s ⧸
    FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeWeightedNilpotentLieAlgebra X s w) :=
  inferInstanceAs (LieAlgebra ℚ (FreeNilpotentLieAlgebra X s ⧸
    FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)))

noncomputable def mk : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ FreeWeightedNilpotentLieAlgebra X s w :=
  lieQuotientMap (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))

theorem mk_surjective : Function.Surjective (mk X s w) := lieQuotientMap_surjective _

theorem mk_eq_zero (x : FreeNilpotentLieAlgebra X s) :
    mk X s w x = 0 ↔ x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w (s + 1) :=
  lieQuotientMap_eq_zero _ x

theorem lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ (FreeWeightedNilpotentLieAlgebra X s w)
      (FreeWeightedNilpotentLieAlgebra X s w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (FreeNilpotentLieAlgebra.lowerCentralSeries_eq_bot X s) _

noncomputable def of (x : X) : FreeWeightedNilpotentLieAlgebra X s w :=
  mk X s w (FreeNilpotentLieAlgebra.of X s x)

noncomputable def filtration (hw : ∀ i, 0 < w i) :
    NilpotentLieFiltration (FreeWeightedNilpotentLieAlgebra X s w) s where
  layer d := (FreeNilpotentLieAlgebra.weightedLayer X s w d).map (mk X s w).toLinearMap
  antitone := fun _ _ h => Submodule.map_mono (FreeNilpotentLieAlgebra.weightedLayer_antitone X s w h)
  one_eq_top := by
    rw [FreeNilpotentLieAlgebra.weightedLayer_one X s w hw, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (mk_surjective X s w)
  lie_mem := by
    rintro d e x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, FreeNilpotentLieAlgebra.weightedLayer_lie_mem X s w ha hb, (mk X s w).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (mk_eq_zero X s w a).mpr ha

theorem of_mem_layer (hw : ∀ i, 0 < w i) (x : X) :
    of X s w x ∈ (filtration X s w hw).layer (w x) :=
  ⟨FreeNilpotentLieAlgebra.of X s x,
    weightedLieUpperSpan_leaf (FreeNilpotentLieAlgebra.of X s) w x, rfl⟩

instance finite [Fintype X] : Module.Finite ℚ (FreeWeightedNilpotentLieAlgebra X s w) :=
  Module.Finite.of_surjective (mk X s w).toLinearMap (mk_surjective X s w)

theorem finrank_le [Fintype X] :
    Module.finrank ℚ (FreeWeightedNilpotentLieAlgebra X s w) ≤ (s + 1) * (Fintype.card X + 1) ^ s :=
  (LinearMap.finrank_le_finrank_of_surjective (mk_surjective X s w)).trans
    (FreeNilpotentLieAlgebra.finrank_le X s)

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
