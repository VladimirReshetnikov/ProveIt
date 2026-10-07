import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleLayerEquiv (i : σ) (c : σ → ℕ) (n : ℕ) :
    (F.weightedLayer c n × F.coordinateActiveLayer i n × F.coordinateActiveLayer i n)
      ≃ₗ[ℚ] F.additiveTripleLayer i c n where
  toFun x := ⟨tripleAssemble (x.1 : L) (x.2.1 : L) (x.2.2 : L), by
    rw [F.mem_additiveTripleLayer, tripleNeutral_assemble, tripleLeft_assemble,
      tripleRight_assemble]
    exact ⟨x.1.property, x.2.1.property, x.2.2.property⟩⟩
  invFun x := (⟨tripleNeutral x.val, x.property.1⟩,
    ⟨tripleLeft x.val, x.property.2.1⟩, ⟨tripleRight x.val, x.property.2.2⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (tripleNeutral_assemble _ _ _)
    · exact Prod.ext (Subtype.ext (tripleLeft_assemble _ _ _))
        (Subtype.ext (tripleRight_assemble _ _ _))
  right_inv x := Subtype.ext (tripleAssemble_decompose x.val)
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp only [tripleAssemble, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, LieSubmodule.coe_add] <;> abel
  map_smul' r x := by
    apply Subtype.ext
    ext <;> simp [tripleAssemble, smul_add]

theorem exists_additiveTriple_layer_basis {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (e : Basis ι ℚ L) (i : σ) (c : σ → ℕ) (n : ℕ)
    (a : Basis α ℚ (F.weightedLayer c n))
    (b : Basis β ℚ (F.coordinateActiveLayer i n))
    {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ j k, RationalHeightLE (e.repr (a j : L) k) H)
    (hb : ∀ j k, RationalHeightLE (e.repr (b j : L) k) H) :
    ∃ q : Basis (Fin (finrank ℚ (F.additiveTripleLayer i c n))) ℚ
        (F.additiveTripleLayer i c n),
      ∀ j k, RationalHeightLE (e.repr (q j).val.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.2 k) H := by
  classical
  let q := (a.prod (b.prod b)).map (F.additiveTripleLayerEquiv i c n)
  have hzero (k : ι) : RationalHeightLE (e.repr 0 k) H := by
    simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  have hq (j : α ⊕ (β ⊕ β)) (k : ι) :
      RationalHeightLE (e.repr (q j).val.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.2 k) H := by
    rcases j with j | j | j
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (a j : L) k) H ∧
          RationalHeightLE (e.repr (a j : L) k) H ∧
          RationalHeightLE (e.repr (a j : L) k) H from ⟨ha j k, ha j k, ha j k⟩)
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr 0 k) H from ⟨hb j k, hb j k, hzero k⟩)
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr 0 k) H ∧
          RationalHeightLE (e.repr (b j : L) k) H from ⟨hb j k, hzero k, hb j k⟩)
  let r := q.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis q).symm)
  refine ⟨r, fun j k => ?_⟩
  simpa only [r, Basis.reindex_apply] using hq _ k

noncomputable def additiveTripleFiltrationLayerEquiv (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (F.additiveTripleFiltration i hi c hc).layer n ≃ₗ[ℚ] F.additiveTripleLayer i c n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.additiveTripleLayer_antitone i c hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
