import OAI.Combinatorics.Progressions.Geometry.RealifiedTripleCoordinates
import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedSubalgebra (c : σ → ℕ) : LieSubalgebra ℚ L :=
  (F.weightedLayer c 1).toLieSubalgebra

noncomputable def weightedFiltration (c : σ → ℕ) :
    NilpotentLieFiltration (F.weightedSubalgebra c) (multidegreeWeight c bound) where
  layer n := (F.weightedLayer c (max 1 n)).toSubmodule.comap (F.weightedSubalgebra c).incl.toLinearMap
  antitone := by
    intro i j hij x hx
    exact F.weightedLayer_antitone c (max_le_max_left 1 hij) hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := by
    intro i j x y hx hy
    change ⁅(x : L), (y : L)⁆ ∈ F.weightedLayer c (max 1 (i + j))
    exact F.weightedLayer_antitone c (by omega : max 1 (i + j) ≤ max 1 i + max 1 j)
      (F.weightedLayer_lie_mem c hx hy)
  terminal := by
    apply bot_unique
    intro x hx
    change (x : L) ∈ F.weightedLayer c (max 1 (multidegreeWeight c bound + 1)) at hx
    rw [max_eq_right (by omega : 1 ≤ multidegreeWeight c bound + 1), F.weightedLayer_terminal c] at hx
    change x = 0
    exact Subtype.ext ((LieSubmodule.mem_bot (x : L)).mp hx)

theorem mem_weightedFiltration_layer (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (x : F.weightedSubalgebra c) :
    x ∈ (F.weightedFiltration c).layer n ↔ (x : L) ∈ F.weightedLayer c n := by
  change (x : L) ∈ F.weightedLayer c (max 1 n) ↔ _
  rw [max_eq_right hn]

theorem weightedFiltration_layer_map (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    ((F.weightedFiltration c).layer n).map (F.weightedSubalgebra c).incl.toLinearMap =
      (F.weightedLayer c n).toSubmodule := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (F.mem_weightedFiltration_layer c n hn y).mp hy
  · intro hx
    let y : F.weightedSubalgebra c := ⟨x, F.weightedLayer_antitone c hn hx⟩
    exact ⟨y, (F.mem_weightedFiltration_layer c n hn y).mpr hx, rfl⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_le_sum {σ : Type*} [Fintype σ]
    (c a : σ → ℕ) (hc : ∀ i, c i ≤ 1) : multidegreeWeight c a ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using Nat.mul_le_mul_right (a i) (hc i)

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_le_ordinary (c : σ → ℕ) (hc : ∀ i, c i ≤ 1) (n : ℕ) :
    (F.weightedLayer c n).toSubmodule ≤ F.ordinary.layer n := by
  change (⨆ a : {a : σ → ℕ // n ≤ multidegreeWeight c a}, F.layerIdeal a.val).toSubmodule ≤ _
  rw [LieSubmodule.iSup_toSubmodule]
  apply iSup_le
  intro a
  exact (F.layer_le_ordinary a.val).trans
    (F.ordinary.antitone (a.property.trans (multidegreeWeight_le_sum c a.val hc)))

theorem coordinateIdeal_abelian [DecidableEq σ] (i : σ) (hi : bound i ≤ 1)
    {x y : L} (hx : x ∈ F.layerIdeal (Pi.single i 1))
    (hy : y ∈ F.layerIdeal (Pi.single i 1)) : ⁅x, y⁆ = 0 := by
  have hnot : ¬(Pi.single i 1 + Pi.single i 1 : σ → ℕ) ≤ bound := by
    intro h
    have hh := h i
    simp only [Pi.add_apply, Pi.single_eq_same] at hh
    omega
  have h := F.lie_mem hx hy
  simpa only [F.terminal _ hnot, Submodule.mem_bot] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def coordinateActiveLayer (i : σ) (n : ℕ) : Submodule ℚ L :=
  F.layer (Pi.single i 1) ⊓ F.ordinary.layer n

theorem coordinateActiveLayer_antitone (i : σ) : Antitone (F.coordinateActiveLayer i) :=
  fun _ _ h _ hx => ⟨hx.1, F.ordinary.antitone h hx.2⟩

theorem weighted_lie_active (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {m n : ℕ} {x y : L} (hx : x ∈ F.weightedLayer c m) (hy : y ∈ F.coordinateActiveLayer i n) :
    ⁅x, y⁆ ∈ F.coordinateActiveLayer i (m + n) :=
  ⟨(F.layerIdeal (Pi.single i 1)).lie_mem hy.1,
    F.ordinary.lie_mem (F.weightedLayer_le_ordinary c hc m hx) hy.2⟩

theorem active_lie_weighted (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {m n : ℕ} {x y : L} (hx : x ∈ F.coordinateActiveLayer i m) (hy : y ∈ F.weightedLayer c n) :
    ⁅x, y⁆ ∈ F.coordinateActiveLayer i (m + n) :=
  ⟨lie_mem_left (R := ℚ) (L := L) (F.layerIdeal (Pi.single i 1)) x y hx.1,
    F.ordinary.lie_mem hx.2 (F.weightedLayer_le_ordinary c hc n hy)⟩

noncomputable def additiveTripleLayer (i : σ) (c : σ → ℕ) (n : ℕ) :
    Submodule ℚ (L × L × L) :=
  ((F.weightedLayer c n).toSubmodule.comap tripleNeutral) ⊓
    ((F.coordinateActiveLayer i n).comap tripleLeft ⊓
      (F.coordinateActiveLayer i n).comap tripleRight)

theorem mem_additiveTripleLayer (i : σ) (c : σ → ℕ) (n : ℕ) (x : L × L × L) :
    x ∈ F.additiveTripleLayer i c n ↔
      tripleNeutral x ∈ F.weightedLayer c n ∧
      tripleLeft x ∈ F.coordinateActiveLayer i n ∧
      tripleRight x ∈ F.coordinateActiveLayer i n := Iff.rfl

theorem additiveTripleLayer_antitone (i : σ) (c : σ → ℕ) : Antitone (F.additiveTripleLayer i c) := by
  intro m n h x hx
  exact ⟨F.weightedLayer_antitone c h hx.1,
    F.coordinateActiveLayer_antitone i h hx.2.1, F.coordinateActiveLayer_antitone i h hx.2.2⟩

theorem additiveTripleLayer_lie_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {m n : ℕ} {x y : L × L × L}
    (hx : x ∈ F.additiveTripleLayer i c m) (hy : y ∈ F.additiveTripleLayer i c n) :
    ⁅x, y⁆ ∈ F.additiveTripleLayer i c (m + n) := by
  have heq : ⁅x, y⁆ = tripleAssemble ⁅tripleNeutral x, tripleNeutral y⁆
      (⁅tripleNeutral x, tripleLeft y⁆ + ⁅tripleLeft x, tripleNeutral y⁆)
      (⁅tripleNeutral x, tripleRight y⁆ + ⁅tripleRight x, tripleNeutral y⁆) := by
    calc
      ⁅x, y⁆ = ⁅tripleAssemble (tripleNeutral x) (tripleLeft x) (tripleRight x),
          tripleAssemble (tripleNeutral y) (tripleLeft y) (tripleRight y)⁆ := by
        rw [tripleAssemble_decompose, tripleAssemble_decompose]
      _ = _ := tripleAssemble_lie _ _ _ _ _ _
        (F.coordinateIdeal_abelian i hi hx.2.1.1 hy.2.1.1)
        (F.coordinateIdeal_abelian i hi hx.2.1.1 hy.2.2.1)
        (F.coordinateIdeal_abelian i hi hx.2.2.1 hy.2.1.1)
        (F.coordinateIdeal_abelian i hi hx.2.2.1 hy.2.2.1)
  rw [heq, F.mem_additiveTripleLayer, tripleNeutral_assemble, tripleLeft_assemble, tripleRight_assemble]
  exact ⟨F.weightedLayer_lie_mem c hx.1 hy.1,
    (F.coordinateActiveLayer i (m + n)).add_mem
      (F.weighted_lie_active i c hc hx.1 hy.2.1) (F.active_lie_weighted i c hc hx.2.1 hy.1),
    (F.coordinateActiveLayer i (m + n)).add_mem
      (F.weighted_lie_active i c hc hx.1 hy.2.2) (F.active_lie_weighted i c hc hx.2.2 hy.1)⟩

theorem additiveTripleLayer_coordinates (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {n : ℕ} {x : L × L × L} (hx : x ∈ F.additiveTripleLayer i c n) :
    x.1 ∈ F.ordinary.layer n ∧ x.2.1 ∈ F.ordinary.layer n ∧ x.2.2 ∈ F.ordinary.layer n := by
  have ha := F.weightedLayer_le_ordinary c hc n hx.1
  have hb := hx.2.1.2
  have hc' := hx.2.2.2
  have heq := tripleAssemble_decompose x
  rw [← heq]
  exact ⟨(F.ordinary.layer n).add_mem ((F.ordinary.layer n).add_mem ha hb) hc',
    (F.ordinary.layer n).add_mem ha hb, (F.ordinary.layer n).add_mem ha hc'⟩

theorem additiveTripleLayer_terminal (i : σ) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleLayer i c (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨h₁, h₂, h₃⟩ := F.additiveTripleLayer_coordinates i c hc hx
  simp only [F.ordinary.terminal, Submodule.mem_bot] at h₁ h₂ h₃
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

theorem additiveTripleLayer_top_relation (i : σ) (c : σ → ℕ)
    (htop : F.weightedLayer c s = ⊥) {x : L × L × L}
    (hx : x ∈ F.additiveTripleLayer i c s) : x.1 = x.2.1 + x.2.2 := by
  have h : tripleNeutral x ∈ F.weightedLayer c s := hx.1
  rw [htop, LieSubmodule.mem_bot] at h
  change x.2.1 + x.2.2 - x.1 = 0 at h
  exact (sub_eq_zero.mp h).symm

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleSubalgebra (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) : LieSubalgebra ℚ (L × L × L) :=
  { F.additiveTripleLayer i c 1 with
    lie_mem' := fun hx hy => F.additiveTripleLayer_antitone i c (by decide : 1 ≤ 1 + 1)
      (F.additiveTripleLayer_lie_mem i hi c hc hx hy) }

noncomputable def additiveTripleFiltration (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    NilpotentLieFiltration (F.additiveTripleSubalgebra i hi c hc) s where
  layer n := (F.additiveTripleLayer i c n).comap (F.additiveTripleSubalgebra i hi c hc).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.additiveTripleLayer_antitone i c h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.additiveTripleLayer_lie_mem i hi c hc hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    have h : (x : L × L × L) ∈ F.additiveTripleLayer i c (s + 1) := hx
    rw [F.additiveTripleLayer_terminal i c hc, Submodule.mem_bot] at h
    exact h

noncomputable def additiveTripleFirst (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl

noncomputable def additiveTripleSecond (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp
    ((LieHom.snd ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl)

noncomputable def additiveTripleThird (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp
    ((LieHom.snd ℚ L (L × L)).comp (F.additiveTripleSubalgebra i hi c hc).incl)

theorem additiveTripleProjections_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {n : ℕ}
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer n) :
    F.additiveTripleFirst i hi c hc x ∈ F.ordinary.layer n ∧
    F.additiveTripleSecond i hi c hc x ∈ F.ordinary.layer n ∧
    F.additiveTripleThird i hi c hc x ∈ F.ordinary.layer n :=
  F.additiveTripleLayer_coordinates i c hc hx

theorem additiveTripleTop_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (htop : F.weightedLayer c s = ⊥)
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer s) :
    F.additiveTripleFirst i hi c hc x =
      F.additiveTripleSecond i hi c hc x + F.additiveTripleThird i hi c hc x :=
  F.additiveTripleLayer_top_relation i c htop hx

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def tripleToPi : (L × L × L) →ₗ⁅ℚ⁆ (Fin 3 → L) :=
  liePiMap ![LieHom.fst ℚ L (L × L),
    (LieHom.fst ℚ L L).comp (LieHom.snd ℚ L (L × L)),
    (LieHom.snd ℚ L L).comp (LieHom.snd ℚ L (L × L))]

@[simp] theorem tripleToPi_zero (x : L × L × L) : tripleToPi x 0 = x.1 := rfl

@[simp] theorem tripleToPi_one (x : L × L × L) : tripleToPi x 1 = x.2.1 := rfl

@[simp] theorem tripleToPi_two (x : L × L × L) : tripleToPi x 2 = x.2.2 := rfl

theorem tripleToPi_injective : Function.Injective (tripleToPi (L := L)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleToPi (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ (Fin 3 → L) :=
  tripleToPi.comp (F.additiveTripleSubalgebra i hi c hc).incl

theorem additiveTripleToPi_injective (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    Function.Injective (F.additiveTripleToPi i hi c hc) :=
  fun _ _ h => Subtype.ext (tripleToPi_injective h)

theorem additiveTripleToPi_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {n : ℕ}
    {x : F.additiveTripleSubalgebra i hi c hc}
    (hx : x ∈ (F.additiveTripleFiltration i hi c hc).layer n) :
    F.additiveTripleToPi i hi c hc x ∈
      (NilpotentLieFiltration.pi (fun _ : Fin 3 => F.ordinary)).layer n := by
  obtain ⟨h₀, h₁, h₂⟩ := F.additiveTripleProjections_mem i hi c hc hx
  apply (NilpotentLieFiltration.mem_pi_layer _ _ _).mpr
  intro j
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_realification (c : σ → ℕ) (n : ℕ) :
    (F.realification.weightedLayer c n).toSubmodule =
      ((F.weightedLayer c n).toSubmodule.baseChange ℝ).restrictScalars ℚ := by
  simp only [weightedLayer, LieSubmodule.iSup_toSubmodule,
    real_baseChange_iSup, real_restrictScalars_iSup]
  rfl

noncomputable def realifiedWeightedEquiv (c : σ → ℕ) :
    (ℝ ⊗[ℚ] F.weightedSubalgebra c) ≃ₗ[ℚ] F.realification.weightedSubalgebra c :=
  ((realificationSubmoduleEquiv (F.weightedSubalgebra c).toSubmodule).restrictScalars ℚ).trans
    (LinearEquiv.ofEq _ _ (F.weightedLayer_realification c 1).symm)

theorem realifiedWeightedEquiv_coe (c : σ → ℕ) (x : ℝ ⊗[ℚ] F.weightedSubalgebra c) :
    (F.realifiedWeightedEquiv c x : ℝ ⊗[ℚ] L) =
      realificationLieHom (F.weightedSubalgebra c).incl x := rfl

theorem realifiedWeightedEquiv_mem_layer (c : σ → ℕ) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.weightedSubalgebra c) :
    x ∈ (F.weightedFiltration c).realification.layer n ↔
      F.realifiedWeightedEquiv c x ∈ (F.realification.weightedFiltration c).layer n := by
  change x ∈ ((F.weightedLayer c (max 1 n)).toSubmodule.comap
    (F.weightedSubalgebra c).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change (F.weightedSubalgebra c).incl.toLinearMap.baseChange ℝ x ∈
    (F.weightedLayer c (max 1 n)).toSubmodule.baseChange ℝ ↔
      (F.realifiedWeightedEquiv c x : ℝ ⊗[ℚ] L) ∈ F.realification.weightedLayer c (max 1 n)
  rw [F.realifiedWeightedEquiv_coe]
  have h := F.weightedLayer_realification c (max 1 n)
  change _ = _ at h
  change _ ↔ _ ∈ (F.realification.weightedLayer c (max 1 n)).toSubmodule
  rw [h]
  rfl

theorem realifiedWeightedEquiv_symm_mem_layer (c : σ → ℕ) (n : ℕ)
    (x : F.realification.weightedSubalgebra c) :
    (F.realifiedWeightedEquiv c).symm x ∈ (F.weightedFiltration c).realification.layer n ↔
      x ∈ (F.realification.weightedFiltration c).layer n := by
  rw [F.realifiedWeightedEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem coordinateActiveLayer_realification (i : σ) (n : ℕ) :
    F.realification.coordinateActiveLayer i n =
      ((F.coordinateActiveLayer i n).baseChange ℝ).restrictScalars ℚ := by
  rw [coordinateActiveLayer, coordinateActiveLayer, realification_inf]
  rfl

theorem realTripleEquiv_mem_layer (i : σ) (c : σ → ℕ) (n : ℕ)
    (x : ℝ ⊗[ℚ] (L × L × L)) :
    realTripleEquiv x ∈ F.realification.additiveTripleLayer i c n ↔
      x ∈ (F.additiveTripleLayer i c n).baseChange ℝ := by
  have hw (y : ℝ ⊗[ℚ] L) : y ∈ F.realification.weightedLayer c n ↔
      y ∈ (F.weightedLayer c n).toSubmodule.baseChange ℝ := by
    change y ∈ (F.realification.weightedLayer c n).toSubmodule ↔ _
    rw [F.weightedLayer_realification]
    rfl
  have ha (y : ℝ ⊗[ℚ] L) : y ∈ F.realification.coordinateActiveLayer i n ↔
      y ∈ (F.coordinateActiveLayer i n).baseChange ℝ := by
    rw [F.coordinateActiveLayer_realification]
    rfl
  rw [F.realification.mem_additiveTripleLayer, hw, ha, ha,
    realTripleEquiv_neutral, realTripleEquiv_left, realTripleEquiv_right]
  simp only [additiveTripleLayer, realification_inf, realification_comap,
    Submodule.mem_inf, Submodule.mem_comap]

noncomputable def realifiedTripleLayerEquiv (i : σ) (c : σ → ℕ) (n : ℕ) :
    ((F.additiveTripleLayer i c n).baseChange ℝ) ≃ₗ[ℚ]
      F.realification.additiveTripleLayer i c n where
  toFun x := ⟨realTripleEquiv x.val, (F.realTripleEquiv_mem_layer i c n x.val).mpr x.property⟩
  invFun x := ⟨realTripleEquiv.symm x.val, (F.realTripleEquiv_mem_layer i c n _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (realTripleEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (realTripleEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (realTripleEquiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((realTripleEquiv.restrictScalars ℚ).map_smul r x.val)

noncomputable def realifiedAdditiveTripleEquiv (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    (ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) ≃ₗ[ℚ]
      F.realification.additiveTripleSubalgebra i hi c hc :=
  ((realificationSubmoduleEquiv (F.additiveTripleLayer i c 1)).restrictScalars ℚ).trans
    (F.realifiedTripleLayerEquiv i c 1)

theorem realifiedAdditiveTripleEquiv_coe (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    (F.realifiedAdditiveTripleEquiv i hi c hc x :
      (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) =
        realTripleEquiv (realificationLieHom (F.additiveTripleSubalgebra i hi c hc).incl x) := rfl

theorem realifiedAdditiveTripleEquiv_mem_layer (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    x ∈ (F.additiveTripleFiltration i hi c hc).realification.layer n ↔
      F.realifiedAdditiveTripleEquiv i hi c hc x ∈
        (F.realification.additiveTripleFiltration i hi c hc).layer n := by
  change x ∈ ((F.additiveTripleLayer i c n).comap
    (F.additiveTripleSubalgebra i hi c hc).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.additiveTripleSubalgebra i hi c hc).incl x ∈
    (F.additiveTripleLayer i c n).baseChange ℝ ↔
      (F.realifiedAdditiveTripleEquiv i hi c hc x :
        (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
          F.realification.additiveTripleLayer i c n
  rw [F.realifiedAdditiveTripleEquiv_coe, F.realTripleEquiv_mem_layer]

theorem realifiedAdditiveTripleEquiv_symm_mem_layer (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ)
    (x : F.realification.additiveTripleSubalgebra i hi c hc) :
    (F.realifiedAdditiveTripleEquiv i hi c hc).symm x ∈
        (F.additiveTripleFiltration i hi c hc).realification.layer n ↔
      x ∈ (F.realification.additiveTripleFiltration i hi c hc).layer n := by
  rw [F.realifiedAdditiveTripleEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

end OAI
