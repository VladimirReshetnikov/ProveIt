import OAI.Combinatorics.Progressions.Dynamics.RationalLieQuotientBudget
import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_subalgebra_basis_and_grid (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (v : η → K) (hspan : Submodule.span ℚ (Set.range v) = ⊤)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i : L) j) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ b : Basis (Fin (finrank ℚ K)) ℚ K, ∃ N : ℕ,
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      (∀ i j, RationalHeightLE (e.repr (b i : L) j) H) ∧
      (∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 11)) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map
          (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) ∧
      bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map
          (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) ⊆ denominatorGrid N := by
  classical
  obtain ⟨b, hb, hc'⟩ := exists_lie_subalgebra_basis_exp_height e K v hspan hHpos hv hc hp hd hH
  have hr : (Fintype.card (Fin (finrank ℚ K)) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr (lie_subalgebra_finrank_le e K)).trans hd
  obtain ⟨N, hN, hNbound, hin, hout⟩ :=
    exists_bchSubgroup_comap_grid_exp_bound (hM := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      b e K.incl (fun _ _ h => Subtype.ext h) Γ hHpos hlpos (by
        intro i j
        rw [LinearMap.toMatrix_apply]
        change RationalHeightLE (e.repr (b j : L) i) H
        exact hb j i) hinner houter hp hd hr hH hl
  exact ⟨b, N, hN, hNbound, hb, hc', hin, hout⟩

theorem exists_quotient_basis_and_grid [Fintype η] (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (v : η → L) (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p) (hm : (Fintype.card η : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ d : ℕ, d ≤ Fintype.card ι ∧ ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ N : ℕ,
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 81) ∧
      (∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 51) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 51)) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b (Γ.map (NilpotentLieBCHGroup.quotientHom I)) ∧
      bchSubgroupCoordinates b (Γ.map (NilpotentLieBCHGroup.quotientHom I)) ⊆ denominatorGrid N := by
  classical
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, _, hD, _, hbracket⟩ :=
    exists_bounded_lie_quotient_with_structure e I v hspan hHpos hv hc
  have htp : (t : ℝ) ≤ p := (Nat.cast_le.mpr ht).trans hm
  have hdp : (d : ℝ) ≤ p := (Nat.cast_le.mpr hd).trans hn
  have hpq : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  obtain ⟨N, hN, hNbound, hin, hout⟩ :=
    exists_bchSubgroup_map_grid_exp_bound (hM := lie_quotient_lowerCentralSeries_eq_bot hnil I)
      e b (lieQuotientMap I) (lieQuotientMap_surjective I) Γ
      (rationalKernelHeight_pos t hHpos) hlpos (by
        intro i j
        rw [hmatrix]
        exact hD i j) hinner houter (by positivity : 0 ≤ (p + 2) ^ 7) (hn.trans hpq)
      (by simpa only [Fintype.card_fin] using hdp.trans hpq)
      (rationalKernelHeight_le_budget t H hp htp hH) (hl.trans (Real.exp_le_exp.mpr hpq))
  have hC := rationalLieQuotientStructureHeight_le_exp (Fintype.card ι) t d H hp hn htp hdp hH
  refine ⟨d, hd, b, N, hN, exponential_budget_comp hp (by positivity) 7 9 le_rfl hNbound, ?_, hin, hout⟩
  intro i j k
  exact ⟨(Nat.cast_le.mpr (hbracket i j k).1).trans hC,
    (Nat.cast_le.mpr (hbracket i j k).2).trans hC⟩

end Erdos3

end

end OAI
