import OAI.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates
import OAI.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec

namespace OAI

section

namespace Erdos3

theorem recover_middle_coset_of_left_class {G : Type*} [Group G] (Γ : Subgroup G)
    (e b r κ t z γ : G) (hfactor : e * b * r * κ = t)
    (hγ : γ ∈ Γ) (hr : r = γ * z) :
    (QuotientGroup.mk b : G ⧸ Γ) = QuotientGroup.mk (e⁻¹ * t * κ⁻¹ * z⁻¹) := by
  have heq : e⁻¹ * t * κ⁻¹ * z⁻¹ = b * γ := by
    rw [← hfactor, hr]
    group
  rw [heq]
  exact (QuotientGroup.mk_mul_of_mem b hγ).symm

theorem recover_mapped_middle_coset_of_left_class {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (Λ : Subgroup H) (e b r κ t : G) (z γ : H)
    (hfactor : e * b * r * κ = t) (hγ : γ ∈ Λ) (hr : φ r = γ * z) :
    (QuotientGroup.mk (φ b) : H ⧸ Λ) =
      QuotientGroup.mk ((φ e)⁻¹ * φ t * (φ κ)⁻¹ * z⁻¹) := by
  apply recover_middle_coset_of_left_class Λ (φ e) (φ b) (φ r) (φ κ) (φ t) z γ _ hγ hr
  simpa only [map_mul] using congrArg φ hfactor

end Erdos3

end

section

namespace Erdos3

open Module

theorem bchSubgroup_inner_grid_of_reindex {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (b : Basis ι ℚ L) (e : ι ≃ κ) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {N : ℕ}
    (h : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (b.reindex e) Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ := by
  have hb : (b.reindex e).reindex e.symm = b := by
    ext i
    simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  have h' := bchSubgroup_inner_grid_reindex (b.reindex e) e.symm Γ h
  rwa [hb] at h'

namespace RationalFilteredNilmanifold

theorem exists_native_factorwise_covers :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ), 0 < m →
      (scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ) →
      ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
          ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
          ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        (pi E).GeometryComplexityLE ((p + C) ^ C) ∧ (pi E).lattice ≤ Λ := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2
  let P := 2 * X ^ 2 + Q + (Q + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ s d D Λ m hm hΛ p hp hι hD hmp
  have hraw : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis (fun i => (D i).basis)) Λ :=
    bchSubgroup_inner_grid_of_reindex _ (Fintype.equivFin _) Λ hΛ
  obtain ⟨Δ, N, hdata, hsubset⟩ := exists_factorwise_bch_covers
    (fun i => (D i).filtration) (fun i => (D i).basis) (fun i => (D i).lattice)
    (fun i => (D i).grid) (fun i => (D i).grid_pos) (fun i => (D i).inner_grid)
    (fun i => (D i).outer_grid) Λ m hm hraw hp
    (fun i => by simpa only [Fintype.card_fin] using (hD i).1) (fun i => (hD i).2.1) hmp
  have hN : ∀ i, 0 < N i := fun i => by rcases hdata i with ⟨_, _, _, _, _, h, _, _, _⟩; exact h
  have hNb : ∀ i, (N i : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, h, _, _⟩; exact h
  have hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, _, h, _⟩; exact h
  have hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i) :=
    fun i => by rcases hdata i with ⟨_, _, _, _, _, _, _, _, h⟩; exact h
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  have hpq : p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hE : ∀ i, (E i).GeometryComplexityLE ((p + 2) ^ 2) := fun i =>
    (D i).withLattice_geometry (Δ i) (N i) (hN i) (hin i) (hout i) (hD i) hpq (hNb i)
  have hprod := pi_geometry E (sq_nonneg (p + 2)) (hι.trans hpq) hE
  have hsum : 2 * p ^ 2 + (p + 2) ^ 2 + ((p + 2) ^ 2 + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, Q, X, Polynomial.eval₂_pow] using hbudget p hp
  have hidx : 2 * p ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (p + 2), sq_nonneg ((p + 2) ^ 2 + 2)]
  have hgeom : (p + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg p, sq_nonneg ((p + 2) ^ 2 + 2)]
  have hprodgeom : ((p + 2) ^ 2 + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg p, sq_nonneg (p + 2)]
  refine ⟨Δ, N, hN, hin, hout, ?_, fun i => (hE i).mono (E i) hgeom,
    hprod.mono (pi E) hprodgeom, hsubset⟩
  intro i
  rcases hdata i with ⟨hle, hchar, hnormal, hfinite, hindex, _, _, _, _⟩
  exact ⟨hle, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hidx)⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_factorwise_reconstruction_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (Λ : Subgroup (pi D).filtration.Group) (m : ℕ) (hm : 0 < m)
      (hΛin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Λ)
      (hΛout : bchSubgroupCoordinates (pi D).basis Λ ⊆ denominatorGrid m)
      {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (m : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        ∃ hsub : (pi E).lattice ≤ Λ,
          (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
            ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
            ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          (pi E).GeometryComplexityLE ((p + C) ^ C) ∧
          let V := (pi D).withLattice Λ m hm hΛin hΛout
          let π := sublatticeProjection V (pi E) hsub
          Function.Surjective π ∧
          (letI := (pi E).metricSpace; letI := V.metricSpace; LipschitzWith 1 π) ∧
          (∀ x : (pi E).RealGroup, π (QuotientGroup.mk x) = QuotientGroup.mk x) ∧
          ∀ (u : V.Space → ℂ) (K : ℝ≥0), (letI := V.metricSpace; LipschitzWith K u) →
            (letI := (pi E).metricSpace; LipschitzWith K (u ∘ π)) ∧
            ∀ x : (pi E).RealGroup, (u ∘ π) (QuotientGroup.mk x) = u (QuotientGroup.mk x) := by
  obtain ⟨C, hC, hcover⟩ := exists_native_factorwise_covers
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ s d D Λ m hm hΛin hΛout p hp hι hD hmp
  obtain ⟨Δ, N, hN, hin, hout, hidx, hE, hprod, hsub⟩ := hcover D Λ m hm hΛin hp hι hD hmp
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let V := (pi D).withLattice Λ m hm hΛin hΛout
  have hb : (pi E).basis = V.basis := rfl
  refine ⟨Δ, N, hN, hin, hout, hsub, hidx, hE, hprod,
    sublatticeProjection_surjective V (pi E) hsub,
    sublatticeProjection_lipschitz V (pi E) hsub hb,
    fun x => sublatticeProjection_mk V (pi E) hsub x, ?_⟩
  intro u K hu
  exact ⟨sublattice_pullback_lipschitz V (pi E) hsub hb u hu, fun _ => rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_normalized_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ r : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ a b : E.RealGroup,
              (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              ∀ x y : D.RealGroup,
                dist (QuotientGroup.mk (a * ψ x * (ψ κ⁻¹ * r)) : E.Space)
                    (QuotientGroup.mk (b * ψ y * (ψ κ⁻¹ * r))) ≤
                  Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
                    dist a b := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hsum : (p + c₀) ^ c₀ + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcoverC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ t + c₁ by positivity) c₁, sq_nonneg (t + 2)]
  have hmetricC : (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + c₀ by positivity) c₀]
  let H := ⌈Real.exp p⌉₊
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hAB : ((A * B : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) := by push_cast; gcongr
      _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hmetricC
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcoverC),
    N, hN, hin, hout, hQ.mono Q hcoverC, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ r hr a b ha x y
  have ha' : LipschitzWith A (fun z => a * z) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) k)))
  have hcompat := D.normalized_right_compatibility E φ q hq Λ htarget hΛ hnormal κ hκ r hr
  have hdist := native_frozenCosetMap_dist_le Q E φ _ a b hcompat hBLip ha' x y
  exact hdist.trans (add_le_add (mul_le_mul_of_nonneg_right hAB dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_left_class_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ z : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun z.coord ∈ realDenominatorGrid q →
            ∀ a a' b b' r r' x x' : D.RealGroup,
              a * b * r * κ = x → a' * b' * r' * κ = x' →
              (∃ γ ∈ E.realLattice, ψ r = γ * z) → (∃ γ ∈ E.realLattice, ψ r' = γ * z) →
              (∀ i, |(E.basis.baseChange ℝ).repr ((ψ a)⁻¹).coord i| ≤ Real.exp ((p + 2) ^ k)) →
              dist (QuotientGroup.mk (ψ b) : E.Space) (QuotientGroup.mk (ψ b')) ≤
                Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk x') +
                  dist (ψ a)⁻¹ (ψ a')⁻¹ := by
  obtain ⟨C, hC, hrecovery⟩ := exists_uniform_normalized_recovery s k
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmetric⟩ :=
    hrecovery D E φ hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ z hz a a' b b' r r' x x' hfactor hfactor' hr hr' ha
  obtain ⟨γ, hγ, hr⟩ := hr
  obtain ⟨γ', hγ', hr'⟩ := hr'
  have hrecover := recover_mapped_middle_coset_of_left_class ψ E.realLattice a b r κ x z γ hfactor hγ hr
  have hrecover' := recover_mapped_middle_coset_of_left_class ψ E.realLattice a' b' r' κ x' z γ' hfactor' hγ' hr'
  have hzinv : (E.basis.baseChange ℝ).equivFun (z⁻¹).coord ∈ realDenominatorGrid q := by
    simpa only [coord_inv, map_neg] using realDenominatorGrid_neg q hz
  rw [hrecover, hrecover']
  simpa only [map_inv, mul_assoc] using hmetric κ hκ z⁻¹ hzinv (ψ a)⁻¹ (ψ a')⁻¹ ha x x'

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_subgroup_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M), Function.Injective φ → ∀ {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup E.filtration.Group, Λ ≤ E.lattice ∧
        (Λ.subgroupOf E.lattice).Characteristic ∧ (Λ.subgroupOf E.lattice).Normal ∧
        (Λ.subgroupOf E.lattice).FiniteIndex ∧ (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := D.metricSpace
          letI := Q.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : E.RealGroup, κ ∈ E.realLattice → ∀ r : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ a b x y : E.RealGroup, ∀ u v : D.RealGroup,
              (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              a * x * (κ⁻¹ * r) = ψ u → b * y * (κ⁻¹ * r) = ψ v →
              dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b <
                Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) ≤
                Real.exp ((p + C) ^ C) *
                  (dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b) := by
  obtain ⟨A, _, hinverse⟩ := exists_native_immersion_local_inverse s
  obtain ⟨B, _, hnormalize⟩ := exists_uniform_normalized_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ hφ p hp hD hE hheight q hq hqp
  obtain ⟨Λ₀, _, _, _, _, _, N₀, hN₀, hin₀, hout₀, hE₀, hlocal⟩ :=
    hinverse D E φ hφ hp hD hE hheight
  let E₀ := E.withLattice Λ₀ N₀ hN₀ hin₀ hout₀
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hidHeight : ∀ i j, rationalLogHeight (E₀.basis.repr ((LieHom.id : M →ₗ⁅ℚ⁆ M) (E.basis j)) i) ≤ t := by
    intro i j
    apply rationalLogHeight_le_of_height (H := 1) _ (by simpa using Real.one_le_exp ht)
    change RationalHeightLE (E.basis.repr (E.basis j) i) 1
    rw [Basis.repr_self]
    by_cases h : j = i <;> simp [h, RationalHeightLE]
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hnorm⟩ :=
    hnormalize E E₀ (LieHom.id : M →ₗ⁅ℚ⁆ M) ht (hE.mono E hpt) (hE₀.mono E₀ hAt)
      hidHeight q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  let Q := E.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hABC : (p + A) ^ A + (t + B) ^ B ≤ (p + C) ^ C := by
    dsimp [t] at hsum
    linarith
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hBC),
    N, hN, hin, hout, hQ.mono Q hBC, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := D.metricSpace
  let := Q.metricSpace
  let := E₀.metricSpace
  have hid (z : E.RealGroup) : realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := E₀.filtration.lowerCentralSeries_eq_bot) (LieHom.id : M →ₗ⁅ℚ⁆ M) z = z := by
    apply NilpotentLieBCHGroup.ext
    exact realificationLieHom_id_apply z.coord
  dsimp only
  intro κ hκ r hr a b x y u v ha hu hv hnear
  have ha' : ∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ k) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  have hd := hnorm κ hκ r hr a b ha' x y
  simp only [hid] at hd
  rw [hu, hv] at hd
  change dist (QuotientGroup.mk (ψ u) : E₀.Space) (QuotientGroup.mk (ψ v)) ≤
    Real.exp ((t + B) ^ B) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
      dist a b at hd
  let delta := dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b
  have hdelta : 0 ≤ delta := add_nonneg dist_nonneg dist_nonneg
  have hNpos : 1 ≤ Real.exp ((t + B) ^ B) := Real.one_le_exp (pow_nonneg (by positivity) _)
  have hbound : dist (QuotientGroup.mk (ψ u) : E₀.Space) (QuotientGroup.mk (ψ v)) ≤
      Real.exp ((t + B) ^ B) * delta := by
    apply hd.trans
    dsimp [delta]
    calc
      _ ≤ Real.exp ((t + B) ^ B) *
          dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
          Real.exp ((t + B) ^ B) * dist a b :=
        add_le_add le_rfl (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hNpos (show 0 ≤ dist a b from dist_nonneg))
      _ = _ := (mul_add _ _ _).symm
  have hsmall : dist (QuotientGroup.mk (ψ u) : E₀.Space) (QuotientGroup.mk (ψ v)) <
      Real.exp (-((p + A) ^ A)) := by
    apply hbound.trans_lt
    calc
      _ < Real.exp ((t + B) ^ B) * Real.exp (-((p + C) ^ C)) :=
        mul_lt_mul_of_pos_left hnear (Real.exp_pos _)
      _ = Real.exp ((t + B) ^ B - (p + C) ^ C) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  apply (hlocal u v hsmall).trans
  calc
    _ ≤ Real.exp ((p + A) ^ A) * (Real.exp ((t + B) ^ B) * delta) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = Real.exp ((p + A) ^ A + (t + B) ^ B) * delta := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hABC) hdelta

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_factorwise_subgroup_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {M : Type*} [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d : ι → ℕ} {e : ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (V : RationalFilteredNilmanifold M s e) (φ : M →ₗ⁅ℚ⁆ (∀ i, L i)),
      Function.Injective φ → ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (pi D).GeometryComplexityLE p →
      V.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi D).basis.repr (φ (V.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
          ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
          ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        (pi E).GeometryComplexityLE ((p + C) ^ C) ∧
        letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
        letI := V.metricSpace
        let ψ := realificationMap (hnil := V.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi D).filtration.lowerCentralSeries_eq_bot) φ
        ∀ κ : (pi D).RealGroup, κ ∈ (pi D).realLattice → ∀ r : (pi D).RealGroup,
          ((pi D).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ a b x y : (pi D).RealGroup, ∀ u v : V.RealGroup,
            (∀ i, |((pi D).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            a * x * (κ⁻¹ * r) = ψ u → b * y * (κ⁻¹ * r) = ψ v →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              (∀ i, dist (QuotientGroup.mk (productProjectionHom D i x) : (E i).Space)
                (QuotientGroup.mk (productProjectionHom D i y)) ≤ ρ) →
              (∀ i,
                letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
                  ((D i).basis.baseChange ℝ)
                dist (productProjectionHom D i a) (productProjectionHom D i b) ≤ ρ) →
              dist (QuotientGroup.mk u : V.Space) (QuotientGroup.mk v) ≤ Real.exp ((p + C) ^ C) * ρ := by
  obtain ⟨A, _, hrecovery⟩ := exists_uniform_subgroup_recovery s k
  obtain ⟨B, _, hfactor⟩ := exists_native_factorwise_covers
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let F := (X + 4) ^ 4 + 1
  let P := T + (T + Polynomial.C B) ^ B + F + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ d e D V φ hφ p hp hι hD hprod hV hheight q hq hqp
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin₀, hout₀, hQ, hrecover⟩ :=
    hrecovery V (pi D) φ hφ hp hV hprod hheight q hq hqp
  let Q := (pi D).withLattice Λ m hm hin₀ hout₀
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨Δ, N, hN, hin, hout, hindex, hE, hpi, hsub⟩ :=
    hfactor D Λ m hm hin₀ ht (hι.trans hpt) (fun i => (hD i).mono (D i) hpt)
      (hQ.2.1.trans (Real.exp_le_exp.mpr hAt))
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  have hsum : t + (t + B) ^ B + ((p + 4) ^ 4 + 1) + 1 ≤ (p + C) ^ C := by
    simpa [P, F, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (t + B) ^ B ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (p + 4) ^ 4 from by positivity]
  have hAC : (p + A) ^ A + ((p + 4) ^ 4 + 1) + 1 ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + B) ^ B from by positivity]
  refine ⟨Δ, N, hN, hin, hout, ?_, fun i => (hE i).mono (E i) hBC, hpi.mono (pi E) hBC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hi⟩
    exact ⟨hle, hchar, hnormal, hfinite, hi.trans (Real.exp_le_exp.mpr hBC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  let := Q.metricSpace
  let := (pi E).metricSpace
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  dsimp only
  intro κ hκ r hr a b x y u v ha hu hv ρ hρ hsmall hinput hleft
  have hcoord : dist (productSpaceEquiv E (QuotientGroup.mk x))
      (productSpaceEquiv E (QuotientGroup.mk y)) ≤ ρ := (dist_pi_le_iff hρ).mpr hinput
  have hfull := (productSpaceEquiv_symm_lipschitz E).dist_le_mul
    (productSpaceEquiv E (QuotientGroup.mk x)) (productSpaceEquiv E (QuotientGroup.mk y))
  simp only [Equiv.symm_apply_apply] at hfull
  have hprojection : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) ≤
      dist (QuotientGroup.mk x : (pi E).Space) (QuotientGroup.mk y) := by
    have h := (sublatticeProjection_lipschitz Q (pi E) hsub rfl).dist_le_mul
      (QuotientGroup.mk x) (QuotientGroup.mk y)
    change dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) ≤
      (1 : ℝ) * dist (QuotientGroup.mk x : (pi E).Space) (QuotientGroup.mk y) at h
    simpa only [one_mul] using h
  have hcovered : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) ≤
      (productMetricBound d : ℝ) * ρ :=
    hprojection.trans (hfull.trans (mul_le_mul_of_nonneg_left hcoord (productMetricBound d).coe_nonneg))
  have hleftbound := native_product_group_dist_le D a b hρ hleft
  have hK : 2 * (productMetricBound d : ℝ) ≤ Real.exp ((p + 4) ^ 4 + 1) := by
    calc
      _ ≤ Real.exp 1 * Real.exp ((p + 4) ^ 4) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (1 : ℝ)])
          (productMetricBound_le_exp d hp hι (fun i => (hD i).1))
          (productMetricBound d).coe_nonneg (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have htotal : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b ≤
      Real.exp ((p + 4) ^ 4 + 1) * ρ := by
    calc
      _ ≤ (productMetricBound d : ℝ) * ρ + (productMetricBound d : ℝ) * ρ :=
        add_le_add hcovered hleftbound
      _ = (2 * (productMetricBound d : ℝ)) * ρ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hρ
  have hnear : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b <
      Real.exp (-((p + A) ^ A)) := by
    calc
      _ ≤ Real.exp ((p + 4) ^ 4 + 1) * ρ := htotal
      _ ≤ Real.exp ((p + 4) ^ 4 + 1) * Real.exp (-((p + C) ^ C)) :=
        mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
      _ = Real.exp (((p + 4) ^ 4 + 1) - (p + C) ^ C) := by
        rw [← Real.exp_add, sub_eq_add_neg]
      _ < _ := Real.exp_lt_exp.mpr (by linarith)
  apply (hrecover κ hκ r hr a b x y u v ha hu hv hnear).trans
  calc
    _ ≤ Real.exp ((p + A) ^ A) * (Real.exp ((p + 4) ^ 4 + 1) * ρ) :=
      mul_le_mul_of_nonneg_left htotal (Real.exp_pos _).le
    _ = Real.exp ((p + A) ^ A + ((p + 4) ^ 4 + 1)) * ρ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hρ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_square_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)] {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
        (m : ℕ) (hm : 0 < m)
        (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates
          (D.filtration.squareFinBasis b w (hF 2)) (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hF 2))
          (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid m),
        let V := D.filtration.squareFiltration.ofAdaptedBasis
          (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
          (D.filtration.squareFinBasis_layers b w hF)
          (D.filtration.squareLattice D.lattice) m hm hin hout
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        V.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
          (hl : ∀ i, 0 < l i)
          (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
          (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
          let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
          (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
            ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
            ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
          letI := V.metricSpace
          ∀ ε γ : D.RealGroup, γ ∈ D.realLattice →
            (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            ∀ a b c d : D.RealGroup, ∀ u v : D.filtration.squareFiltration.realification.Group,
              D.filtration.realSquareFstHom u = ε⁻¹ * a * γ⁻¹ →
              D.filtration.realSquareSndHom u = b →
              D.filtration.realSquareFstHom v = ε⁻¹ * c * γ⁻¹ →
              D.filtration.realSquareSndHom v = d →
              ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
                dist (QuotientGroup.mk a : (E true).Space) (QuotientGroup.mk c) ≤ ρ →
                dist (QuotientGroup.mk b : (E false).Space) (QuotientGroup.mk d) ≤ ρ →
                dist (QuotientGroup.mk u : V.Space) (QuotientGroup.mk v) ≤
                  Real.exp ((p + C) ^ C) * ρ := by
  obtain ⟨A, _, hrecovery⟩ := exists_factorwise_subgroup_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let S := ((X + 3) ^ 11 + 2 * X + 5) ^ 11
  let T := X + S + (X + 4) ^ 2 + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D _ _ _ _ p hp hD
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨b, w, hF, m, hm, hin, hout, hb, hV⟩ := D.exists_controlled_square_geometry hp0 hD
  let V := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) m hm hin hout
  let D₂ := fun _ : Bool => D
  let : FiniteDimensional ℚ (Bool → L) := (productFinBasis D₂).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Bool → L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Bool → L)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (Bool → L)) := realification_moduleTopology_t2 (productFinBasis D₂)
  let r := p + squareGeometryBudget p + (p + 4) ^ 2 + 2
  have hS : 0 ≤ squareGeometryBudget p := squareGeometryBudget_nonneg hp0
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 4)]
  have hpr2 : p + 2 ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 4)]
  have hSr : squareGeometryBudget p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 4)]
  have hrr : (p + 2) ^ 2 ≤ r := by dsimp [r]; nlinarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hbool : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  have hprod := (pi_geometry D₂ hp0 hbool (fun _ => hD)).mono (pi D₂) hrr
  have hmatrix : ∀ i j, rationalLogHeight ((pi D₂).basis.repr
      (D.filtration.squarePairMap (V.basis j)) i) ≤ r := by
    intro i j
    exact (D.squarePairMap_matrix_logHeight b w (hF 2) (by linarith : 0 ≤ p + 1)
      (fun i j => hb j i) i j).trans (by linarith)
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hE, _, hrecover⟩ :=
    hrecovery D₂ V D.filtration.squarePairMap D.filtration.squarePairMap_injective
      hr (hbool.trans hpr) (fun _ => hD.mono D hpr) hprod (hV.mono V hSr) hmatrix
      1 (by decide) (by simpa only [Nat.cast_one] using Real.one_le_exp hr)
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have hsum : r + (r + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, S, T, r, squareGeometryBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hAC : (r + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  have hrC : r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  refine ⟨b, w, hF, m, hm, hin, hout, fun i j => (hb i j).trans (by linarith),
    hV.mono V (hSr.trans hrC),
    Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hAC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hbound⟩
    exact ⟨hle, hchar, hnormal, hfinite, hbound.trans (Real.exp_le_exp.mpr hAC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  dsimp only
  intro ε γ hγ hε a b c d u v huf hus hvf hvs ρ hρ hsmall hfirst hsecond
  let e := realBCHPiEquiv (fun _ : Bool => D.filtration)
  let K := e.symm (fun flag => cond flag γ 1)
  let B := e.symm (fun flag => cond flag ε⁻¹ 1)
  let P := e.symm (fun flag => cond flag a b)
  let Q := e.symm (fun flag => cond flag c d)
  have hK : K ∈ (pi D₂).realLattice := by
    apply pi_symm_mem_realLattice D₂
    intro flag
    cases flag
    · exact D.realLattice.one_mem
    · exact hγ
  have hgrid : ((pi D₂).basis.baseChange ℝ).equivFun (1 : (pi D₂).RealGroup).coord ∈
      realDenominatorGrid 1 := by
    refine ⟨fun _ => 0, ?_⟩
    simp only [coord_one, map_zero, Nat.cast_one, one_smul, Int.cast_zero, Pi.zero_def]
  have hB : ∀ i, |((pi D₂).basis.baseChange ℝ).repr B.coord i| ≤ Real.exp ((r + 2) ^ k) := by
    intro i
    exact (D.squareNormalizer_coordinate_bound ε (Real.exp_pos _).le hε i).trans
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) k))
  have hu : B * P * (K⁻¹ * 1) = D.filtration.realSquarePairHom u := by
    simpa only [mul_one] using D.filtration.realSquarePairHom_normalization ε γ a b u huf hus
  have hv : B * Q * (K⁻¹ * 1) = D.filtration.realSquarePairHom v := by
    simpa only [mul_one] using D.filtration.realSquarePairHom_normalization ε γ c d v hvf hvs
  have hnear : ρ ≤ Real.exp (-((r + A) ^ A)) :=
    hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hAC))
  have hP (flag : Bool) : productProjectionHom D₂ flag P = cond flag a b :=
    productProjectionHom_pi_symm D₂ (fun flag => cond flag a b) flag
  have hQ (flag : Bool) : productProjectionHom D₂ flag Q = cond flag c d :=
    productProjectionHom_pi_symm D₂ (fun flag => cond flag c d) flag
  have hinput : ∀ i, dist (QuotientGroup.mk (productProjectionHom D₂ i P) : (E i).Space)
      (QuotientGroup.mk (productProjectionHom D₂ i Q)) ≤ ρ := by
    intro flag
    rw [hP, hQ]
    cases flag
    · exact hsecond
    · exact hfirst
  have hd := hrecover K hK 1 hgrid B B P Q u v hB hu hv ρ hρ hnear hinput
    (fun _ => by simpa only [dist_self] using hρ)
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAC) hρ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
