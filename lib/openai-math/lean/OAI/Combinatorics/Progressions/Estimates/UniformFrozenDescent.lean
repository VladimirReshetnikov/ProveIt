/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.FixedObservableMarkedFiberGlobalLift
import OAI.Combinatorics.Progressions.Nilpotent.FrozenComplexNiltest

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def topQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ F.layerIdeal (s + 1)) s
      (Fintype.card {i : Fin d // ¬ s + 1 ≤ w i}) :=
  F.coordinateQuotientModel b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout

theorem topQuotientModel_geometry (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N)
    {p : ℝ} (hp : 0 ≤ p)
    (hgeom : (F.ofAdaptedBasis b w hlayers Γ N hN hin hout).GeometryComplexityLE p) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).GeometryComplexityLE p := by
  apply F.coordinateQuotientModel_geometry b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout hp
  · simpa only [Fintype.card_fin] using hgeom.1
  · exact hgeom.2.1
  · exact hgeom.2.2.1

@[simp] theorem topQuotientModel_filtration (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).filtration = F.quotientTop := rfl

@[simp] theorem topQuotientModel_lattice (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).lattice =
      Γ.map (F.quotientStepHom (F.layerIdeal (s + 1)) le_rfl) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem quotientFinBasis_repr_mk {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (b : Basis ι ℚ L) (I : LieIdeal ℚ L) (S : Set ι) [DecidablePred (· ∈ S)]
    (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))
    (x : L) (k : Fin (Fintype.card {i // i ∉ S})) :
    (quotientFinBasis b I S hspan).repr (lieQuotientMap I x) k =
      b.repr x ((Fintype.equivFin {i // i ∉ S}).symm k) := by
  rw [quotientFinBasis, Basis.repr_reindex_apply]
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hspan x _

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_quotient {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
        Q.filtration = D.filtration.quotientTop ∧
        Q.lattice = D.lattice.map
          (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
        Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
        (∀ i k, rationalLogHeight (Q.basis.repr
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis i)) k) ≤ (p + 3) ^ 5) ∧
        ∃ w : Fin n → ℕ, ∀ j, Q.filtration.layer j = Submodule.span ℚ (Q.basis '' {i | j ≤ w i}) := by
  classical
  obtain ⟨b, w, N, _, _, hF, _, hinverse, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let Q := D.filtration.topQuotientModel b w hF D.lattice N hN hin hout
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hn : Fintype.card {i : Fin (finrank ℚ L) // ¬ s + 1 ≤ w i} ≤ d := by
    simpa only [Fintype.card_fin, hdim] using
      Fintype.card_subtype_le (fun i : Fin (finrank ℚ L) => ¬ s + 1 ≤ w i)
  have hp1 : 0 ≤ p + 1 := by linarith
  have hpPow : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget hp1 (by decide : 1 ≤ 11))
  have hpr : p ≤ (p + 3) ^ 11 := (by linarith : p ≤ p + 1).trans hpPow
  have hbase : 1 ≤ p + 3 := by linarith
  have h9 : (p + 3) ^ 9 ≤ (p + 3) ^ 11 := pow_le_pow_right₀ hbase (by decide)
  have hgeom : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.topQuotientModel_geometry b w hF D.lattice N hN hin hout (by positivity)
    apply D.filtration.ofAdaptedBasis_geometry b w hF D.lattice N hN hin hout (by positivity)
    · exact (by simpa only [hdim] using hD.1 : (finrank ℚ L : ℝ) ≤ p).trans hpr
    · exact hNp.trans (Real.exp_le_exp.mpr h9)
    · exact hbracket
  refine ⟨_, hn, Q, rfl, rfl, hgeom, ?_, quotientFinWeight w {i | s + 1 ≤ w i}, ?_⟩
  · intro i k
    have hspan : (D.filtration.layerIdeal (s + 1)).toSubmodule =
        Submodule.span ℚ (b '' {i | s + 1 ≤ w i}) := hF (s + 1)
    have hcoord := quotientFinBasis_repr_mk b (D.filtration.layerIdeal (s + 1))
      {i | s + 1 ≤ w i} hspan (D.basis i) k
    exact (congrArg rationalLogHeight hcoord).le.trans (hinverse i _)
  · intro j
    exact D.filtration.quotientFinBasis_layers b w hF (D.filtration.layerIdeal (s + 1)) le_rfl
      {i | s + 1 ≤ w i} (hF (s + 1)) j

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

theorem exists_controlled_reduced_square_geometry {p : ℝ}
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom⟩ :=
    D.exists_controlled_square_geometry hp hD
  exact ⟨b, w, hlayers, N, hN, hin, hout, hb, hgeom,
    D.filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _
      (squareGeometryBudget_nonneg hp) hgeom⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_controlled_top_subspace_quotient
    {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (vK : κ → K) (hspanK : Submodule.span ℚ (Set.range vK) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hvK : ∀ j i, rationalLogHeight (D.basis.repr (vK j : L) i) ≤ p) :
    let I := D.filtration.topSubspaceIdeal K hK
    let hI : D.filtration.layer (s + 1) ≤ I.toSubmodule := by rw [D.filtration.terminal]; exact bot_le
    ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ I) s n,
      Q.filtration = D.filtration.quotientLie I hI ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI) ∧
      Q.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis i)) j) ≤ (p + 3) ^ 5 := by
  classical
  intro I hI
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  obtain ⟨b, w, S, hw, hcentral, hb, hlayers, hKS⟩ :=
    D.filtration.exists_bounded_adapted_basis_with_top_subspace hs D.basis
      (fun i => D.layerBasis i) (fun i => (D.layerBasis i).span_eq) K hK vK hspanK
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.2 i j k))
      (fun j i => rationalHeightLE_ceil_exp (hvK j i))
  have hdim : finrank ℚ L = d := by simpa only [Fintype.card_fin] using finrank_eq_card_basis D.basis
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by simpa only [hdim] using hd
  obtain ⟨N, hN, hNp, hin, hout⟩ := exists_basis_change_grid_exp_bound D.basis b D.lattice
    hH D.grid_pos hb D.inner_grid D.outer_grid (by linarith : 0 ≤ p + 1) hd hr hHp
    (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  have hbinv := inverse_basis_entries_height D.basis b hH hb
  have hc := basis_change_structure_height D.basis b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hcb := rationalLieStructureHeight_inverse_budget (Fintype.card (Fin d))
    (Fintype.card (Fin (finrank ℚ L))) H (by linarith : 0 ≤ p + 1) hd hr hHp
  have hsolve := rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H
    (by linarith : 0 ≤ p + 1) hr hHp
  have hspanI : I.toSubmodule = Submodule.span ℚ (b '' S) := hKS
  let Q := D.filtration.coordinateQuotientModel b w hlayers I hI S hspanI D.lattice N hN hin hout
  have hbig : p + 1 ≤ (p + 3) ^ 11 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      le_power_budget (by linarith : 0 ≤ p + 1) (by decide : 1 ≤ 11)
  have hgeometry : Q.GeometryComplexityLE ((p + 3) ^ 11) := by
    apply D.filtration.coordinateQuotientModel_geometry b w hlayers I hI S hspanI
      D.lattice N hN hin hout (by positivity) (hr.trans hbig)
    · apply hNp.trans (Real.exp_le_exp.mpr ?_)
      rw [show p + 1 + 2 = p + 3 by ring]
      exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 9 ≤ 11)
    · intro i j k
      apply rationalLogHeight_le_of_height (hc i j k)
      simpa only [show p + 1 + 2 = p + 3 by ring] using hcb
  refine ⟨_, ?_, Q, rfl, rfl, hgeometry, ?_⟩
  · simpa only [Fintype.card_fin, hdim] using Fintype.card_subtype_le (fun i => i ∉ S)
  · intro i j
    have hcoord := quotientFinBasis_repr_mk b I S hspanI (D.basis i) j
    change rationalLogHeight ((quotientFinBasis b I S hspanI).repr (lieQuotientMap I (D.basis i)) j) ≤ _
    rw [hcoord]
    apply rationalLogHeight_le_of_height (hbinv i _)
    simpa only [show p + 1 + 2 = p + 3 by ring] using hsolve

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_topQuotientOtherTarget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] {H : Type u} {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {s d : ℕ} {e : ι → ℕ} (D : RationalFilteredNilmanifold H (s + 1) d)
      (E : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (e i))
      (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (E i).GeometryComplexityLE p) →
      (∀ a i j, rationalLogHeight ((E a).basis.repr (ψ a (D.basis j)) i) ≤ p) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (H ⧸ D.filtration.layerIdeal (s + 1)) s n,
          Q.filtration = D.filtration.quotientTop ∧
          Q.lattice = D.lattice.map
            (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          (optionProduct (Q.raiseStep (Nat.le_succ s)) E).GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ i j, rationalLogHeight ((optionProduct (Q.raiseStep (Nat.le_succ s)) E).basis.repr
            (optionProductMap (lieQuotientMap (D.filtration.layerIdeal (s + 1))) ψ (D.basis j)) i) ≤
              (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11
  let P := R + (R + 3) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ H L _ _ _ _ s d e D E ψ p hp hD hι hE hψ
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ := D.exists_controlled_top_quotient hp hD
  let t := (p + 3) ^ 11
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    apply (show p ≤ p + 3 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (show 1 ≤ 11 by omega)
  have h5 : (p + 3) ^ 5 ≤ t := pow_le_pow_right₀ (by linarith) (by omega)
  have hsum : t + (t + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hsum
  have htargetC : (t + 3) ^ 2 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hgeom := optionProduct_geometry (Q.raiseStep (Nat.le_succ s)) E ht (hι.trans hpt)
    (Q.raiseStep_geometry (Nat.le_succ s) hQ) (fun i => (hE i).mono (E i) hpt)
  refine ⟨n, hn, Q, hQF, hQL, hQ.mono Q htC, hgeom.mono _ htargetC, ?_⟩
  intro i j
  apply (optionProductMap_logHeight (Q.raiseStep (Nat.le_succ s)) E D.basis
    (lieQuotientMap (D.filtration.layerIdeal (s + 1))) ψ
    (fun i j => (hproj j i).trans h5) (fun a i j => (hψ a i j).trans hpt) i j).trans htC

theorem topQuotientOtherMap_real_kernel {ι : Type v} [Fintype ι]
    {H : Type u} {L : ι → Type u} [LieRing H] [LieAlgebra ℚ H]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s d n : ℕ} {e : ι → ℕ}
    (D : RationalFilteredNilmanifold H (s + 1) d)
    (Q : RationalFilteredNilmanifold (H ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (E : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (e i))
    (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : ℝ ⊗[ℚ] H) :
    realificationLieHom (optionProductMap (lieQuotientMap (D.filtration.layerIdeal (s + 1))) ψ) x = 0 ↔
      x ∈ D.filtration.realification.layer (s + 1) ∧ ∀ i, realificationLieHom (ψ i) x = 0 := by
  rw [optionProductMap_real_kernel (Q.raiseStep (Nat.le_succ s)) E]
  exact and_congr (realification_mkQ_eq_zero_iff (D.filtration.layerIdeal (s + 1)).toSubmodule x) Iff.rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_constructed_fixedObservable_topInvariant_descent (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ τ Ω : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      {v : σ → ℕ} {w : τ → ℕ} (T : D.Niltest v)
      (localTests : Ω → D.Niltest w),
      (∀ a, (localTests a).observable = T.observable) → T.UnitIntervalValued →
      ∀ p : ℝ, 0 ≤ p → T.ComplexityLE p →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
        ∃ hQF : Q.filtration = D.filtration.quotientTop,
          Q.lattice = D.lattice.map
            (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
          letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
          letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
            realification_moduleTopology_t2 Q.basis
          ∃ (S : Q.Niltest v) (quotientTests : Ω → Q.Niltest w),
            S.orbit = D.topQuotientOrbit Q hQF T.orbit ∧
            S.normBound = T.normBound ∧
            S.lipBound = rationalReconstructionLipschitzBound s d n
              ⌈Real.exp ((p + 3) ^ 11)⌉₊ T.lipBound T.normBound ∧
            S.UnitIntervalValued ∧ S.ComplexityLE ((p + C) ^ C) ∧
            (∀ g : D.RealGroup, S.observable (QuotientGroup.mk
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := Q.filtration.lowerCentralSeries_eq_bot)
                (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
              T.observable (QuotientGroup.mk g)) ∧
            (∀ x, S.eval x = T.eval x) ∧
            ∀ a, (quotientTests a).observable = S.observable ∧
              (quotientTests a).orbit = D.topQuotientOrbit Q hQF (localTests a).orbit ∧
              (quotientTests a).normBound = S.normBound ∧
              (quotientTests a).lipBound = S.lipBound ∧
              (quotientTests a).UnitIntervalValued ∧
              (quotientTests a).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (quotientTests a).eval x = (localTests a).eval x := by
  obtain ⟨a, _, hdescent⟩ := exists_fixedObservable_topInvariant_descent_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L σ τ Ω _ _ _ _ _ _ d D v w T localTests hcommon hunit p hp hT hinv
  let q := (p + 3) ^ 11
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + 3 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 1 ≤ 11)
  obtain ⟨n, hn, Q, hQF, hQL, hQ, he, _⟩ := D.exists_controlled_top_quotient hp hT.1
  have heq : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ q := by
    intro i j
    exact (he j i).trans (pow_le_pow_right₀
      (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11))
  let _ := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let _ : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let _ : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  obtain ⟨S, quotientTests, hSo, hSn, hSl, hSu, hSc, hrec, hSe, hfamily⟩ :=
    hdescent D Q hQF hQL T localTests hcommon hunit q hq (hT.mono hpq) hQ heq hinv
  have hfinal : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, q, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, Q, hQF, hQL, S, quotientTests, hSo, hSn, hSl, hSu,
    hSc.mono hfinal, hrec, hSe, ?_⟩
  intro k
  obtain ⟨hobs, ho, hnorm, hlip, hu, hc, heval⟩ := hfamily k
  exact ⟨hobs, ho, hnorm, hlip, hu, hc.mono hfinal, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_frozen_descent (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e) (φ : L →ₗ⁅ℚ⁆ M)
      {w : σ → ℕ} (T : E.Niltest w)
      (g : D.filtration.realification.PolynomialOrbit w) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → T.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ d ∧
          ∃ Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n,
            ∃ hQF : Q.filtration = D.filtration.quotientTop,
              Q.lattice = Λ.map
                (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
              Q.GeometryComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∀ a r : E.RealGroup,
                 (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
                 (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
                 (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x : D.RealGroup,
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * r)) =
                   T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * r))) →
                 ∃ S : Q.Niltest w, S.orbit = D.topQuotientOrbit Q hQF g ∧
                   S.normBound = T.normBound ∧ S.ComplexityLE ((p + C) ^ C) ∧
                   ∀ x : σ → ℤ, S.eval x = T.observable (QuotientGroup.mk
                     (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                       (hM := E.filtration.lowerCentralSeries_eq_bot) φ
                       (D.filtration.realification.polynomialOrbitEval w x g) * r))) := by
  obtain ⟨A, _, hmaps⟩ := exists_uniform_frozen_map (s + 1) k
  obtain ⟨B, _, hdesc⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := X + U + 4
  let R := P + (P + 3) ^ 11 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L M σ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w T g p hp hD hT hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hF, hmap⟩ :=
    hmaps D E φ p hp hD hT.1 hφ q hq hqp
  let F := D.withLattice Λ N hN hin hout
  let u := (p + A) ^ A
  let t := p + u + 4
  let r := t + (t + 3) ^ 11 + 4
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hut : u ≤ t := by dsimp [t]; linarith
  have htr : t ≤ r := by dsimp [r]; linarith [pow_nonneg (by linarith : 0 ≤ t + 3) 11]
  have hr : 0 ≤ r := ht.trans htr
  have hQr : (t + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hsum : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, P, U, X, r, t, u, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ :=
    F.exists_controlled_top_quotient ht (hF.mono F hut)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr ((hut.trans htr).trans hrC)),
    n, hn, Q, hQF, hQL, hQ.mono Q (hQr.trans hrC), ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ F.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  intro a b ha hb hinvariant
  obtain ⟨hconj, K, hK, hKlip⟩ := hmap a b ha hb
  let T' := F.frozenComplexNiltest E φ a b hconj T g K hKlip
  have hT' : T'.ComplexityLE t :=
    F.frozenComplexNiltest_complexity E φ a b hconj T g K hKlip hp hu hF hT hK
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  obtain ⟨S, hSo, hSn, hSc, hSe⟩ := hdesc F Q hQF hQL T' r hr (hT'.mono htr)
    (hQ.mono Q hQr) (fun i j => (hproj j i).trans (h5.trans hQr))
    (F.frozenComplexNiltest_top_invariant E φ a b hconj T g K hKlip hinvariant)
  refine ⟨S, hSo, hSn, hSc.mono hcost, ?_⟩
  intro x
  exact (hSe x).trans (F.frozenComplexNiltest_eval E φ a b hconj T g K hKlip x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
