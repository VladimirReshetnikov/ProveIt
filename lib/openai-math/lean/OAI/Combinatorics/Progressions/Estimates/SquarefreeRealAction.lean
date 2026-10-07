/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.Core
import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Dynamics.SquarefreeModelBudget
import OAI.Combinatorics.Progressions.Estimates.RealificationFixedSubmodule
import OAI.Combinatorics.Progressions.Lattices.NativeSquarefreeLattice
import OAI.Combinatorics.Progressions.Linear.ComparisonBasisBudget
import OAI.Combinatorics.Progressions.Nilpotent.BlockLayerBracket

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraph (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] (L × F.SquarefreeAlgebra π) :=
  (F.layer a).subtype.prod (F.blockLayerMap π a ha)

theorem comparisonGraph_apply (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonGraph π a ha x = (x.val, F.blockLayerMap π a ha x) := rfl

theorem comparisonGraph_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a)
    (n : ℕ) (hn : n ≤ ∑ i, a i) :
    F.comparisonGraph π a ha x ∈ (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n) :=
  ⟨F.ordinary.antitone hn (F.layer_le_ordinary a x.property),
    F.squarefreeDegreeLayer_antitone π hn (F.blockLayerMap_mem_degree π a ha x)⟩

theorem comparisonGraph_lie (a b : σ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (x : F.layer a) (y : F.layer b) :
    ⁅F.comparisonGraph π a ha x, F.comparisonGraph π b hb y⁆ =
      F.comparisonGraph π (a + b) hab ⟨⁅x.val, y.val⁆, F.lie_mem x.property y.property⟩ :=
  Prod.ext rfl (F.blockLayerMap_lie π a b ha hb hab x y)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraphLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) := by
  classical
  exact ⨆ a : {a : σ → ℕ // a ≠ 0},
    if n ≤ ∑ i, a.val i then LinearMap.range (F.comparisonGraph π a.val a.property) else ⊥

theorem comparisonGraph_mem_graphLayer (n : ℕ) (a : σ → ℕ) (ha : a ≠ 0)
    (hn : n ≤ ∑ i, a i) (x : F.layer a) :
    F.comparisonGraph π a ha x ∈ F.comparisonGraphLayer π n := by
  classical
  have hle : LinearMap.range (F.comparisonGraph π a ha) ≤ F.comparisonGraphLayer π n := by
    unfold comparisonGraphLayer
    apply le_iSup_of_le (⟨a, ha⟩ : {a : σ → ℕ // a ≠ 0})
    rw [ite_eq_left hn]
  exact hle ⟨x, rfl⟩

theorem comparisonGraphLayer_induction (n : ℕ) {P : L × F.SquarefreeAlgebra π → Prop}
    {x : L × F.SquarefreeAlgebra π} (hx : x ∈ F.comparisonGraphLayer π n)
    (hgraph : ∀ (a : σ → ℕ) (ha : a ≠ 0), n ≤ ∑ i, a i →
      ∀ y : F.layer a, P (F.comparisonGraph π a ha y))
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
  classical
  refine Submodule.iSup_induction (motive := P) _ hx ?_ hzero hadd
  intro a y hy
  by_cases hn : n ≤ ∑ i, a.val i
  · rw [ite_eq_left hn] at hy
    obtain ⟨z, rfl⟩ := hy
    exact hgraph a.val a.property hn z
  · rw [ite_eq_right hn, Submodule.mem_bot] at hy
    simpa only [hy] using hzero

theorem comparisonGraphLayer_antitone : Antitone (F.comparisonGraphLayer π) := by
  intro n m hnm x hx
  apply F.comparisonGraphLayer_induction π m hx
  · intro a ha hm y
    exact F.comparisonGraph_mem_graphLayer π n a ha (hnm.trans hm) y
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

theorem comparisonGraphLayer_le_degree (n : ℕ) :
    F.comparisonGraphLayer π n ≤ (F.ordinary.layer n).prod (F.squarefreeDegreeLayer π n) := by
  intro x hx
  apply F.comparisonGraphLayer_induction π n hx
  · intro a ha hn y
    exact F.comparisonGraph_mem_degree π a ha y n hn
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonLayer (n : ℕ) : Submodule ℚ (L × F.SquarefreeAlgebra π) :=
  F.comparisonProductLayer π (n + 1) ⊔ F.comparisonGraphLayer π n

theorem comparisonLayer_antitone : Antitone (F.comparisonLayer π) := by
  intro n m h
  exact sup_le_sup (F.comparisonProductLayer_antitone π (Nat.add_le_add_right h 1))
    (F.comparisonGraphLayer_antitone π h)

theorem comparisonLayer_le_product (n : ℕ) :
    F.comparisonLayer π n ≤ F.comparisonProductLayer π n :=
  sup_le (F.comparisonProductLayer_antitone π (Nat.le_succ n)) (F.comparisonGraphLayer_le_degree π n)

theorem comparisonLayer_zero : F.comparisonLayer π 0 = ⊤ := by
  rw [comparisonLayer, zero_add, F.comparisonProductLayer_one, top_sup_eq]

theorem comparisonLayer_terminal : F.comparisonLayer π (max s (Fintype.card ι) + 1) = ⊥ := by
  apply bot_unique
  exact (F.comparisonLayer_le_product π _).trans (F.comparisonProductLayer_terminal π).le

theorem comparisonGraph_mem_layer (n : ℕ) (a : σ → ℕ) (ha : a ≠ 0)
    (hn : n ≤ ∑ i, a i) (x : F.layer a) :
    F.comparisonGraph π a ha x ∈ F.comparisonLayer π n :=
  (le_sup_right : F.comparisonGraphLayer π n ≤ F.comparisonLayer π n)
    (F.comparisonGraph_mem_graphLayer π n a ha hn x)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem map_mem_submodule_of_basis {κ V W : Type*} [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis κ ℚ V) (f : V →ₗ[ℚ] W) (P : Submodule ℚ W)
    (h : ∀ i, f (b i) ∈ P) (x : V) : f x ∈ P := by
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact P.smul_mem _ (h i)

namespace MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonLayer_le_of_generators (n : ℕ) (P : Submodule ℚ (L × F.SquarefreeAlgebra π))
    (hfirst : ∀ x ∈ F.ordinary.layer (n + 1), (x, 0) ∈ P)
    (hsecond : ∀ y ∈ F.squarefreeDegreeLayer π (n + 1), (0, y) ∈ P)
    (hgraph : ∀ (a : σ → ℕ) (ha : a ≠ 0), a ≤ bound → n ≤ ∑ i, a i →
      ∀ x : F.layer a, F.comparisonGraph π a ha x ∈ P) :
    F.comparisonLayer π n ≤ P := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  apply P.add_mem
  · simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      P.add_mem (hfirst u.1 hu.1) (hsecond u.2 hu.2)
  · refine F.comparisonGraphLayer_induction π n (P := fun v => v ∈ P) hv ?_ P.zero_mem ?_
    · intro a ha hn x
      by_cases hab : a ≤ bound
      · exact hgraph a ha hab hn x
      · have hx : x = 0 := by
          apply Subtype.ext
          exact (Submodule.mem_bot ℚ).mp (F.terminal a hab ▸ x.property)
        rw [hx, map_zero]
        exact P.zero_mem
    · exact fun x y hx hy => P.add_mem hx hy

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeFinBasis (p : ℝ) : Basis (Fin (Fintype.card M.SquarefreeBasisIndex)) ℚ
    (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :=
  (M.squarefreeBasis p).reindex (Fintype.equivFin M.SquarefreeBasisIndex)

theorem squarefreeFinBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p) (i j k) :
    RationalHeightLE (lieStructureConstants (M.squarefreeFinBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  rw [squarefreeFinBasis, lieStructureConstants_reindex]
  exact M.squarefreeBasis_structure_height hM _ _ _

theorem squarefreeFinBasis_multidegree_height (p : ℝ) (c : ReplicatedIndex bound → ℕ) (j k) :
    RationalHeightLE ((M.squarefreeFinBasis p).repr
      (M.filtration.squarefreeMultidegreeBasis (fun j : ReplicatedIndex bound => j.1)
        (M.squarefreeCoefficientBasis p) c j).val k) 1 := by
  rw [squarefreeFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.squarefreeMultidegreeBasis_height _ (M.squarefreeCoefficientBasis p) c j _

theorem squarefreeFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.squarefreeFinBasis p).repr
      (M.filtration.squarefreeDegreeBasis (fun j : ReplicatedIndex bound => j.1)
        (M.squarefreeCoefficientBasis p) n j).val k) 1 := by
  rw [squarefreeFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.squarefreeDegreeBasis_height _ (M.squarefreeCoefficientBasis p) n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem blockLayerMap_chosen_height (p : ℝ) (a : σ → ℕ) (ha : a ≠ 0)
    (j : Fin (finrank ℚ (M.filtration.layer a))) (k : M.SquarefreeBasisIndex) :
    RationalHeightLE ((M.squarefreeBasis p).repr
      (M.filtration.blockLayerMap (fun i : ReplicatedIndex bound => i.1) a ha
        (M.comparisonLayerBasis p a j)) k) (multidegreeFactorial a) := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let π := fun i : ReplicatedIndex bound => i.1
  let v := M.filtration.squarefreeAlgebraEquiv π
    (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)) k.1
  change RationalHeightLE
    ((chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊
      (M.filtration.squarefreeCoefficientLayer π k.1)).repr v k.2) _
  by_cases hka : blockDegree π k.1.val = a
  · have hk : k.1.val ≠ 0 := by
      intro h
      apply ha
      rw [h, blockDegree_zero] at hka
      exact hka.symm
    have hUV : M.filtration.layer a = M.filtration.squarefreeCoefficientLayer π k.1 := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ite_eq_right hk, hka]
    have hq : RationalHeightLE (multidegreeFactorial a : ℚ) (multidegreeFactorial a) := by
      constructor
      · simp
      · simpa using Nat.succ_le_of_lt (multidegreeFactorial_pos a)
    apply chosenBasis_smul_coordinate_height D.basis ⌈Real.exp p⌉₊
      (M.filtration.layer a) (M.filtration.squarefreeCoefficientLayer π k.1)
      hUV j v (multidegreeFactorial a) hq
    change squarefreePolynomialEquiv
      (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)).val k.1 = _
    rw [M.filtration.blockLayerMap_coe, factorialBlockMonomial_coefficient, ite_eq_left hka]
    rfl
  · have hv : v = 0 := by
      apply Subtype.ext
      change squarefreePolynomialEquiv
        (M.filtration.blockLayerMap π a ha (M.comparisonLayerBasis p a j)).val k.1 = 0
      rw [M.filtration.blockLayerMap_coe, factorialBlockMonomial_coefficient, ite_eq_right hka]
    rw [hv, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (multidegreeFactorial_pos a)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem comparisonGraph_chosen_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : σ → ℕ) (ha : a ≠ 0) (hab : a ≤ bound)
    (j : Fin (finrank ℚ (M.filtration.layer a)))
    (k : Fin d ⊕ Fin (Fintype.card M.SquarefreeBasisIndex)) :
    RationalHeightLE ((D.basis.prod (M.squarefreeFinBasis p)).repr
      (M.filtration.comparisonGraph (fun i : ReplicatedIndex bound => i.1) a ha
        (M.comparisonLayerBasis p a j)) k) (comparisonBasisHeight bound p) := by
  cases k with
  | inl k =>
      exact (M.comparisonLayerBasis_height hM a hab j k).mono
        (comparisonBasisHeight_ge_ceil bound p)
  | inr k =>
      change RationalHeightLE ((M.squarefreeFinBasis p).repr
        (M.filtration.blockLayerMap (fun i : ReplicatedIndex bound => i.1) a ha
          (M.comparisonLayerBasis p a j)) k) _
      rw [squarefreeFinBasis, Basis.repr_reindex_apply]
      exact (M.blockLayerMap_chosen_height p a ha j _).mono
        ((multidegreeFactorial_mono hab).trans (comparisonBasisHeight_ge_factorial bound p))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeModel (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B) :
    RationalFilteredNilmanifold (M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
      (Fintype.card (ReplicatedIndex bound)) (Fintype.card M.SquarefreeBasisIndex) where
  filtration := M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)
  basis := M.squarefreeFinBasis p
  layerBasis i := M.filtration.squarefreeDegreeBasis (fun j : ReplicatedIndex bound => j.1)
    (M.squarefreeCoefficientBasis p) (i.val + 1)
  lattice := M.squarefreeLattice p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.squarefreeLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.squarefreeLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def squarefreeModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    (M.squarefreeModel p B hB hstable).MultidegreeStructure (fun _ : ReplicatedIndex bound => 1) where
  filtration := M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)
  ordinary := rfl
  basis a := M.filtration.squarefreeMultidegreeBasis (fun j : ReplicatedIndex bound => j.1)
    (M.squarefreeCoefficientBasis p) (fun j => (a j).val)

theorem squarefreeModel_complexity {p q : ℝ} (hM : M.ComplexityLE p) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) (hq : 0 ≤ q)
    (hd : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ q) (hBq : (B : ℝ) ≤ Real.exp q)
    (hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q) :
    (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE q := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_one]
    exact Real.one_le_exp_iff.mpr hq
  refine ⟨⟨hd, hBq, ?_, ?_⟩, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (M.squarefreeFinBasis_structure_height hM i j k) hHq
  · intro i j k
    exact rationalLogHeight_le_of_height (M.squarefreeFinBasis_degree_height p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.squarefreeFinBasis_multidegree_height p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_layer_basis_height {p : ℝ} (hM : M.ComplexityLE p) (n : ℕ) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n))) ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n),
      ∀ j k, RationalHeightLE
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val k)
        (comparisonBasisHeight bound p) := by
  classical
  let π := fun i : ReplicatedIndex bound => i.1
  let A := M.filtration.SquarefreeAlgebra π
  let e := D.basis.prod (M.squarefreeFinBasis p)
  let U := M.filtration.comparisonLayer π n
  let S : Set (L × A) := {z | z ∈ U ∧ ∀ k,
    RationalHeightLE (e.repr z k) (comparisonBasisHeight bound p)}
  have hpos := comparisonBasisHeight_pos bound p
  have hspan : Submodule.span ℚ S = U := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (fun z hz => hz.1)
    · apply M.filtration.comparisonLayer_le_of_generators π n
      · intro x hx
        obtain ⟨b, hb⟩ : ∃ b : Basis
            (Fin (finrank ℚ (M.filtration.ordinary.layer (n + 1)))) ℚ
            (M.filtration.ordinary.layer (n + 1)),
            ∀ j k, rationalLogHeight (D.basis.repr (b j).val k) ≤ p := by
          rw [M.ordinary]
          exact D.exists_positive_layer_basis (n + 1) (by omega) hM.1
        let f := (LinearMap.inl ℚ L A).comp (M.filtration.ordinary.layer (n + 1)).subtype
        apply map_mem_submodule_of_basis b f (Submodule.span ℚ S) _ ⟨x, hx⟩
        intro j
        apply Submodule.subset_span
        refine ⟨?_, ?_⟩
        · exact (le_sup_left : M.filtration.comparisonProductLayer π (n + 1) ≤ U)
            ⟨(b j).property, Submodule.zero_mem _⟩
        · intro k
          cases k with
          | inl k =>
              exact (rationalHeightLE_ceil_exp (hb j k)).mono
                (comparisonBasisHeight_ge_ceil bound p)
          | inr k =>
              change RationalHeightLE ((M.squarefreeFinBasis p).repr 0 k) _
              simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hpos
      · intro y hy
        let b := M.filtration.squarefreeDegreeBasis π (M.squarefreeCoefficientBasis p) (n + 1)
        let f := (LinearMap.inr ℚ L A).comp (M.filtration.squarefreeDegreeLayer π (n + 1)).subtype
        apply map_mem_submodule_of_basis b f (Submodule.span ℚ S) _ ⟨y, hy⟩
        intro j
        apply Submodule.subset_span
        refine ⟨?_, ?_⟩
        · exact (le_sup_left : M.filtration.comparisonProductLayer π (n + 1) ≤ U)
            ⟨Submodule.zero_mem _, (b j).property⟩
        · intro k
          cases k with
          | inl k =>
              change RationalHeightLE (D.basis.repr 0 k) _
              simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hpos
          | inr k =>
              exact (M.squarefreeFinBasis_degree_height p (n + 1) j k).mono hpos
      · intro a ha hab hn x
        apply map_mem_submodule_of_basis (M.comparisonLayerBasis p a)
          (M.filtration.comparisonGraph π a ha) (Submodule.span ℚ S) _ x
        intro j
        exact Submodule.subset_span
          ⟨M.filtration.comparisonGraph_mem_layer π n a ha hn _,
            M.comparisonGraph_chosen_height hM a ha hab j⟩
  have hrange : Set.range (Subtype.val : S → L × A) = S := by
    ext z
    simp only [Subtype.range_coe_subtype, Set.mem_ofPred_eq]
  exact exists_bounded_submodule_basis_from_spanning e U
    (Subtype.val : S → L × A) (by rw [hrange]; exact hspan) (fun z => z.property.2)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_squarefree_model {p : ℝ} (hM : M.ComplexityLE p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B), l ∣ B ∧
      (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE
        (squarefreeModelBudget (∑ i, bound i) p) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨B, hB, hdiv, hraw, hstable⟩ := M.exists_squarefree_stable_grid hM l hl
  rw [replicatedIndex_card] at hraw
  refine ⟨B, hB, hstable, hdiv, ?_⟩
  have hq := squarefreeInputBudget_nonneg (∑ i, bound i) hp
  have hqq := squarefreeInputBudget_le_model (∑ i, bound i) hp
  have hdq : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ squarefreeInputBudget (∑ i, bound i) p := by
    calc
      _ ≤ (2 : ℝ) ^ (∑ i, bound i) * d := by exact_mod_cast M.squarefreeBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ (∑ i, bound i) * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  apply M.squarefreeModel_complexity hM B hB hstable (hq.trans hqq) (hdq.trans hqq)
  · exact squarefree_grid_budget _ _ d l B hp hM.1.1 (M.squarefreeBasisIndex_card_le p) hlp hraw
  · exact (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hqq))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

noncomputable def squarefreeRealPermute (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).RealGroup →*
      (M.squarefreeModel p B hB hstable).RealGroup :=
  realificationMap
    (hnil := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
    (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
    (M.filtration.replicatedLiePermute e).toLieHom

theorem squarefreeRealPermute_one (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeRealPermute p B hB hstable 1 g = g := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_eq_self _ M.filtration.replicatedLiePermute_one g.coord

theorem squarefreeRealPermute_mul (e f : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeRealPermute p B hB hstable (e * f) g =
      M.squarefreeRealPermute p B hB hstable e (M.squarefreeRealPermute p B hB hstable f g) := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_comp_apply _ _ _ (M.filtration.replicatedLiePermute_mul e f) g.coord

theorem squarefreeRealPermute_lattice (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).realLattice ≤
      (M.squarefreeModel p B hB hstable).realLattice.comap
        (M.squarefreeRealPermute p B hB hstable e) := by
  apply realificationMap_subgroup
  intro g hg
  exact (M.squarefreeLattice_permute p B hstable (replicatedPermutation bound e)
    (replicatedPermutation_block bound e) g).mpr hg

theorem squarefreeRealPermute_top (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (hg : g ∈ (M.squarefreeModel p B hB hstable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound))) :
    M.squarefreeRealPermute p B hB hstable e g = g := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_eq_self_on _ _
    (M.filtration.replicatedLiePermute_ordinary_top e) g.coord hg

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
