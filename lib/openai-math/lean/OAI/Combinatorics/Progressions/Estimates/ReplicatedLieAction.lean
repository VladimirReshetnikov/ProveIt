import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sigma
import OAI.Combinatorics.Progressions.Linear.CanonicalRankCompatibility
import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
import OAI.Combinatorics.Progressions.Polynomial.SquarefreeTopDegree
import OAI.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

abbrev ReplicatedIndex (bound : σ → ℕ) := Σ i, Fin (bound i)

theorem replicatedIndex_card [Fintype σ] (bound : σ → ℕ) :
    Fintype.card (ReplicatedIndex bound) = ∑ i, bound i := by
  simp only [ReplicatedIndex, Fintype.card_sigma, Fintype.card_fin]

def replicatedPermutation (bound : σ → ℕ) (e : ∀ i, Equiv.Perm (Fin (bound i))) :
    Equiv.Perm (ReplicatedIndex bound) := Equiv.sigmaCongrRight e

theorem replicatedPermutation_block (bound : σ → ℕ) (e : ∀ i, Equiv.Perm (Fin (bound i)))
    (j : ReplicatedIndex bound) : (replicatedPermutation bound e j).1 = j.1 := rfl

theorem replicated_blockDegree_apply [Fintype σ] (bound : σ → ℕ)
    (a : ReplicatedIndex bound →₀ ℕ) (i : σ) :
    blockDegree (fun j : ReplicatedIndex bound => j.1) a i = ∑ j : Fin (bound i), a ⟨i, j⟩ := by
  classical
  change (∑ j : ReplicatedIndex bound, if j.1 = i then a j else 0) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [hji, ite_false, Finset.sum_const_zero]
  · simp

theorem replicated_blockDegree_le [Fintype σ] (bound : σ → ℕ)
    (a : SquarefreeIndex (ReplicatedIndex bound)) :
    blockDegree (fun j : ReplicatedIndex bound => j.1) a.val ≤ bound := by
  intro i
  rw [replicated_blockDegree_apply]
  calc
    _ ≤ ∑ _j : Fin (bound i), 1 := Finset.sum_le_sum fun j _ => a.property ⟨i, j⟩
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} (bound : σ → ℕ)

abbrev ReplicatedPermutation := ∀ i, Equiv.Perm (Fin (bound i))

noncomputable instance replicatedPermutationFintype [Fintype σ] :
    Fintype (ReplicatedPermutation bound) := Fintype.ofFinite _

theorem replicatedPermutation_one :
    replicatedPermutation bound (1 : ReplicatedPermutation bound) = 1 := by
  apply Equiv.ext
  intro i
  cases i
  rfl

theorem replicatedPermutation_mul (e f : ReplicatedPermutation bound) :
    replicatedPermutation bound (e * f) = replicatedPermutation bound e * replicatedPermutation bound f := by
  apply Equiv.ext
  intro i
  cases i
  rfl

theorem replicatedPermutation_injective : Function.Injective (replicatedPermutation bound) := by
  intro e f h
  funext i
  apply Equiv.ext
  intro j
  have hh := congrArg (fun g : Equiv.Perm (ReplicatedIndex bound) => g ⟨i, j⟩) h
  change (⟨i, e i j⟩ : ReplicatedIndex bound) = ⟨i, f i j⟩ at hh
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

theorem replicatedPermutation_card_le [Fintype σ] :
    Fintype.card (ReplicatedPermutation bound) ≤ (∑ i, bound i).factorial := by
  classical
  have h := Fintype.card_le_of_injective _ (replicatedPermutation_injective bound)
  simpa only [Fintype.card_perm, replicatedIndex_card] using h

end Erdos3

end

section

namespace Erdos3

theorem replicated_blockDegree_full {σ : Type*} [Fintype σ] (bound : σ → ℕ) :
    blockDegree (fun j : ReplicatedIndex bound => j.1)
      (SquarefreeIndex.full (ReplicatedIndex bound)).val = bound := by
  ext i
  rw [replicated_blockDegree_apply]
  simp only [SquarefreeIndex.full_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedTopCoefficient :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) →ₗ[ℚ] F.layer bound where
  toFun x := ⟨squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound)), by
    have h := (x.property (SquarefreeIndex.full (ReplicatedIndex bound))).1
    simpa only [replicated_blockDegree_full] using h⟩
  map_add' x y := by
    apply Subtype.ext
    exact congrFun (map_add squarefreePolynomialEquiv x.val y.val) _
  map_smul' r x := by
    apply Subtype.ext
    exact congrFun (map_smul squarefreePolynomialEquiv r x.val) _

theorem replicatedTopCoefficient_apply
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    (F.replicatedTopCoefficient x).val =
      squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound)) := rfl

theorem replicatedTopCoefficient_permute (e : ∀ i, Equiv.Perm (Fin (bound i)))
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedTopCoefficient
        (F.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1)
          (replicatedPermutation bound e) (replicatedPermutation_block bound e) x) =
      F.replicatedTopCoefficient x := by
  apply Subtype.ext
  change squarefreePolynomialEquiv (squarefreePermute (replicatedPermutation bound e) x.val)
    (SquarefreeIndex.full (ReplicatedIndex bound)) = _
  rw [squarefreePermute_coefficient, SquarefreeIndex.permute_symm, SquarefreeIndex.permute_full]
  rfl

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure MultidegreeStructure (D : RationalFilteredNilmanifold L s d) (bound : σ → ℕ) where
  filtration : MultidegreeLieFiltration σ L s bound
  ordinary : filtration.ordinary = D.filtration
  basis : ∀ a : ∀ i, Fin (bound i + 1),
    Basis (Fin (finrank ℚ (filtration.layer (fun i => (a i).val)))) ℚ
      (filtration.layer (fun i => (a i).val))

namespace MultidegreeStructure

variable {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def ComplexityLE (p : ℝ) : Prop := D.GeometryComplexityLE p ∧
  ∀ a j k, rationalLogHeight (D.basis.repr (M.basis a j : L) k) ≤ p

theorem ComplexityLE.mono {p q : ℝ} (hM : M.ComplexityLE p) (hpq : p ≤ q) : M.ComplexityLE q :=
  ⟨hM.1.mono D hpq, fun a j k => (hM.2 a j k).trans hpq⟩

noncomputable def realSubgroup (a : σ → ℕ) : Subgroup D.RealGroup := M.filtration.realification.subgroup a

theorem realSubgroup_eq_realificationSubgroup (a : σ → ℕ) :
    M.realSubgroup a = NilpotentLieBCHGroup.realificationSubgroup
      (hnil := D.filtration.lowerCentralSeries_eq_bot) (M.filtration.layerIdeal a).toLieSubalgebra := by
  ext x
  rfl

noncomputable def orbitToOrdinary : M.filtration.realification.PolynomialOrbit →*
    D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) := by
  have h : M.filtration.realification.ordinary = D.filtration.realification := by
    change M.filtration.ordinary.realification = D.filtration.realification
    rw [M.ordinary]
  exact (M.filtration.realification.ordinary.orbitEquivOfEq h (fun _ : σ => 1)).toMonoidHom.comp
    M.filtration.realification.toOrdinaryOrbit

theorem orbitToOrdinary_eval (g : M.filtration.realification.PolynomialOrbit) (x : σ → ℤ) :
    D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x (M.orbitToOrdinary g) =
      M.filtration.realification.polynomialOrbitEval x g := by
  have h : M.filtration.realification.ordinary = D.filtration.realification := by
    change M.filtration.ordinary.realification = D.filtration.realification
    rw [M.ordinary]
  change D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) x
    (M.filtration.realification.ordinary.orbitEquivOfEq h (fun _ : σ => 1)
      (M.filtration.realification.toOrdinaryOrbit g)) = _
  rw [NilpotentLieFiltration.orbitEquivOfEq_eval,
    MultidegreeLieFiltration.toOrdinaryOrbit_eval]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realSubgroup_closed (a : σ → ℕ) : IsClosed (M.realSubgroup a : Set D.RealGroup) := by
  rw [M.realSubgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_closed D.basis (M.filtration.layerIdeal a).toLieSubalgebra

theorem realSubgroup_lattice_closed_discrete (a : σ → ℕ) :
    let Λ := D.realLattice.comap (M.realSubgroup a).subtype
    IsClosed (Λ : Set (M.realSubgroup a)) ∧ IsDiscrete (Λ : Set (M.realSubgroup a)) := by
  rw [M.realSubgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_lattice_closed_discrete D.basis
    (M.filtration.layerIdeal a).toLieSubalgebra D.lattice D.grid D.grid_pos D.outer_grid

omit [T2Space (ℝ ⊗[ℚ] L)] in
theorem realSubgroup_lattice_cocompact (a : σ → ℕ) :
    CompactSpace (M.realSubgroup a ⧸ D.realLattice.comap (M.realSubgroup a).subtype) := by
  rw [M.realSubgroup_eq_realificationSubgroup]
  exact NilpotentLieBCHGroup.realificationSubgroup_lattice_cocompact D.basis
    (M.filtration.layerIdeal a).toLieSubalgebra D.lattice D.grid D.grid_pos D.inner_grid D.outer_grid

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace MultidegreeLieFiltration

theorem ordinary_top_eq {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) :
    F.ordinary.layer (∑ i, bound i) = F.layer bound := by
  classical
  apply le_antisymm
  · rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    by_cases hle : a ≤ bound
    · have hsum : (∑ i, a i) = ∑ i, bound i :=
        le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) ha
      have heq : a = bound := funext (fun i =>
        (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum i (Finset.mem_univ i))
      rw [heq]
    · rw [F.terminal a hle]
      exact bot_le
  · exact F.layer_le_ordinary bound

end MultidegreeLieFiltration

namespace RationalFilteredNilmanifold.MultidegreeStructure

theorem realSubgroup_top {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    (M : D.MultidegreeStructure bound) :
    M.realSubgroup bound = D.filtration.realification.subgroup (∑ i, bound i) := by
  ext x
  change x.coord ∈ (M.filtration.layer bound).baseChange ℝ ↔
    x.coord ∈ (D.filtration.layer (∑ i, bound i)).baseChange ℝ
  rw [← M.ordinary, M.filtration.ordinary_top_eq]

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def restrictBound (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥) :
    MultidegreeLieFiltration σ L s bound' where
  ordinary := F.ordinary
  layer := F.layer
  antitone := F.antitone
  zero_eq_top := F.zero_eq_top
  lie_mem := F.lie_mem
  terminal := hzero
  degree_eq := F.degree_eq

noncomputable def restrictBoundRealOrbit (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥)
    (g : F.realification.PolynomialOrbit) :
    (F.restrictBound bound' hzero).realification.PolynomialOrbit := g

theorem restrictBoundRealOrbit_eval (bound' : σ → ℕ)
    (hzero : ∀ a, ¬a ≤ bound' → F.layer a = ⊥)
    (g : F.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.restrictBound bound' hzero).realification.polynomialOrbitEval x
        (F.restrictBoundRealOrbit bound' hzero g) =
      F.realification.polynomialOrbitEval x g := rfl

end MultidegreeLieFiltration

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def restrictBound (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥) :
    D.MultidegreeStructure bound' where
  filtration := M.filtration.restrictBound bound' hzero
  ordinary := M.ordinary
  basis a := M.basis (fun i => ⟨(a i).val, lt_of_lt_of_le (a i).isLt (Nat.add_le_add_right (hbound i) 1)⟩)

theorem restrictBound_complexity (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥)
    {p : ℝ} (hM : M.ComplexityLE p) :
    (M.restrictBound bound' hbound hzero).ComplexityLE p :=
  ⟨hM.1, fun a => hM.2 (fun i =>
    ⟨(a i).val, lt_of_lt_of_le (a i).isLt (Nat.add_le_add_right (hbound i) 1)⟩)⟩

theorem restrictBound_orbitToOrdinary (bound' : σ → ℕ) (hbound : bound' ≤ bound)
    (hzero : ∀ a, ¬a ≤ bound' → M.filtration.layer a = ⊥)
    (g : M.filtration.realification.PolynomialOrbit) :
    (M.restrictBound bound' hbound hzero).orbitToOrdinary
        (M.filtration.restrictBoundRealOrbit bound' hzero g) = M.orbitToOrdinary g := rfl

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_eq_finite (c : σ → ℕ) (n : ℕ) :
    F.weightedLayer c n =
      ⨆ a : {a : ∀ i, Fin (bound i + 1) // n ≤ multidegreeWeight c (fun i => (a i).val)},
        F.layerIdeal (fun i => (a.val i).val) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro a
    by_cases ha : a.val ≤ bound
    · let b : ∀ i, Fin (bound i + 1) := fun i => ⟨a.val i, Nat.lt_succ_of_le (ha i)⟩
      exact le_iSup_of_le ⟨b, a.property⟩ le_rfl
    · intro x hx
      have h : x = 0 := by
        have hx' : x ∈ F.layer a.val := hx
        simpa only [F.terminal a.val ha, Submodule.mem_bot] using hx'
      rw [h]
      exact LieSubmodule.zero_mem _
  · apply iSup_le
    intro a
    exact F.layer_le_weightedLayer c (fun i => (a.val i).val) n a.property

end Erdos3.MultidegreeLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem weightedLayer_span (c : σ → ℕ) (n : ℕ) :
    (M.filtration.weightedLayer c n).toSubmodule = Submodule.span ℚ
      (Set.range (fun a : Σ a : {a : ∀ i, Fin (bound i + 1) //
          n ≤ multidegreeWeight c (fun i => (a i).val)},
          Fin (finrank ℚ (M.filtration.layer (fun i => (a.val i).val))) =>
        (M.basis a.1.val a.2 : L))) := by
  rw [M.filtration.weightedLayer_eq_finite]
  simp only [LieSubmodule.iSup_toSubmodule]
  apply le_antisymm
  · apply iSup_le
    intro a
    change M.filtration.layer (fun i => (a.val i).val) ≤ _
    rw [← span_submodule_basis _ (M.basis a.val)]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨a, j⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨a, j⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem a (M.basis a.val j).property

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeTwoVariableSplit (s d : ℕ) (p epsilon : ℝ)
    (f : (Fin 2 → ℤ) → ℂ) where
  count : ℕ
  count_pos : 0 < count
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Bool → Type
  [lie : ∀ b, LieRing (L b)]
  [algebra : ∀ b, LieAlgebra ℚ (L b)]
  dim : Bool → ℕ
  [topology : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] L b)]
  [topologicalAdd : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] L b)]
  [continuousSMul : ∀ b, ContinuousSMul ℝ (ℝ ⊗[ℚ] L b)]
  [hausdorff : ∀ b, T2Space (ℝ ⊗[ℚ] L b)]
  model : ∀ b, RationalFilteredNilmanifold (L b) (∑ _ : Fin 2, s) (dim b)
  multi : ∀ b, (model b).MultidegreeStructure (totalDegreeSplitBound s b)
  complexity : ∀ b, (multi b).ComplexityLE p
  dimension_bound : ∀ b, dim b ≤ 2 ^ (2 * s) * d
  orbit : ∀ b, (multi b).filtration.realification.PolynomialOrbit
  test : ∀ b, Fin count → (model b).Niltest (fun _ : Fin 2 => 1)
  test_norm : ∀ b j, (test b j).normBound ≤ 1
  test_complexity : ∀ b j, (test b j).ComplexityLE p
  test_orbit : ∀ b j, (test b j).orbit = (multi b).orbitToOrdinary (orbit b)
  approximation : ∀ x,
    ‖f x - ∑ j, (test false j).eval x * (test true j).eval x‖ ≤ epsilon

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedLiePermute (e : ReplicatedPermutation bound) :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) ≃ₗ⁅ℚ⁆
      F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) :=
  F.squarefreeBlockPermute _ (replicatedPermutation bound e) (replicatedPermutation_block bound e)

theorem replicatedLiePermute_one (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedLiePermute 1 x = x := by
  unfold replicatedLiePermute
  simp only [replicatedPermutation_one]
  exact F.squarefreeBlockPermute_one _ x

theorem replicatedLiePermute_mul (e f : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedLiePermute (e * f) x = F.replicatedLiePermute e (F.replicatedLiePermute f x) := by
  apply Subtype.ext
  change squarefreePermute (replicatedPermutation bound (e * f)) x.val =
    squarefreePermute (replicatedPermutation bound e)
      (squarefreePermute (replicatedPermutation bound f) x.val)
  rw [replicatedPermutation_mul, squarefreePermute_mul]

theorem replicatedLiePermute_top (e : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
    (hx : x ∈ F.squarefreeMultidegreeLayer (fun j : ReplicatedIndex bound => j.1) (fun _ => 1)) :
    F.replicatedLiePermute e x = x :=
  F.squarefreeBlockPermute_eq_self_top _ _ _ x hx

theorem replicatedLiePermute_ordinary_top (e : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
    (hx : x ∈ (F.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).layer
      (Fintype.card (ReplicatedIndex bound))) : F.replicatedLiePermute e x = x := by
  have htop := (F.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).ordinary_top_eq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at htop
  change (F.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).layer
    (Fintype.card (ReplicatedIndex bound)) =
      F.squarefreeMultidegreeLayer (fun j : ReplicatedIndex bound => j.1) (fun _ => 1) at htop
  apply F.replicatedLiePermute_top e x
  rw [← htop]
  exact hx

end Erdos3.MultidegreeLieFiltration

end

end OAI
