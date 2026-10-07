/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.RealMultidegreeQuotientOrbit
import OAI.Combinatorics.Progressions.Estimates.VectorApproximationPrecomposition
import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
import OAI.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialMonomial (a : σ →₀ ℕ) (ha : a ≠ 0) :
    F.layer (fun i => a i) →ₗ[ℚ] F.positivePolynomialAlgebra where
  toFun x := ⟨monomial a x.val, F.monomial_mem_adaptedSubmodule a x.property, by
    classical
    simp [ha]⟩
  map_add' x y := by
    apply Subtype.ext
    change monomial a (x.val + y.val) = monomial a x.val + monomial a y.val
    simp [monomial, TensorProduct.tmul_add]
  map_smul' c x := by
    apply Subtype.ext
    change monomial a (c • x.val) = c • monomial a x.val
    simp [monomial]

theorem positivePolynomialMonomial_coe (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : F.layer (fun i => a i)) : (F.positivePolynomialMonomial a ha x).val = monomial a x.val := rfl

theorem positivePolynomialMonomial_mem_layer (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : F.layer (fun i => a i)) :
    F.positivePolynomialMonomial a ha x ∈ F.positivePolynomialMultidegreeLayer (fun i => a i) := by
  change monomial a x.val ∈ coefficientSupport {b : σ →₀ ℕ | (fun i => a i) ≤ fun i => b i}
  apply monomial_mem_coefficientSupport
  exact fun i => le_rfl

theorem positivePolynomialMonomial_evaluation (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : F.layer (fun i => a i)) : F.positivePolynomialEvaluation (F.positivePolynomialMonomial a ha x) = x.val := by
  change eval (fun _ : σ => (1 : ℚ)) (monomial a x.val) = _
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialMap_monomial (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : ℝ ⊗[ℚ] F.layer (fun i => a i)) :
    F.realPositivePolynomialMap ((F.positivePolynomialMonomial a ha).baseChange ℝ x) =
      monomial a ((F.layer (fun i => a i)).subtype.baseChange ℝ x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul r y =>
    apply coefficients.injective
    ext b
    rw [LinearMap.baseChange_tmul, F.realPositivePolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (monomial a y.val) b =
      coefficients (monomial a (r ⊗ₜ[ℚ] y.val)) b
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    simp [monomial, TensorProduct.tmul_add]

theorem realPositivePolynomialMonomial_mem_layer (a : σ →₀ ℕ) (ha : a ≠ 0)
    (x : ℝ ⊗[ℚ] F.layer (fun i => a i)) :
    (F.positivePolynomialMonomial a ha).baseChange ℝ x ∈
      (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ := by
  induction x using TensorProduct.inductionOn with
  | tmul r y =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.positivePolynomialMonomial_mem_layer a ha y)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem exists_realPositivePolynomial_component
    (p : F.realification.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    ∃ x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra,
      F.realPositivePolynomialTensor x = F.realification.positivePolynomialComponent a p ∧
      x ∈ (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ := by
  classical
  by_cases ha : a = 0
  · subst a
    refine ⟨0, ?_, Submodule.zero_mem _⟩
    rw [map_zero]
    exact ((F.realification.positivePolynomialComponent_eq_zero 0 p).mpr p.property.2).symm
  · let Q := F.layer (fun i => a i)
    let c : Q.baseChange ℝ := ⟨coefficients p.val a, p.property.1 a⟩
    let y : ℝ ⊗[ℚ] Q := (realificationSubmoduleEquiv Q).symm c
    have hy : Q.subtype.baseChange ℝ y = c.val :=
      congrArg Subtype.val ((realificationSubmoduleEquiv Q).apply_symm_apply c)
    refine ⟨(F.positivePolynomialMonomial a ha).baseChange ℝ y, ?_,
      F.realPositivePolynomialMonomial_mem_layer a ha y⟩
    apply Subtype.ext
    change F.realPositivePolynomialMap ((F.positivePolynomialMonomial a ha).baseChange ℝ y) =
      monomial a (coefficients p.val a)
    rw [F.realPositivePolynomialMap_monomial, hy]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialTensor_mem_layer (a : σ → ℕ)
    {x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra}
    (hx : x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ) :
    F.realPositivePolynomialTensor x ∈ F.realification.positivePolynomialMultidegreeLayer a := by
  let U := F.positivePolynomialMultidegreeLayer a
  have hbase (z : ℝ ⊗[ℚ] U) :
      F.realPositivePolynomialTensor (U.subtype.baseChange ℝ z) ∈
        F.realification.positivePolynomialMultidegreeLayer a := by
    induction z using TensorProduct.inductionOn with
    | tmul r p =>
      intro b hb
      change coefficients (F.realPositivePolynomialMap
        (U.subtype.baseChange ℝ (r ⊗ₜ[ℚ] p))) b = 0
      rw [LinearMap.baseChange_tmul, F.realPositivePolynomialMap_coefficient_tmul]
      have hz : coefficients p.val.val b = 0 := p.property b hb
      change r ⊗ₜ[ℚ] coefficients p.val.val b = 0
      rw [hz, TensorProduct.tmul_zero]
    | add z w hz hw =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hz hw
  let z := (realificationSubmoduleEquiv U).symm ⟨x, hx⟩
  have hz : U.subtype.baseChange ℝ z = x :=
    congrArg Subtype.val ((realificationSubmoduleEquiv U).apply_symm_apply ⟨x, hx⟩)
  exact hz ▸ hbase z

theorem exists_realPositivePolynomial_preimage_layer (a : σ → ℕ)
    (p : F.realification.positivePolynomialAlgebra)
    (hp : p ∈ F.realification.positivePolynomialMultidegreeLayer a) :
    ∃ x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra,
      x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ ∧
      F.realPositivePolynomialTensor x = p := by
  classical
  choose y hy hylayer using F.exists_realPositivePolynomial_component p
  refine ⟨∑ b ∈ (coefficients p.val).support, y b, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro b hb
    have hab : a ≤ fun i => b i := by
      by_contra h
      have hz : coefficients p.val b = 0 := hp b h
      exact (Finsupp.mem_support_iff.mp hb) hz
    exact Submodule.baseChange_mono ℝ (F.positivePolynomialMultidegreeLayer_antitone hab) (hylayer b)
  · rw [map_sum]
    simp_rw [hy]
    exact F.realification.sum_positivePolynomialComponent p

theorem realPositivePolynomialTensor_surjective : Function.Surjective F.realPositivePolynomialTensor := by
  intro p
  obtain ⟨x, _, hx⟩ := F.exists_realPositivePolynomial_preimage_layer 0 p (by
    rw [F.realification.positivePolynomialMultidegreeLayer_zero]
    trivial)
  exact ⟨x, hx⟩

noncomputable def realPositivePolynomialEquiv :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) ≃ₗ⁅ℚ⁆ F.realification.positivePolynomialAlgebra :=
  LieEquiv.ofBijective F.realPositivePolynomialTensor
    ⟨F.realPositivePolynomialTensor_injective, F.realPositivePolynomialTensor_surjective⟩

theorem realPositivePolynomialEquiv_apply (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realPositivePolynomialEquiv x = F.realPositivePolynomialTensor x := rfl

theorem realPositivePolynomialEquiv_mem_layer (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realPositivePolynomialEquiv x ∈ F.realification.positivePolynomialMultidegreeLayer a ↔
      x ∈ (F.positivePolynomialMultidegreeLayer a).baseChange ℝ := by
  constructor
  · intro hx
    obtain ⟨y, hy, heq⟩ := F.exists_realPositivePolynomial_preimage_layer a _ hx
    have hxy : y = x := F.realPositivePolynomialTensor_injective heq
    exact hxy ▸ hy
  · exact F.realPositivePolynomialTensor_mem_layer a

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realPositivePolynomialOrbitTransport
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit) :
    F.positivePolynomialMultidegree.realification.PolynomialOrbit :=
  F.positivePolynomialMultidegree.realification.polynomialOrbitOfLog
    (VectorPolynomial.map F.realPositivePolynomialEquiv.symm.toLinearMap
      (PolynomialOrbit.log F.realification.positivePolynomialMultidegree g)) (by
        intro a
        rw [coefficients_map]
        change F.realPositivePolynomialEquiv.symm _ ∈
          (F.positivePolynomialMultidegreeLayer (fun i => a i)).baseChange ℝ
        apply (F.realPositivePolynomialEquiv_mem_layer (fun i => a i) _).mp
        rw [F.realPositivePolynomialEquiv.apply_symm_apply]
        exact PolynomialOrbit.adapted F.realification.positivePolynomialMultidegree g a)

theorem realPositivePolynomialOrbitTransport_eval
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit) (x : σ → ℤ) :
    NilpotentLieBCHGroup.mapOfSteps F.realPositivePolynomialEquiv.toLieHom
        (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x
          (F.realPositivePolynomialOrbitTransport g)) =
      F.realification.positivePolynomialMultidegree.polynomialOrbitEval x g := by
  apply NilpotentLieBCHGroup.ext
  change F.realPositivePolynomialEquiv
      (eval (fun i => (x i : ℚ)) (VectorPolynomial.map F.realPositivePolynomialEquiv.symm.toLinearMap
        (PolynomialOrbit.log F.realification.positivePolynomialMultidegree g))) = _
  rw [eval_map]
  exact F.realPositivePolynomialEquiv.apply_symm_apply _

theorem realPositivePolynomialOrbitTransport_zero
    (g : F.realification.positivePolynomialMultidegree.PolynomialOrbit)
    (hg : F.realification.positivePolynomialMultidegree.polynomialOrbitEval 0 g = 1) :
    F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0
      (F.realPositivePolynomialOrbitTransport g) = 1 := by
  apply NilpotentLieBCHGroup.mapOfSteps_injective F.realPositivePolynomialEquiv.toLieHom
    F.realPositivePolynomialEquiv.injective
  rw [map_one, F.realPositivePolynomialOrbitTransport_eval, hg]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_realPositivePolynomial_orbit (g : F.realification.PolynomialOrbit)
    (hg : F.realification.polynomialOrbitEval 0 g = 1) :
    ∃ h : F.positivePolynomialMultidegree.realification.PolynomialOrbit,
      F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
      ∀ x, NilpotentLieBCHGroup.realificationMap
          (hnil := F.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
          (hM := F.ordinary.lowerCentralSeries_eq_bot) F.positivePolynomialEvaluation
          (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        F.realification.polynomialOrbitEval x g := by
  obtain ⟨q, hqzero, hq⟩ := F.realification.exists_positivePolynomial_orbit g hg
  refine ⟨F.realPositivePolynomialOrbitTransport q,
    F.realPositivePolynomialOrbitTransport_zero q hqzero, ?_⟩
  intro x
  apply NilpotentLieBCHGroup.ext
  have htransport := congrArg NilpotentLieBCHGroup.coord
    (F.realPositivePolynomialOrbitTransport_eval q x)
  have hprojection := congrArg NilpotentLieBCHGroup.coord (hq x)
  calc
    _ = F.realification.positivePolynomialEvaluation (F.realPositivePolynomialEquiv
        (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x
          (F.realPositivePolynomialOrbitTransport q)).coord) :=
      (F.realPositivePolynomialEvaluation_commute _).symm
    _ = F.realification.positivePolynomialEvaluation
        (F.realification.positivePolynomialMultidegree.polynomialOrbitEval x q).coord :=
      congrArg F.realification.positivePolynomialEvaluation htransport
    _ = _ := hprojection

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

theorem positivePolynomialDownset_projection_height (p : ℝ) (i j) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (lieQuotientMap (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
        (M.positivePolynomialFinBasis p j)) i) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply,
    positivePolynomialFinBasis, Basis.reindex_apply]
  change RationalHeightLE ((M.filtration.positivePolynomialDownsetBasis
    (M.positiveCoefficientBasis p) J hJ).repr
      (lieQuotientMap _ (M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p) _)) _) 1
  rw [M.filtration.positivePolynomialDownsetBasis_repr]
  exact basis_repr_height_one _ _ _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial NilpotentLieBCHGroup

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

noncomputable def positivePolynomialQuotientProductModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :=
  RationalFilteredNilmanifold.pi (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable)

omit [DecidableEq α] in
theorem positivePolynomialQuotientProductModel_geometry (p q : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hα : (Fintype.card α : ℝ) ≤ q)
    (hE : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q) :
    (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).GeometryComplexityLE ((q + 2) ^ 2) :=
  pi_geometry _ ((Nat.cast_nonneg _).trans hE.1) hα
    (fun a => (M.positivePolynomialDownsetModel_complexity (J a) (hJ a) p q B hB hstable hE).1)

omit [DecidableEq α] in
theorem positivePolynomialQuotientProductModel_map_height (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) (i j) :
    RationalHeightLE ((M.positivePolynomialQuotientProductModel J hJ p B hB hstable).basis.repr
      (M.filtration.positivePolynomialQuotientProductMap J hJ (M.positivePolynomialFinBasis p j)) i) 1 := by
  change RationalHeightLE ((pi (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable)).basis.repr _ i) 1
  rw [productFinBasis_repr]
  exact M.positivePolynomialDownset_projection_height _ _ p _ j

theorem positivePolynomialQuotientProductModel_lattice_cover (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) :
    (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).realLattice ⊓
      (M.filtration.positivePolynomialQuotientProductRealMap J hJ).range ≤
        (M.positivePolynomialModel p B hB hstable).realLattice.map
          (M.filtration.positivePolynomialQuotientProductRealMap J hJ) := by
  exact M.filtration.positivePolynomialQuotientProduct_lattice_cover J hJ
    (M.positiveCoefficientBasis p) hcover (M.positivePolynomialLattice p B hstable) B
    (M.positivePolynomialLattice_coordinates p B hstable)

omit [DecidableEq σ] [∀ a, DecidablePred (· ∈ J a)] in
theorem positivePolynomialQuotientProductModel_map_injective (p : ℝ)
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) :
    Function.Injective (M.filtration.positivePolynomialQuotientProductRealMap J hJ) :=
  M.filtration.positivePolynomialQuotientProductRealMap_injective J hJ (M.positiveCoefficientBasis p) hcover

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetOrbit
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.PolynomialOrbit :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) g

theorem positivePolynomialDownsetOrbit_eval
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval x
      (F.positivePolynomialDownsetOrbit J hJ g) =
        F.positivePolynomialMultidegree.realQuotientMultidegreeMap
          (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)
          (F.positivePolynomialMultidegree.realification.polynomialOrbitEval x g) :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit_eval _ g x

theorem positivePolynomialDownsetOrbit_zero
    (g : F.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (hg : F.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 g = 1) :
    (F.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval 0
      (F.positivePolynomialDownsetOrbit J hJ g) = 1 :=
  F.positivePolynomialMultidegree.realQuotientMultidegreeOrbit_zero _ g hg

end Erdos3.MultidegreeLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open VectorPolynomial

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))

theorem positivePolynomialProductProjection_mk (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.positivePolynomialMultidegree.realification.Group) (a : α) :
    productProjection (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable) a
      (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ g)) =
        QuotientGroup.mk (M.filtration.positivePolynomialMultidegree.realQuotientMultidegreeMap
          (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)) g) := by
  change QuotientGroup.mk (realBCHPiEquiv
    (fun a => (M.filtration.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
      (M.filtration.positivePolynomialQuotientProductRealMap J hJ g) a) = _
  rw [M.filtration.positivePolynomialQuotientProductRealMap_component]
  rfl

theorem positivePolynomialProductProjection_orbit (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (x : σ → ℤ) (a : α) :
    productProjection (fun a => M.positivePolynomialDownsetModel (J a) (hJ a) p B hB hstable) a
      (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ
        (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x g))) =
      QuotientGroup.mk ((M.filtration.positivePolynomialDownsetQuotient (J a) (hJ a)).realification.polynomialOrbitEval x
        (M.filtration.positivePolynomialDownsetOrbit (J a) (hJ a) g)) := by
  rw [M.positivePolynomialProductProjection_mk,
    M.filtration.positivePolynomialDownsetOrbit_eval]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_positivePolynomial_product_reconstruction (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α σ L : Type*} [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ a, DecidablePred (· ∈ J a)] (hJ : ∀ a, IsLowerSet (J a))
      [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      [T2Space (ℝ ⊗[ℚ] (∀ a, M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J a) (hJ a)))]
      (p q : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (∑ i, bound i) = t → (Fintype.card α : ℝ) ≤ q →
      (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q →
      (∀ c, c ≠ 0 → (∀ a, c ∉ J a) → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ (u : (M.positivePolynomialModel p B hB hstable).Space → ℂ) (ℓ : ℝ≥0),
        (ℓ : ℝ) ≤ Real.exp q →
        (letI := (M.positivePolynomialModel p B hB hstable).metricSpace; LipschitzWith ℓ u) →
        (∀ x, ‖u x‖ ≤ 1) →
        ∃ (v : (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).Space → ℂ) (K : ℝ≥0),
          (K : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
          (letI := (M.positivePolynomialQuotientProductModel J hJ p B hB hstable).metricSpace;
            LipschitzWith K v) ∧ (∀ y, ‖v y‖ ≤ 2) ∧
          ∀ x, v (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ x)) =
            u (QuotientGroup.mk x) := by
  obtain ⟨a, _, hrec⟩ := exists_native_complex_reconstruction t
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + 2) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro α σ L _ _ _ _ _ _ s d D bound M J _ hJ _ _ _ _ _ _ _ _ p q B hB hstable ht hα hX hcover u ℓ hℓ hu hub
  subst t
  let X := M.positivePolynomialModel p B hB hstable
  let Y := M.positivePolynomialQuotientProductModel J hJ p B hB hstable
  let r := q + (q + 2) ^ 2
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hX.1
  have hqr : q ≤ r := le_add_of_nonneg_right (sq_nonneg _)
  have hrr : (q + 2) ^ 2 ≤ r := le_add_of_nonneg_left hq
  have hr : 0 ≤ r := hq.trans hqr
  have hY := M.positivePolynomialQuotientProductModel_geometry J hJ p q B hB hstable hα hX
  have hmap : ∀ i j, rationalLogHeight
      (Y.basis.repr (M.filtration.positivePolynomialQuotientProductMap J hJ (X.basis j)) i) ≤ r := by
    intro i j
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialQuotientProductModel_map_height J hJ p B hB hstable i j)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hr)
  have hker : ∀ k ∈ (M.filtration.positivePolynomialQuotientProductRealMap J hJ).ker, ∀ x,
      u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x) := by
    intro k hk x
    have hk1 : k = 1 := M.positivePolynomialQuotientProductModel_map_injective J hJ p hcover
      ((MonoidHom.mem_ker.mp hk).trans (map_one _).symm)
    rw [hk1, one_mul]
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec X Y
    (M.filtration.positivePolynomialQuotientProductMap J hJ) hr
    (hX.mono X hqr) (hY.mono Y hrr) hmap
    (M.positivePolynomialQuotientProductModel_lattice_cover J hJ p B hB hstable hcover)
    u ℓ (hℓ.trans (Real.exp_le_exp.mpr hqr)) hu hub hker
  have hcost : (r + a) ^ a ≤ (q + C) ^ C := by
    simpa [P, r, Polynomial.eval₂_pow] using hbudget q hq
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv, hb, heval⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))

theorem positivePolynomial_factor_error_of_lift (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.realification.PolynomialOrbit)
    (h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (hproj : ∀ x, realificationMap
      (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        M.filtration.realification.polynomialOrbitEval x g)
    (n : α → ℕ)
    (ψ : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Space → ℝ)
    (c : (∀ i, Fin (n i)) → ℂ) (u : D.Space → ℂ) (epsilon : ℝ)
    (happrox : ∀ y, ‖u (QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation y)) -
      ∑ j, (∏ i, (ψ i (j i) (productProjection
        (fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable) i
        (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ y))) : ℂ)) * c j‖ ≤ epsilon) :
    ∀ x, ‖u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) -
      ∑ j, (∏ i, (ψ i (j i) (QuotientGroup.mk
        ((M.filtration.positivePolynomialDownsetQuotient (J i) (hJ i)).realification.polynomialOrbitEval x
          (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h))) : ℂ)) * c j‖ ≤ epsilon := by
  intro x
  have hx := happrox (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h)
  rw [hproj x] at hx
  simpa only [M.positivePolynomialProductProjection_orbit] using hx

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

variable {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
  {bound : σ → ℕ} (M : D.MultidegreeStructure bound)
  (J : α → Set (σ →₀ ℕ)) [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))

theorem positivePolynomial_vector_error_of_lift (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (g : M.filtration.realification.PolynomialOrbit)
    (h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
    (hproj : ∀ x, realificationMap
      (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h) =
        M.filtration.realification.polynomialOrbitEval x g)
    (n : α → ℕ)
    (ψ : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable).Space → ℝ)
    (c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I) (u : I → D.Space → ℂ) (epsilon : ℝ)
    (happrox : ∀ y, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation y))) : EuclideanSpace ℂ I) -
      ∑ j, (∏ i, (ψ i (j i) (productProjection
        (fun i => M.positivePolynomialDownsetModel (J i) (hJ i) p B hB hstable) i
        (QuotientGroup.mk (M.filtration.positivePolynomialQuotientProductRealMap J hJ y))) : ℂ)) • c j‖ ≤ epsilon) :
    ∀ x, ‖(WithLp.toLp 2 (fun k => u k (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
      ∑ j, (∏ i, (ψ i (j i) (QuotientGroup.mk
        ((M.filtration.positivePolynomialDownsetQuotient (J i) (hJ i)).realification.polynomialOrbitEval x
          (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h))) : ℂ)) • c j‖ ≤ epsilon := by
  intro x
  have hx := happrox (M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval x h)
  rw [hproj x] at hx
  simpa only [M.positivePolynomialProductProjection_orbit] using hx

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
