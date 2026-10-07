/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source.
Import the finite-weight compatibility lemma for Lean 4.32. -/
import OAI.Compat.FinsuppWeight
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.ComparisonLayerBracket
import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
import OAI.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realSquarefreeLayerMap (a : SquarefreeIndex ι) :
    (F.layer (blockDegree π a.val)).baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :=
  ((F.squarefreeLayerMap π a).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).symm.toLinearMap

theorem realSquarefreeLayerMap_tmul (a : SquarefreeIndex ι) (r : ℝ)
    (v : F.layer (blockDegree π a.val)) :
    F.realSquarefreeLayerMap π a
      (realificationSubmoduleEquiv (F.layer (blockDegree π a.val)) (r ⊗ₜ[ℚ] v)) =
      r ⊗ₜ[ℚ] F.squarefreeLayerMap π a v := by
  simp only [realSquarefreeLayerMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem realSquarefreeLayerMap_zero (a : SquarefreeIndex ι) (ha : a.val = 0)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeLayerMap π a v = 0 := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul, F.squarefreeLayerMap_zero π a ha,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem realSquarefreeLayerMap_mem (a : SquarefreeIndex ι)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeLayerMap π a v ∈
      (F.squarefreeMultidegreeLayer π (fun i => a.val i)).baseChange ℝ := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.squarefreeLayerMap_mem π a x)
  | add x y hx hy =>
    simpa only [map_add] using
      ((F.squarefreeMultidegreeLayer π (fun i => a.val i)).baseChange ℝ).add_mem hx hy

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realBlockCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) : (F.layer (blockDegree π a.val)).baseChange ℝ :=
  ⟨coefficients p.val (blockExponent π a.val), p.property (blockExponent π a.val)⟩

noncomputable def realPolarizedCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) : ℝ ⊗[ℚ] F.SquarefreeAlgebra π :=
  (multidegreeFactorial (blockDegree π a.val) : ℚ) •
    F.realSquarefreeLayerMap π a (F.realBlockCoefficient π p a)

theorem realPolarizedCoefficient_zero (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val = 0) : F.realPolarizedCoefficient π p a = 0 := by
  rw [realPolarizedCoefficient, F.realSquarefreeLayerMap_zero π a ha, smul_zero]

theorem realPolarizedCoefficient_mem (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) :
    F.realPolarizedCoefficient π p a ∈
      (F.squarefreeMultidegreeFiltration π).realification.layer (fun i => a.val i) :=
  ((F.squarefreeMultidegreeFiltration π).realification.layer _).smul_mem _
    (F.realSquarefreeLayerMap_mem π a (F.realBlockCoefficient π p a))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realSquarefreeInclusion :
    (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) →ₗ[ℝ] (ℝ ⊗[ℚ] SquarefreePolynomial ι L) :=
  (F.squarefreeAdaptedSubalgebra π).toSubmodule.subtype.baseChange ℝ

theorem realSquarefreeInclusion_injective : Function.Injective (F.realSquarefreeInclusion π) :=
  realification_subtype_injective (F.squarefreeAdaptedSubalgebra π).toSubmodule

theorem realSquarefreeInclusion_layerMap (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeInclusion π (F.realSquarefreeLayerMap π a v) =
      (squarefreeMonomial a).baseChange ℝ v.val := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul]
    change r ⊗ₜ[ℚ] (F.squarefreeLayerMap π a x).val = r ⊗ₜ[ℚ] squarefreeMonomial a x.val
    rw [F.squarefreeLayerMap_coe π a ha]
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy

theorem realSquarefreeInclusion_permute (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i)
    (x : ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :
    F.realSquarefreeInclusion π ((F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ x) =
      (squarefreePermute (L := L) e).toLinearMap.baseChange ℝ (F.realSquarefreeInclusion π x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem realSquarefreePermute_monomial (e : Equiv.Perm ι) (a : SquarefreeIndex ι)
    (x : ℝ ⊗[ℚ] L) :
    (squarefreePermute (L := L) e).toLinearMap.baseChange ℝ
        ((squarefreeMonomial a).baseChange ℝ x) =
      (squarefreeMonomial (SquarefreeIndex.permute e a)).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, squarefreePermute_monomial]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace MultidegreeLieFiltration

variable {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedCoefficient_inclusion (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val ≠ 0) :
    F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a) =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        (squarefreeMonomial a).baseChange ℝ (coefficients p.val (blockExponent π a.val)) := by
  rw [realPolarizedCoefficient, LinearMap.map_smul_of_tower,
    F.realSquarefreeInclusion_layerMap π a ha]
  rfl

theorem realPolarizedCoefficient_permute (p : F.realification.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    (F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ (F.realPolarizedCoefficient π p a) =
      F.realPolarizedCoefficient π p (SquarefreeIndex.permute e a) := by
  by_cases ha : a.val = 0
  · rw [F.realPolarizedCoefficient_zero π p a ha,
      F.realPolarizedCoefficient_zero π p _ ((SquarefreeIndex.permute_zero_iff e a).mpr ha),
      map_zero]
  · have hea : (SquarefreeIndex.permute e a).val ≠ 0 :=
      fun h => ha ((SquarefreeIndex.permute_zero_iff e a).mp h)
    apply F.realSquarefreeInclusion_injective π
    rw [F.realSquarefreeInclusion_permute, F.realPolarizedCoefficient_inclusion π p a ha,
      F.realPolarizedCoefficient_inclusion π p _ hea, LinearMap.map_smul_of_tower,
      realSquarefreePermute_monomial, SquarefreeIndex.permute_blockDegree π e he a,
      blockExponent_permute π e he a]

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonSubalgebra : LieSubalgebra ℚ (L × F.SquarefreeAlgebra π) :=
  { F.comparisonLayer π 1 with
    lie_mem' := fun hx hy => F.comparisonLayer_antitone π (by decide : 1 ≤ 1 + 1)
      (F.comparisonLayer_lie_mem π hx hy) }

noncomputable def comparisonFiltration :
    NilpotentLieFiltration (F.comparisonSubalgebra π) (max s (Fintype.card ι)) where
  layer n := (F.comparisonLayer π n).comap (F.comparisonSubalgebra π).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.comparisonLayer_antitone π h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.comparisonLayer_lie_mem π hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × F.SquarefreeAlgebra π)
    have h : x.val ∈ F.comparisonLayer π (max s (Fintype.card ι) + 1) := hx
    simpa only [F.comparisonLayer_terminal, Submodule.mem_bot] using h

theorem mem_comparisonFiltration_layer (n : ℕ) (x : F.comparisonSubalgebra π) :
    x ∈ (F.comparisonFiltration π).layer n ↔ x.val ∈ F.comparisonLayer π n := Iff.rfl

noncomputable def comparisonFirst : F.comparisonSubalgebra π →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L (F.SquarefreeAlgebra π)).comp (F.comparisonSubalgebra π).incl

noncomputable def comparisonSecond : F.comparisonSubalgebra π →ₗ⁅ℚ⁆ F.SquarefreeAlgebra π :=
  (LieHom.snd ℚ L (F.SquarefreeAlgebra π)).comp (F.comparisonSubalgebra π).incl

theorem comparisonFirst_mem_layer (n : ℕ) {x : F.comparisonSubalgebra π}
    (hx : x ∈ (F.comparisonFiltration π).layer n) : F.comparisonFirst π x ∈ F.ordinary.layer n :=
  (F.comparisonLayer_le_product π n hx).1

theorem comparisonSecond_mem_layer (n : ℕ) {x : F.comparisonSubalgebra π}
    (hx : x ∈ (F.comparisonFiltration π).layer n) :
    F.comparisonSecond π x ∈ F.squarefreeDegreeLayer π n :=
  (F.comparisonLayer_le_product π n hx).2

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraphLift (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] F.comparisonSubalgebra π where
  toFun x := ⟨F.comparisonGraph π a ha x, F.comparisonGraph_mem_layer π 1 a ha (by
    by_contra h
    have hs : (∑ i, a i) = 0 := by omega
    apply ha
    funext i
    change a i = 0
    exact (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)) x⟩
  map_add' x y := Subtype.ext (map_add (F.comparisonGraph π a ha) x y)
  map_smul' r x := Subtype.ext (map_smul (F.comparisonGraph π a ha) r x)

theorem comparisonGraphLift_first (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonFirst π (F.comparisonGraphLift π a ha x) = x.val := rfl

theorem comparisonGraphLift_second (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonSecond π (F.comparisonGraphLift π a ha x) = F.blockLayerMap π a ha x := rfl

theorem comparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).layer (∑ i, a i) :=
  F.comparisonGraph_mem_layer π _ a ha le_rfl x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonFiltrationLayerEquiv (n : ℕ) (hn : 1 ≤ n) :
    (F.comparisonFiltration π).layer n ≃ₗ[ℚ] F.comparisonLayer π n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.comparisonLayer_antitone π hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonGraphLift (a : σ → ℕ) (ha : a ≠ 0) :
    (F.layer a).baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] F.comparisonSubalgebra π) :=
  ((F.comparisonGraphLift π a ha).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer a)).symm.toLinearMap

theorem realComparisonGraphLift_tmul (a : σ → ℕ) (ha : a ≠ 0) (r : ℝ) (x : F.layer a) :
    F.realComparisonGraphLift π a ha (realificationSubmoduleEquiv (F.layer a) (r ⊗ₜ[ℚ] x)) =
      r ⊗ₜ[ℚ] F.comparisonGraphLift π a ha x := by
  simp only [realComparisonGraphLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem realComparisonGraphLift_first (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonGraphLift π a ha x) = x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul, realificationLieHom_tmul, F.comparisonGraphLift_first]
    rfl
  | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

theorem realComparisonGraphLift_second (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonGraphLift π a ha x)) =
      (factorialBlockMonomial π a).baseChange ℝ x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul, realificationLieHom_tmul, F.comparisonGraphLift_second]
    change r ⊗ₜ[ℚ] (F.blockLayerMap π a ha y).val = r ⊗ₜ[ℚ] factorialBlockMonomial π a y.val
    rw [F.blockLayerMap_coe]
  | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

theorem realComparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    F.realComparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).realification.layer (∑ i, a i) := by
  change F.realComparisonGraphLift π a ha x ∈ ((F.comparisonFiltration π).layer (∑ i, a i)).baseChange ℝ
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.comparisonGraphLift_mem_degree π a ha y)
  | add y z hy hz =>
    simpa only [map_add] using (((F.comparisonFiltration π).layer (∑ i, a i)).baseChange ℝ).add_mem hy hz

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : σ →₀ ℕ) : ℝ ⊗[ℚ] F.comparisonSubalgebra π := by
  classical
  exact if ha : a = 0 then 0 else
    F.realComparisonGraphLift π (fun i => a i)
      (fun h => ha (Finsupp.ext fun i => congrFun h i))
      ⟨coefficients p.val a, p.property a⟩

theorem realComparisonCoefficient_zero_index (p : F.realification.adaptedLieSubalgebra) :
    F.realComparisonCoefficient π p 0 = 0 := by
  simp [realComparisonCoefficient]

theorem realComparisonCoefficient_zero_value (p : F.realification.adaptedLieSubalgebra)
    (a : σ →₀ ℕ) (h : coefficients p.val a = 0) : F.realComparisonCoefficient π p a = 0 := by
  by_cases ha : a = 0
  · subst a
    exact F.realComparisonCoefficient_zero_index π p
  · rw [realComparisonCoefficient, dite_eq_right ha]
    have hz : (⟨coefficients p.val a, p.property a⟩ :
        (F.layer (fun i => a i)).baseChange ℝ) = 0 := Subtype.ext h
    rw [hz, map_zero]

theorem realComparisonCoefficient_mem (p : F.realification.adaptedLieSubalgebra) (a : σ →₀ ℕ) :
    F.realComparisonCoefficient π p a ∈
      (F.comparisonFiltration π).realification.layer (Finsupp.weight (fun _ => 1) a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index]
    exact Submodule.zero_mem _
  · rw [realComparisonCoefficient, dite_eq_right ha]
    have h := F.realComparisonGraphLift_mem_degree π (fun i => a i)
      (fun h => ha (Finsupp.ext fun i => congrFun h i))
      ⟨coefficients p.val a, p.property a⟩
    simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using h

end Erdos3.MultidegreeLieFiltration

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} [Fintype ι] {L₀ H : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing H] [LieAlgebra ℚ H]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionProductMap_point_logHeight
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : H) {p : ℝ}
    (h₀ : ∀ i, rationalLogHeight (D₀.basis.repr (φ₀ x) i) ≤ p)
    (hφ : ∀ a i, rationalLogHeight ((D a).basis.repr (φ a x) i) ≤ p) :
    ∀ i, rationalLogHeight
      ((optionProduct D₀ D).basis.repr (optionProductMap φ₀ φ x) i) ≤ p := by
  intro i
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i : Option ι, Fin (optionDimension d₀ d i))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none => exact h₀ k
  | some a => exact hφ a k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonFirst_real_mem_layer (n : ℕ) (x : ℝ ⊗[ℚ] F.comparisonSubalgebra π)
    (hx : x ∈ (F.comparisonFiltration π).realification.layer n) :
    realificationLieHom (F.comparisonFirst π) x ∈ F.ordinary.realification.layer n :=
  (F.comparisonFiltration π).realificationLieHom_mem_layer F.ordinary (F.comparisonFirst π)
    (fun j _ hj => F.comparisonFirst_mem_layer π j hj) n x hx

theorem comparisonSecond_real_mem_layer (n : ℕ) (x : ℝ ⊗[ℚ] F.comparisonSubalgebra π)
    (hx : x ∈ (F.comparisonFiltration π).realification.layer n) :
    realificationLieHom (F.comparisonSecond π) x ∈
      (F.squarefreeOrdinaryFiltration π).realification.layer n :=
  (F.comparisonFiltration π).realificationLieHom_mem_layer (F.squarefreeOrdinaryFiltration π)
    (F.comparisonSecond π) (fun j _ hj => F.comparisonSecond_mem_layer π j hj) n x hx

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonAmbient (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :=
  optionProduct (D.raiseStep (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))))
    (fun _ : PUnit.{1} => (M.squarefreeModel p B hB hstable).raiseStep
      (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))))

noncomputable def comparisonToAmbient :=
  optionProductMap (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))
    (fun _ : PUnit.{1} => M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))

theorem comparisonToAmbient_injective : Function.Injective M.comparisonToAmbient := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrFun h none) (congrFun h (some PUnit.unit))

theorem comparisonAmbient_geometry {p q : ℝ} (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) (hD : D.GeometryComplexityLE p)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q) :
    (M.comparisonAmbient p B hB hstable).GeometryComplexityLE ((p + q + 4) ^ 2) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have h := optionProduct_geometry
    (D.raiseStep (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))))
    (fun _ : PUnit.{1} => (M.squarefreeModel p B hB hstable).raiseStep
      (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))))
    (p := p + q + 1) (by linarith)
    (by simpa only [Fintype.card_punit, Nat.cast_one] using
      (show (1 : ℝ) ≤ p + q + 1 by linarith))
    ((D.raiseStep_geometry _ hD).mono _ (by linarith))
    (fun _ => ((M.squarefreeModel p B hB hstable).raiseStep_geometry _ hE).mono _ (by linarith))
  simpa only [comparisonAmbient, show p + q + 1 + 3 = p + q + 4 by ring] using h

theorem comparisonAmbient_point_logHeight (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (x : M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    {q : ℝ} (hx : ∀ k, rationalLogHeight
      ((D.basis.prod (M.squarefreeFinBasis p)).repr x.val k) ≤ q) :
    ∀ k, rationalLogHeight
      ((M.comparisonAmbient p B hB hstable).basis.repr (M.comparisonToAmbient x) k) ≤ q := by
  apply optionProductMap_point_logHeight
  · exact fun k => hx (Sum.inl k)
  · exact fun _ k => hx (Sum.inr k)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
