/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv

namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ M₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

namespace NilpotentLieFiltration

def optionFiltrations (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) :
    ∀ i : Option ι, NilpotentLieFiltration (optionLieSpace L₀ L i) s
  | none => F₀
  | some i => F i

@[simp] theorem optionFiltrations_none (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) : optionFiltrations F₀ F none = F₀ := rfl

@[simp] theorem optionFiltrations_some (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (i : ι) :
    optionFiltrations F₀ F (some i) = F i := rfl

end NilpotentLieFiltration

def optionMarkedComponents (φ : L₀ →ₗ⁅ℚ⁆ M₀) :
    ∀ i : Option ι, (∀ j : Option ι, optionLieSpace L₀ L j) →ₗ⁅ℚ⁆
      optionLieSpace M₀ L i
  | none => φ.comp (liePiEval none)
  | some i => liePiEval (some i)

def optionMarkedLieMap (φ : L₀ →ₗ⁅ℚ⁆ M₀) :
    (∀ i : Option ι, optionLieSpace L₀ L i) →ₗ⁅ℚ⁆
      (∀ i : Option ι, optionLieSpace M₀ L i) :=
  liePiMap (optionMarkedComponents (L := L) φ)

@[simp] theorem optionMarkedLieMap_none (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionMarkedLieMap φ x none = φ (x none) := rfl

@[simp] theorem optionMarkedLieMap_some (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) (i : ι) :
    optionMarkedLieMap φ x (some i) = x (some i) := rfl

theorem realification_optionMarkedLieMap_none (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval none) (realificationLieHom (optionMarkedLieMap φ) x) =
      realificationLieHom φ (realificationLieHom (liePiEval none) x) := by
  rw [optionMarkedLieMap, realification_liePiEval_liePiMap]
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add (realificationLieHom φ) _ _).symm

theorem realification_optionMarkedLieMap_some (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) (i : ι) :
    realificationLieHom (liePiEval (some i))
        (realificationLieHom (optionMarkedLieMap φ) x) =
      realificationLieHom (liePiEval (some i)) x := by
  rw [optionMarkedLieMap, realification_liePiEval_liePiMap]
  rfl

open NilpotentLieFiltration

theorem optionMarkedLieMap_mem_layer (F₀ : NilpotentLieFiltration L₀ s)
    (G₀ : NilpotentLieFiltration M₀ s) (F : ∀ i, NilpotentLieFiltration (L i) s)
    (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (hφ : ∀ n x, x ∈ F₀.layer n → φ x ∈ G₀.layer n)
    (n : ℕ) (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (pi (optionFiltrations F₀ F)).layer n) :
    optionMarkedLieMap φ x ∈ (pi (optionFiltrations G₀ F)).layer n := by
  apply (mem_pi_layer _ _ _).mpr
  intro i
  cases i with
  | none => exact hφ n _ ((mem_pi_layer _ _ _).mp hx none)
  | some i => exact (mem_pi_layer _ _ _).mp hx (some i)

variable [Fintype ι] [DecidableEq ι]

theorem realBCHPiEquiv_optionMarkedLieMap_none
    (F₀ : NilpotentLieFiltration L₀ s) (G₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : (pi (optionFiltrations F₀ F)).realification.Group) :
    realBCHPiEquiv (optionFiltrations G₀ F)
        (NilpotentLieBCHGroup.realificationMap
          (hnil := (pi (optionFiltrations F₀ F)).lowerCentralSeries_eq_bot)
          (hM := (pi (optionFiltrations G₀ F)).lowerCentralSeries_eq_bot)
          (optionMarkedLieMap φ) g) none =
      NilpotentLieBCHGroup.realificationMap
        (hnil := F₀.lowerCentralSeries_eq_bot) (hM := G₀.lowerCentralSeries_eq_bot)
        φ (realBCHPiEquiv (optionFiltrations F₀ F) g none) := by
  apply NilpotentLieBCHGroup.ext
  exact realification_optionMarkedLieMap_none φ g.coord

theorem realBCHPiEquiv_optionMarkedLieMap_some
    (F₀ : NilpotentLieFiltration L₀ s) (G₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : (pi (optionFiltrations F₀ F)).realification.Group) (i : ι) :
    realBCHPiEquiv (optionFiltrations G₀ F)
        (NilpotentLieBCHGroup.realificationMap
          (hnil := (pi (optionFiltrations F₀ F)).lowerCentralSeries_eq_bot)
          (hM := (pi (optionFiltrations G₀ F)).lowerCentralSeries_eq_bot)
          (optionMarkedLieMap φ) g) (some i) =
      realBCHPiEquiv (optionFiltrations F₀ F) g (some i) := by
  apply NilpotentLieBCHGroup.ext
  exact realification_optionMarkedLieMap_some φ g.coord i

end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s dL dM : ℕ} {d : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s dL)
    (Q : RationalFilteredNilmanifold M s dM)
    (E : ∀ a, RationalFilteredNilmanifold (Partner a) s (d a))
    (φ : L →ₗ⁅ℚ⁆ M)

theorem optionMarkedLieMap_native_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hφ : ∀ i j, rationalLogHeight (Q.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct Q E).basis.repr
      (optionMarkedLieMap (L := Partner) φ ((optionProduct D E).basis j)) i) ≤ p := by
  classical
  intro i j
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz :
    (Fintype.equivFin (Σ a : Option Pivot, Fin (optionDimension dM d a))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none =>
    change rationalLogHeight (Q.basis.repr
      (φ (productFinBasis (optionFactors D E) j none)) k) ≤ p
    rw [productFinBasis, Basis.reindex_apply]
    generalize hy :
      (Fintype.equivFin (Σ a : Option Pivot, Fin (optionDimension dL d a))).symm j = y
    rcases y with ⟨b, l⟩
    rw [Pi.basis_apply]
    cases b with
    | none =>
      rw [Pi.single_eq_same]
      exact hφ k l
    | some b =>
      rw [Pi.single_eq_of_ne (by simp : (none : Option Pivot) ≠ some b)]
      change rationalLogHeight (Q.basis.repr (φ (0 : L)) k) ≤ p
      rw [map_zero, map_zero]
      change rationalLogHeight (0 : ℚ) ≤ p
      simpa [rationalLogHeight] using hp
  | some a =>
    change rationalLogHeight ((E a).basis.repr
      (liePiEval (R := ℚ) (some a) ((optionProduct D E).basis j)) k) ≤ p
    exact rationalLogHeight_le_of_height
      (productProjection_matrix_height (optionFactors D E) (some a) j k)
      (by simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hp)

theorem optionMarkedLieMap_native_logHeight_max {p : ℝ}
    (hφ : ∀ i j, rationalLogHeight (Q.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct Q E).basis.repr
      (optionMarkedLieMap (L := Partner) φ ((optionProduct D E).basis j)) i) ≤ max p 0 :=
  optionMarkedLieMap_native_logHeight D Q E φ (le_max_right _ _)
    (fun i j => (hφ i j).trans (le_max_left _ _))

theorem optionMarkedLieMap_native_matrix_height {p : ℝ} (hp : 0 ≤ p)
    (hφ : ∀ i j, rationalLogHeight (Q.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, RationalHeightLE ((optionProduct Q E).basis.repr
      (optionMarkedLieMap (L := Partner) φ ((optionProduct D E).basis j)) i)
      ⌈Real.exp p⌉₊ := by
  intro i j
  exact rationalHeightLE_ceil_exp (optionMarkedLieMap_native_logHeight D Q E φ hp hφ i j)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem optionMarkedLieMap_piRealOrbit_log
    {ι : Type v} [Fintype ι] {L₀ M₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ e₀ : ℕ} {d : ι → ℕ} {σ : Type*} {w : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (Q₀ : RationalFilteredNilmanifold M₀ s e₀)
    (E : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : ∀ i, (optionFactors D₀ E i).filtration.realification.PolynomialOrbit w)
    (h : ∀ i, (optionFactors Q₀ E i).filtration.realification.PolynomialOrbit w)
    (hnone : VectorPolynomial.map
      ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) (g none).log =
        (h none).log)
    (hsome : ∀ i, (g (some i)).log = (h (some i)).log) :
    VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap φ)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (optionFactors D₀ E i).filtration) g).log =
        (piRealOrbit (fun i => (optionFactors Q₀ E i).filtration) h).log := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_map]
  apply ((Pi.basis (fun i => (optionFactors Q₀ E i).basis)).baseChange ℝ).repr.injective
  ext ⟨i, k⟩
  rw [realification_pi_basis_repr, realification_pi_basis_repr]
  change ((optionFactors Q₀ E i).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval i)
      (realificationLieHom (optionMarkedLieMap φ)
        (coefficients (piRealOrbit (fun i => (optionFactors D₀ E i).filtration) g).log α))) k =
    ((optionFactors Q₀ E i).basis.baseChange ℝ).repr
      (realificationLieHom (liePiEval i)
        (coefficients (piRealOrbit (fun i => (optionFactors Q₀ E i).filtration) h).log α)) k
  rw [piRealOrbit_coefficient]
  cases i with
  | none =>
    rw [realification_optionMarkedLieMap_none, piRealOrbit_coefficient]
    have hα := congrArg (fun q => coefficients q α) hnone
    erw [coefficients_map] at hα
    exact congrArg (fun x => (Q₀.basis.baseChange ℝ).repr x k) hα
  | some i =>
    rw [realification_optionMarkedLieMap_some, piRealOrbit_coefficient]
    exact congrArg (fun q => ((E i).basis.baseChange ℝ).repr (coefficients q α) k)
      (hsome i)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

variable {J : Type v} {L Y : Type u} {M : J → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing Y] [LieAlgebra ℚ Y]
    [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]

theorem optionMarkedLieMap_surjective (φ : L →ₗ⁅ℚ⁆ Y)
    (hφ : Function.Surjective φ) :
    Function.Surjective (optionMarkedLieMap (L := M) φ) := by
  intro y
  obtain ⟨x, hx⟩ := hφ (y none)
  let z : ∀ i : Option J, optionLieSpace L M i
    | none => x
    | some j => y (some j)
  refine ⟨z, ?_⟩
  funext i
  cases i with
  | none => exact hx
  | some j => rfl

theorem quotientInducedMark_surjective (ideal : LieIdeal ℚ L)
    (φ : L →ₗ⁅ℚ⁆ Y) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : Function.Surjective φ) :
    Function.Surjective (quotientInducedMark ideal φ hker) := by
  intro y
  obtain ⟨x, hx⟩ := hφ y
  exact ⟨lieQuotientMap ideal x, (quotientInducedMark_mk ideal φ hker x).trans hx⟩

theorem optionQuotientMarkedLieMap_surjective (ideal : LieIdeal ℚ L)
    (φ : L →ₗ⁅ℚ⁆ Y) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : Function.Surjective φ) :
    Function.Surjective (optionMarkedLieMap (L := M) (quotientInducedMark ideal φ hker)) :=
  optionMarkedLieMap_surjective _ (quotientInducedMark_surjective ideal φ hker hφ)

end Erdos3

end

end OAI
