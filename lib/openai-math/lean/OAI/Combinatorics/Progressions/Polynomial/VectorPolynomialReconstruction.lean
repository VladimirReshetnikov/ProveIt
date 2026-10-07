-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.Compat.TensorProduct
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

abbrev VectorPolynomial (σ R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  MvPolynomial σ R ⊗[R] V

namespace VectorPolynomial

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def coefficients : VectorPolynomial σ R V ≃ₗ[R] (σ →₀ ℕ) →₀ V := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials σ R)

noncomputable def monomial (α : σ →₀ ℕ) (v : V) : VectorPolynomial σ R V :=
  MvPolynomial.monomial α (1 : R) ⊗ₜ[R] v

@[simp] theorem coefficients_tmul (p : MvPolynomial σ R) (v : V) (α : σ →₀ ℕ) :
    coefficients (p ⊗ₜ[R] v) α = p.coeff α • v := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _

@[simp] theorem coefficients_monomial (α : σ →₀ ℕ) (v : V) :
    coefficients (monomial (R := R) α v) = Finsupp.single α v := by
  classical
  ext β
  by_cases h : α = β
  · subst β
    simp [monomial]
  · simp [monomial, h, Ne.symm h]

@[simp] theorem coefficients_symm_single (α : σ →₀ ℕ) (v : V) :
    (coefficients (R := R)).symm (Finsupp.single α v) = monomial α v := by
  apply coefficients.injective
  simp

theorem sum_monomial_coefficients (p : VectorPolynomial σ R V) :
    (coefficients p).sum (fun α v => monomial (R := R) α v) = p := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft_symm_apply
    (MvPolynomial.basisMonomials σ R) (coefficients p)).symm.trans
      (coefficients.symm_apply_apply p)

noncomputable def map (f : V →ₗ[R] W) : VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R W :=
  f.lTensor (MvPolynomial σ R)

@[simp] theorem map_monomial (f : V →ₗ[R] W) (α : σ →₀ ℕ) (v : V) :
    map f (monomial α v) = monomial α (f v) := rfl

@[simp] theorem coefficients_map (f : V →ₗ[R] W) (p : VectorPolynomial σ R V)
    (α : σ →₀ ℕ) : coefficients (map f p) α = f (coefficients p α) := by
  induction p using TensorProduct.inductionOn with
  | tmul q v => simp [map]
  | add p q hp hq => simp [hp, hq]

def DegreeLE (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) : Prop :=
  ∀ α, d < Finsupp.weight w α → coefficients p α = 0

theorem degreeLE_iff (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔ ∀ α ∈ (coefficients p).support, Finsupp.weight w α ≤ d := by
  classical
  simp only [DegreeLE, Finsupp.mem_support_iff]
  exact ⟨fun h α hα => le_of_not_gt (fun hd => hα (h α hd)),
    fun h α hd => Classical.byContradiction (fun hα => (not_le_of_gt hd) (h α hα))⟩

theorem DegreeLE.map {w : σ → ℕ} {d : ℕ} {p : VectorPolynomial σ R V}
    (hp : DegreeLE w d p) (f : V →ₗ[R] W) : DegreeLE w d (map f p) := by
  intro α hα
  rw [coefficients_map, hp α hα, f.map_zero]

theorem degreeLE_map_iff (w : σ → ℕ) (d : ℕ) (f : V →ₗ[R] W)
    (hf : Function.Injective f) (p : VectorPolynomial σ R V) :
    DegreeLE w d (map f p) ↔ DegreeLE w d p := by
  refine ⟨fun h α hα => hf ?_, fun h => h.map f⟩
  simpa only [coefficients_map, f.map_zero] using h α hα

noncomputable def eval (x : σ → R) : VectorPolynomial σ R V →ₗ[R] V :=
  (TensorProduct.lid R V).toLinearMap.comp
    ((MvPolynomial.aeval x).toLinearMap.rTensor V)

@[simp] theorem eval_tmul (x : σ → R) (q : MvPolynomial σ R) (v : V) :
    eval x (q ⊗ₜ[R] v) = MvPolynomial.aeval x q • v := rfl

@[simp] theorem eval_monomial (x : σ → R) (α : σ →₀ ℕ) (v : V) :
    eval x (monomial α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.eval_monomial]

@[simp] theorem eval_map (x : σ → R) (f : V →ₗ[R] W) (p : VectorPolynomial σ R V) :
    eval x (map f p) = f (eval x p) := by
  induction p using TensorProduct.inductionOn with
  | tmul q v => simp [map]
  | add p q hp hq => simp [hp, hq]

end VectorPolynomial
end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

noncomputable def monomialScale {σ : Type*} (T : σ → ℝ) (α : σ →₀ ℕ) : ℝ :=
  α.prod (fun i n => T i ^ n)

@[simp] theorem monomialScale_zero {σ : Type*} (T : σ → ℝ) : monomialScale T 0 = 1 := by
  simp [monomialScale]

theorem monomialScale_pos {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 0 < T i) (α : σ →₀ ℕ) :
    0 < monomialScale T α := by
  classical
  exact Finset.prod_pos (fun i _ => pow_pos (hT i) _)

theorem one_le_monomialScale {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i) (α : σ →₀ ℕ) :
    1 ≤ monomialScale T α := by
  classical
  exact Finset.one_le_prod₀ (fun index _ => one_le_pow₀ (hT index))

theorem le_monomialScale_of_ne_zero {σ : Type*} (T : σ → ℝ) {R : ℝ}
    (hR : 1 ≤ R) (hT : ∀ i, R ≤ T i) {α : σ →₀ ℕ} (hα : α ≠ 0) :
    R ≤ monomialScale T α := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hα
    ext i
    exact hn i
  have hTi : 1 ≤ T i := hR.trans (hT i)
  have hp : T i ≤ T i ^ α i := by
    simpa only [pow_one] using pow_le_pow_right₀ hTi (Nat.one_le_iff_ne_zero.mpr hi)
  have hs : ({i} : Finset σ) ⊆ α.support :=
    Finset.singleton_subset_iff.mpr (Finsupp.mem_support_iff.mpr hi)
  have hprod := Finset.prod_le_prod_of_subset_of_one_le₀ hs
    (fun index _ => pow_nonneg (zero_le_one.trans (hR.trans (hT index))) (α index))
    (fun index _ _ => one_le_pow₀ (hR.trans (hT index)))
  exact (hT i).trans (hp.trans (by
    simpa only [Finset.prod_singleton, monomialScale, Finsupp.prod] using hprod))

theorem monomialScale_add {σ : Type*} (T : σ → ℝ) (α β : σ →₀ ℕ) :
    monomialScale T (α + β) = monomialScale T α * monomialScale T β := by
  classical
  exact Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def multiplyVariable (i : σ) :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  (LinearMap.mulLeft ℚ (MvPolynomial.X i : MvPolynomial σ ℚ)).rTensor V

@[simp] theorem multiplyVariable_tmul (i : σ) (P : MvPolynomial σ ℚ) (v : V) :
    multiplyVariable i (P ⊗ₜ[ℚ] v) = (MvPolynomial.X i * P) ⊗ₜ[ℚ] v := rfl

theorem coefficients_multiplyVariable [DecidableEq σ] (i : σ)
    (P : VectorPolynomial σ ℚ V) (β : σ →₀ ℕ) :
    coefficients (multiplyVariable i P) β =
      if i ∈ β.support then coefficients P (β - Finsupp.single i 1) else 0 := by
  induction P using TensorProduct.inductionOn with
  | tmul p v =>
    rw [multiplyVariable_tmul, coefficients_tmul, MvPolynomial.coeff_X_mul', coefficients_tmul]
    split_ifs <;> simp
  | add P Q hP hQ =>
    simp only [map_add, Finsupp.add_apply, hP, hQ]
    split_ifs <;> simp

noncomputable def eulerSum [Fintype σ] :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  ∑ i, (multiplyVariable i).comp ((MvPolynomial.pderiv i).toLinearMap.rTensor V)

theorem eulerSum_monomial [Fintype σ] (β : σ →₀ ℕ) (v : V) :
    eulerSum (monomial (R := ℚ) β v) =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) β : ℚ) • monomial β v := by
  have hdegree : β.degree = Finsupp.weight (fun _ : σ => (1 : ℕ)) β :=
    DFunLike.congr_fun Finsupp.degree_eq_weight_one β
  have h := (MvPolynomial.isHomogeneous_monomial (1 : ℚ) hdegree).sum_X_mul_pderiv
  simp only [eulerSum, LinearMap.sum_apply, LinearMap.comp_apply, monomial,
    LinearMap.rTensor_tmul, multiplyVariable_tmul]
  change (∑ i, (MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial β (1 : ℚ))) ⊗ₜ[ℚ] v) = _
  rw [← TensorProduct.sum_tmul, h]
  simp only [Nat.cast_smul_eq_nsmul, TensorProduct.smul_tmul']

theorem eulerSum_eq_degree_smul [Fintype σ] (d : ℕ) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0) :
    eulerSum P = (d : ℚ) • P := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients P]
  conv_rhs => rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, eulerSum_monomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have he : Finsupp.weight (fun _ : σ => (1 : ℕ)) β = d := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hβ) (hP β hn)
  rw [he]

noncomputable def reconstructDerivatives [Fintype σ] (d : ℕ) :
    (σ → VectorPolynomial σ ℚ V) →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  (d : ℚ)⁻¹ • ∑ i, (multiplyVariable i).comp (LinearMap.proj i)

theorem reconstructDerivatives_apply [Fintype σ] (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V) :
    reconstructDerivatives d P = (d : ℚ)⁻¹ • ∑ i, multiplyVariable i (P i) := by
  simp only [reconstructDerivatives, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

theorem reconstructDerivatives_partial [Fintype σ] {d : ℕ} (hd : 0 < d)
    (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0) :
    reconstructDerivatives d (fun i => (MvPolynomial.pderiv i).toLinearMap.rTensor V P) = P := by
  rw [reconstructDerivatives_apply]
  have he := eulerSum_eq_degree_smul d P hP
  simp only [eulerSum, LinearMap.sum_apply, LinearMap.comp_apply] at he
  rw [he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]

theorem coefficients_reconstructDerivatives [Fintype σ] [DecidableEq σ] (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V) (β : σ →₀ ℕ) :
    coefficients (reconstructDerivatives d P) β =
      (d : ℚ)⁻¹ • ∑ i, if i ∈ β.support then coefficients (P i) (β - Finsupp.single i 1) else 0 := by
  rw [reconstructDerivatives_apply]
  simp only [map_smul, Finsupp.smul_apply, map_sum, Finsupp.finsetSum_apply,
    coefficients_multiplyVariable]

theorem reconstructDerivatives_mem [Fintype σ] (W : Submodule ℚ V) (d : ℕ)
    (P : σ → VectorPolynomial σ ℚ V)
    (hP : ∀ i β, coefficients (P i) β ∈ W) :
    ∀ β, coefficients (reconstructDerivatives d P) β ∈ W := by
  classical
  intro β
  rw [coefficients_reconstructDerivatives]
  apply W.smul_mem
  apply W.sum_mem
  intro i _
  split_ifs
  · exact hP i _
  · exact W.zero_mem

theorem reconstructDerivatives_homogeneous [Fintype σ] {d : ℕ} (hd : 0 < d)
    (P : σ → VectorPolynomial σ ℚ V)
    (hP : ∀ i β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d - 1 → coefficients (P i) β = 0) :
    ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d →
      coefficients (reconstructDerivatives d P) β = 0 := by
  classical
  intro β hβ
  rw [coefficients_reconstructDerivatives]
  suffices (∑ i, if i ∈ β.support then coefficients (P i) (β - Finsupp.single i 1) else 0) = 0 by
    rw [this, smul_zero]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · apply hP
    have hw := Finsupp.weight_sub_single_add (w := fun _ : σ => (1 : ℕ))
      (Finsupp.mem_support_iff.mp hi)
    omega
  · rfl

theorem homogeneous_derivative_split_mod [Fintype σ] (W : Submodule ℚ V)
    {d : ℕ} (hd : 0 < d) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ β, Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ d → coefficients P β = 0)
    (S R : σ → VectorPolynomial σ ℚ V)
    (hsplit : ∀ i β, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor V P - S i - R i) β ∈ W) :
    ∀ β, coefficients (P - reconstructDerivatives d S - reconstructDerivatives d R) β ∈ W := by
  let D : σ → VectorPolynomial σ ℚ V := fun i => (MvPolynomial.pderiv i).toLinearMap.rTensor V P
  have he : reconstructDerivatives d (D - S - R) =
      P - reconstructDerivatives d S - reconstructDerivatives d R := by
    rw [map_sub, map_sub, reconstructDerivatives_partial hd P hP]
  rw [← he]
  exact reconstructDerivatives_mem W d (D - S - R) hsplit

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ ι R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def coefficientTensorBasis (b : Basis ι R V) :
    Basis ((σ →₀ ℕ) × ι) R (VectorPolynomial σ R V) :=
  (MvPolynomial.basisMonomials σ R).tensorProduct b

@[simp] theorem coefficientTensorBasis_apply (b : Basis ι R V) (α : σ →₀ ℕ) (i : ι) :
    coefficientTensorBasis b (α, i) = monomial α (b i) := by
  simp [coefficientTensorBasis, monomial]

theorem coefficientTensorBasis_repr (b : Basis ι R V) (p : VectorPolynomial σ R V)
    (α : σ →₀ ℕ) (i : ι) :
    (coefficientTensorBasis b).repr p (α, i) = b.repr (coefficients p α) i := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
      simp only [coefficientTensorBasis, Basis.tensorProduct_repr_tmul_apply, coefficients_tmul,
        map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr v i * q.coeff α = q.coeff α * b.repr v i
      exact mul_comm _ _
  | add p q hp hq =>
      simp only [map_add, Finsupp.add_apply, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V]

noncomputable def coordinate (f : V →+ S) (p : VectorPolynomial σ R V) : MvPolynomial σ S :=
  (MvPolynomial.basisMonomials σ S).repr.symm ((coefficients p).mapRange f f.map_zero)

@[simp] theorem coeff_coordinate (f : V →+ S) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    (coordinate f p).coeff α = f (coefficients p α) := by
  change ((MvPolynomial.basisMonomials σ S).repr
    ((MvPolynomial.basisMonomials σ S).repr.symm _)) α = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem coordinate_monomial (f : V →+ S) (α : σ →₀ ℕ) (v : V) :
    coordinate f (monomial (R := R) α v) = MvPolynomial.monomial α (f v) := by
  classical
  ext β
  by_cases h : α = β
  · subst β
    simp
  · simp [h, Ne.symm h]

@[simp] theorem coordinate_sum {κ : Type*} (f : V →+ S) (u : Finset κ)
    (p : κ → VectorPolynomial σ R V) :
    coordinate f (∑ i ∈ u, p i) = ∑ i ∈ u, coordinate f (p i) := by
  ext α
  simp only [coeff_coordinate, map_sum, Finsupp.finsetSum_apply, MvPolynomial.coeff_sum]

theorem scalar_weightedDegree_le_iff (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ S) :
    p.weightedTotalDegree w ≤ d ↔
      ∀ α, d < Finsupp.weight w α → p.coeff α = 0 := by
  classical
  simp only [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff,
    MvPolynomial.mem_support_iff]
  exact ⟨fun h α hd => Classical.byContradiction (fun hα => (not_le_of_gt hd) (h α hα)),
    fun h α hα => le_of_not_gt (fun hd => hα (h α hd))⟩

theorem degreeLE_iff_coordinates (w : σ → ℕ) (d : ℕ)
    (f : ι → V →+ S) (hsep : ∀ v, (∀ i, f i v = 0) → v = 0)
    (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔ ∀ i, (coordinate (f i) p).weightedTotalDegree w ≤ d := by
  simp only [scalar_weightedDegree_le_iff, coeff_coordinate]
  constructor
  · intro hp i α hα
    rw [hp α hα, map_zero]
  · intro hp α hα
    exact hsep _ (fun i => hp i α hα)

theorem degreeLE_iff_basis_coordinates [Module S V]
    (e : Module.Basis ι S V) (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE w d p ↔
      ∀ i, (coordinate (e.coord i).toAddMonoidHom p).weightedTotalDegree w ≤ d := by
  apply degreeLE_iff_coordinates
  intro v hv
  apply e.repr.injective
  ext i
  have hi : (e.coord i) v = 0 := hv i
  simpa only [map_zero, Finsupp.zero_apply, Module.Basis.coord_apply] using hi

theorem degreeLE_one_iff_basis_totalDegree [Module S V]
    (e : Module.Basis ι S V) (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE (1 : σ → ℕ) d p ↔
      ∀ i, (coordinate (e.coord i).toAddMonoidHom p).totalDegree ≤ d := by
  simpa only [MvPolynomial.weightedTotalDegree_one] using
    degreeLE_iff_basis_coordinates e (1 : σ → ℕ) d p

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W) :
    VectorPolynomial σ R (V × W) :=
  map (LinearMap.inl R V W) p + map (LinearMap.inr R V W) q

@[simp] theorem coefficients_pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W)
    (α : σ →₀ ℕ) : coefficients (pair p q) α = (coefficients p α, coefficients q α) := by
  simp [pair]

@[simp] theorem eval_pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W) (x : σ → R) :
    eval x (pair p q) = (eval x p, eval x q) := by
  simp [pair]

noncomputable def restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) : VectorPolynomial σ R P :=
  coefficients.symm
    { support := (coefficients p).support
      toFun α := ⟨coefficients p α, hp α⟩
      mem_support_toFun := by intro α; simp }

@[simp] theorem coefficients_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) (α : σ →₀ ℕ) :
    (coefficients (restrictCoefficients P p hp) α : V) = coefficients p α := by
  simp only [restrictCoefficients, LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem map_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) : map P.subtype (restrictCoefficients P p hp) = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact coefficients_restrictCoefficients P p hp α

theorem eval_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) (x : σ → R) :
    (eval (V := P) x (restrictCoefficients P p hp) : V) = eval x p := by
  change P.subtype (eval x (restrictCoefficients P p hp)) = _
  rw [← eval_map, map_restrictCoefficients]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def coefficientSupport (S : Set (σ →₀ ℕ)) : Submodule R (VectorPolynomial σ R V) where
  carrier := {p | ∀ a, a ∉ S → coefficients p a = 0}
  zero_mem' := by simp
  add_mem' hp hq := by
    intro a ha
    simp only [map_add, Finsupp.add_apply, hp a ha, hq a ha, add_zero]
  smul_mem' c p hp := by
    intro a ha
    simp only [map_smul, Finsupp.smul_apply, hp a ha, smul_zero]

@[simp] theorem mem_coefficientSupport (S : Set (σ →₀ ℕ)) (p : VectorPolynomial σ R V) :
    p ∈ coefficientSupport S ↔ ∀ a, a ∉ S → coefficients p a = 0 := Iff.rfl

theorem coefficientSupport_mono {S T : Set (σ →₀ ℕ)} (hST : S ⊆ T) :
    coefficientSupport (R := R) (V := V) S ≤ coefficientSupport T := by
  intro p hp a ha
  exact hp a (fun h => ha (hST h))

theorem monomial_mem_coefficientSupport {S : Set (σ →₀ ℕ)} {a : σ →₀ ℕ}
    (ha : a ∈ S) (v : V) : monomial (R := R) a v ∈ coefficientSupport S := by
  classical
  intro b hb
  have hab : a ≠ b := by rintro rfl; exact hb ha
  simp [hab]

theorem coefficientSupport_inf (S T : Set (σ →₀ ℕ)) :
    coefficientSupport (R := R) (V := V) (S ∩ T) =
      coefficientSupport S ⊓ coefficientSupport T := by
  ext p
  constructor
  · intro hp
    exact ⟨coefficientSupport_mono Set.inter_subset_left hp,
      coefficientSupport_mono Set.inter_subset_right hp⟩
  · rintro ⟨hS, hT⟩ a ha
    by_cases h : a ∈ S
    · exact hT a (fun h' => ha ⟨h, h'⟩)
    · exact hS a h

@[simp] theorem coefficientSupport_empty :
    coefficientSupport (R := R) (V := V) (∅ : Set (σ →₀ ℕ)) = ⊥ := by
  apply bot_unique
  intro p hp
  apply coefficients.injective
  ext a
  exact hp a (Set.notMem_empty a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V]

noncomputable def ofScalar (f : S →+ V) (p : MvPolynomial σ S) : VectorPolynomial σ R V :=
  coefficients.symm (((MvPolynomial.basisMonomials σ S).repr p).mapRange f f.map_zero)

@[simp] theorem coefficients_ofScalar (f : S →+ V) (p : MvPolynomial σ S) (α : σ →₀ ℕ) :
    coefficients (ofScalar (R := R) f p) α = f (p.coeff α) := by
  simp only [ofScalar, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
  rfl

variable [Fintype ι] [Module S V]

noncomputable def ofCoordinates (e : Module.Basis ι S V) (p : ι → MvPolynomial σ S) :
    VectorPolynomial σ R V :=
  ∑ i, ofScalar ((LinearMap.id : S →ₗ[S] S).smulRight (e i)).toAddHom (p i)

theorem coefficients_ofCoordinates (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (α : σ →₀ ℕ) :
    coefficients (ofCoordinates (R := R) e p) α = ∑ index, (p index).coeff α • e index := by
  simp [ofCoordinates]

@[simp] theorem coordinate_ofCoordinates (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (i : ι) :
    coordinate (e.coord i).toAddMonoidHom (ofCoordinates (R := R) e p) = p i := by
  classical
  ext α
  rw [coeff_coordinate, coefficients_ofCoordinates]
  change e.coord i (∑ index, (p index).coeff α • e index) = _
  simp [Module.Basis.coord_apply, Finsupp.single_apply, mul_ite]

@[simp] theorem ofCoordinates_coordinate (e : Module.Basis ι S V)
    (p : VectorPolynomial σ R V) :
    ofCoordinates e (fun i => coordinate (e.coord i).toAddMonoidHom p) = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_ofCoordinates]
  simp only [coeff_coordinate]
  change (∑ i, e.repr (coefficients p α) i • e i) = coefficients p α
  exact e.sum_repr _

noncomputable def coordinatesEquiv (e : Module.Basis ι S V) :
    VectorPolynomial σ R V ≃ (ι → MvPolynomial σ S) where
  toFun p i := coordinate (e.coord i).toAddMonoidHom p
  invFun := ofCoordinates e
  left_inv := ofCoordinates_coordinate e
  right_inv p := funext (coordinate_ofCoordinates e p)

end Erdos3.VectorPolynomial

end

end OAI
