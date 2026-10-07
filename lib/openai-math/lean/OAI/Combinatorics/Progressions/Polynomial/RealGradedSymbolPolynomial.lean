/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use older Finsupp reindexing names and direct application of simplified
coordinate identities on Lean 4.32; allow deeper elaboration of quotient
instances. Mathematical statements unchanged. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Finsupp.Defs
import OAI.Combinatorics.Progressions.Estimates.SquareGradedRelative
import OAI.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def mixedCoordinates (b : Basis ι S V) :
    VectorPolynomial σ R V ≃ₗ[R] ((σ →₀ ℕ) × ι) →₀ S :=
  coefficients.trans ((Finsupp.mapRange.linearEquiv (b.repr.restrictScalars R)).trans
    (Finsupp.curryLinearEquiv R).symm)

@[simp] theorem mixedCoordinates_apply (b : Basis ι S V)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) (i : ι) :
    mixedCoordinates b p (α, i) = b.repr (coefficients p α) i := rfl

@[simp] theorem mixedCoordinates_symm_apply (b : Basis ι S V)
    (c : ((σ →₀ ℕ) × ι) →₀ S) (α : σ →₀ ℕ) (i : ι) :
    b.repr (coefficients ((mixedCoordinates b).symm c : VectorPolynomial σ R V) α) i =
      c (α, i) := by
  rw [← mixedCoordinates_apply, LinearEquiv.apply_symm_apply]

noncomputable def ofSupportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : (A →₀ S) →ₗ[R] VectorPolynomial σ R V :=
  (mixedCoordinates b).symm.toLinearMap.comp (Finsupp.lmapDomain S R Subtype.val)

@[simp] theorem ofSupportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) (z : A) :
    b.repr (coefficients (ofSupportedCoordinates (R := R) b A c) z.val.1) z.val.2 = c z := by
  change mixedCoordinates b ((mixedCoordinates b).symm _) z.val = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective c z

theorem ofSupportedCoordinates_apply_of_not_mem (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) (α : σ →₀ ℕ) (i : ι)
    (h : (α, i) ∉ A) :
    b.repr (coefficients (ofSupportedCoordinates (R := R) b A c) α) i = 0 := by
  change mixedCoordinates b ((mixedCoordinates b).symm _) (α, i) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨z, hz⟩
  exact h (hz ▸ z.property)

noncomputable def supportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : VectorPolynomial σ R V →ₗ[R] A →₀ S :=
  (Finsupp.lsubtypeDomain A).comp (mixedCoordinates b).toLinearMap

@[simp] theorem supportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (p : VectorPolynomial σ R V) (z : A) :
    supportedCoordinates b A p z = b.repr (coefficients p z.val.1) z.val.2 := rfl

@[simp] theorem supportedCoordinates_ofSupportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) :
    supportedCoordinates b A (ofSupportedCoordinates (R := R) b A c) = c := by
  ext z
  exact ofSupportedCoordinates_apply b A c z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realificationLinearEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) ≃ₗ[ℚ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) :=
  TensorProduct.leftComm ℚ ℝ (MvPolynomial σ ℚ) V

@[simp] theorem coefficients_realificationLinearEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ V) (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.inductionOn with
  | tmul f v =>
    change coefficients (f ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v)) α = _
    rw [coefficients_tmul, coefficients_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

theorem realificationLinearEquiv_eq_zero_iff
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) :
    x = 0 ↔ ∀ α, coefficients (realificationLinearEquiv x) α = 0 := by
  constructor
  · rintro rfl α
    simp only [map_zero, Finsupp.zero_apply]
  · intro hx
    apply realificationLinearEquiv.injective
    apply coefficients.injective
    ext α
    simpa only [map_zero, Finsupp.zero_apply] using hx α

end Linear

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

section General

private theorem ring_zero_lie {K : Type*} [LieRing K] (x : K) : ⁅(0 : K), x⁆ = 0 := zero_lie x

private theorem ring_lie_zero {K : Type*} [LieRing K] (x : K) : ⁅x, (0 : K)⁆ = 0 := lie_zero x

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {N : Type*} [LieRing N] [LieAlgebra R N]

noncomputable def lieTensorLeftComm :
    (A ⊗[R] (B ⊗[R] N)) ≃ₗ⁅R⁆ (B ⊗[R] (A ⊗[R] N)) :=
  { TensorProduct.leftComm R A B N with
  map_lie' {x y} := by
    change TensorProduct.leftComm R A B N ⁅x, y⁆ =
      ⁅TensorProduct.leftComm R A B N x, TensorProduct.leftComm R A B N y⁆
    induction x using TensorProduct.inductionOn with
    | tmul a p =>
      induction y using TensorProduct.inductionOn with
      | tmul b q =>
        induction p using TensorProduct.inductionOn with
        | tmul f u =>
          induction q using TensorProduct.inductionOn with
          | tmul g v =>
            simp only [LieAlgebra.ExtendScalars.bracket_tmul, TensorProduct.leftComm_tmul]
          | add q r hq hr =>
            rw [TensorProduct.tmul_add, LieRing.lie_add, map_add, hq, hr, map_add, LieRing.lie_add]
        | add p q hp hq =>
          rw [TensorProduct.tmul_add, LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]
      | add y z hy hz => rw [LieRing.lie_add, map_add, hy, hz, map_add, LieRing.lie_add]
    | add x z hx hz => rw [LieRing.add_lie, map_add, hx, hz, map_add, LieRing.add_lie] }

end General

noncomputable def realificationLieEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) ≃ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  lieTensorLeftComm

@[simp] theorem realificationLieEquiv_tmul_tmul (a : ℝ) (p : MvPolynomial σ ℚ) (v : L) :
    realificationLieEquiv (a ⊗ₜ[ℚ] (p ⊗ₜ[ℚ] v)) = p ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v) :=
  TensorProduct.leftComm_tmul ℚ _ _ _

@[simp] theorem coefficients_realificationLieEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (realificationLieEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.inductionOn with
  | tmul f v =>
    rw [realificationLieEquiv_tmul_tmul, coefficients_tmul, coefficients_tmul,
      TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

theorem eval_realificationLieEquiv_tmul {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (r : ℝ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (realificationLieEquiv (r ⊗ₜ[ℚ] p)) = r ⊗ₜ[ℚ] eval x p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
    rw [realificationLieEquiv_tmul_tmul, eval_tmul, eval_tmul, TensorProduct.tmul_smul]
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable instance realModule : Module ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) :=
  (realificationLinearEquiv (σ := σ) (V := V)).symm.toAddEquiv.module ℝ

noncomputable def realificationRealLinearEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) ≃ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) :=
  ((realificationLinearEquiv (σ := σ) (V := V)).symm.toAddEquiv.linearEquiv ℝ).symm

@[simp] theorem realificationRealLinearEquiv_apply
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) :
    realificationRealLinearEquiv x = realificationLinearEquiv x := rfl

instance realScalarTower : IsScalarTower ℚ ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) :=
  LinearEquiv.isScalarTower ℝ (realificationLinearEquiv (σ := σ) (V := V)).symm

theorem coefficients_realification_smul (a : ℝ)
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv (a • x)) α =
      a • coefficients (realificationLinearEquiv x) α := by
  induction x using TensorProduct.inductionOn with
  | tmul r p =>
    rw [TensorProduct.smul_tmul', coefficients_realificationLinearEquiv_tmul,
      coefficients_realificationLinearEquiv_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [smul_add, map_add, Finsupp.add_apply, hx, hy]

@[simp] theorem coefficients_smul_real (a : ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) (α : σ →₀ ℕ) :
    coefficients (a • P) α = a • coefficients P α := by
  obtain ⟨x, rfl⟩ := realificationRealLinearEquiv.surjective P
  rw [← map_smul, realificationRealLinearEquiv_apply, realificationRealLinearEquiv_apply]
  exact coefficients_realification_smul a x α

noncomputable def realCoefficient (α : σ →₀ ℕ) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) →ₗ[ℝ] ℝ ⊗[ℚ] V where
  toFun P := coefficients P α
  map_add' P Q := by simp only [map_add, Finsupp.add_apply]
  map_smul' a P := coefficients_smul_real a P α

@[simp] theorem realCoefficient_apply (α : σ →₀ ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) : realCoefficient α P = coefficients P α := rfl

noncomputable def realMonomial (α : σ →₀ ℕ) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) where
  toFun := monomial α
  map_add' x y := by
    apply coefficients.injective
    simp only [coefficients_monomial, map_add, Finsupp.single_add]
  map_smul' a x := by
    apply coefficients.injective
    ext β
    simp only [coefficients_smul_real, coefficients_monomial]
    exact DFunLike.congr_fun (Finsupp.smul_single a α x).symm β

@[simp] theorem realMonomial_apply (α : σ →₀ ℕ) (x : ℝ ⊗[ℚ] V) :
    realMonomial α x = monomial (R := ℚ) α x := rfl

end Linear

section Lie

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieEquiv_smul (a : ℝ)
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) :
    realificationLieEquiv (a • x) = a • realificationLieEquiv x :=
  (realificationRealLinearEquiv (σ := σ) (V := L)).map_smul a x

noncomputable instance realLieAlgebra : LieAlgebra ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) where
  lie_smul a P Q := by
    obtain ⟨p, rfl⟩ := realificationLieEquiv.surjective P
    obtain ⟨q, rfl⟩ := realificationLieEquiv.surjective Q
    change ⁅realificationLieEquiv p, a • realificationLieEquiv q⁆ =
      a • ⁅realificationLieEquiv p, realificationLieEquiv q⁆
    rw [← realificationLieEquiv_smul, ← LieEquiv.map_lie, lie_smul,
      realificationLieEquiv_smul, LieEquiv.map_lie]

end Lie

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

section BasisCriterion

attribute [local instance 100] LieRing.ofAssociativeRing

theorem linear_map_lie_of_basis {R V W ι : Type*} [CommRing R]
    [LieRing V] [LieAlgebra R V] [LieRing W] [LieAlgebra R W]
    (b : Basis ι R V) (f : V →ₗ[R] W)
    (h : ∀ i j, f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆) (x y : V) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  have he : (LieModule.toEnd R V V).toLinearMap.compr₂ f =
      (LieModule.toEnd R W W).toLinearMap.compl₁₂ f f :=
    LinearMap.ext_basis b b h
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

end BasisCriterion

namespace VectorPolynomial

theorem ofSupportedCoordinates_single {σ ι R S V : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
    (b : Basis ι S V) (A : Set ((σ →₀ ℕ) × ι)) (z : A) (c : S) :
    ofSupportedCoordinates (R := R) b A (Finsupp.single z c) =
      monomial z.val.1 (c • b z.val.2) := by
  classical
  apply (mixedCoordinates b).injective
  change mixedCoordinates b ((mixedCoordinates b).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change Finsupp.mapDomain Subtype.val (Finsupp.single z c) = _
  rw [Finsupp.mapDomain_single]
  apply Finsupp.ext
  rintro ⟨α, i⟩
  rw [mixedCoordinates_apply, coefficients_monomial]
  by_cases hα : z.val.1 = α <;> by_cases hi : z.val.2 = i <;>
    simp [Finsupp.single_apply, Prod.ext_iff, hα, hi]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def gradedSymbolPolynomial :
    F.PolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  (ofSupportedCoordinates (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}).comp
      (F.polynomialSymbolBasis b ω hlayers w).repr.toLinearMap

@[simp] theorem gradedSymbolPolynomial_coefficient (x : F.PolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    (F.associatedGradedBasis b ω hlayers).repr
      (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) z.val.1) z.val.2 =
      (F.polynomialSymbolBasis b ω hlayers w).repr x z := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize (F.polynomialSymbolBasis b ω hlayers w).repr x = c
  have h := ofSupportedCoordinates_apply (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    c z
  convert h using 2 <;> rfl

theorem gradedSymbolPolynomial_coefficient_of_ne (x : F.PolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    (F.associatedGradedBasis b ω hlayers).repr
      (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α) i = 0 := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize (F.polynomialSymbolBasis b ω hlayers w).repr x = c
  have hh := ofSupportedCoordinates_apply_of_not_mem (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    c α i h
  convert hh using 2

@[simp] theorem gradedSymbolPolynomial_basis (z : SymbolBasisIndex w ω) :
    F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w z) =
      monomial z.val.1 (F.associatedGradedBasis b ω hlayers z.val.2) := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [Basis.repr_self]
  have h := ofSupportedCoordinates_single (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2} z (1 : ℚ)
  simp only [one_smul] at h
  exact h

theorem gradedSymbolPolynomial_injective :
    Function.Injective (F.gradedSymbolPolynomial b ω hlayers w) := by
  intro x y hxy
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [← F.gradedSymbolPolynomial_coefficient, ← F.gradedSymbolPolynomial_coefficient, hxy]

theorem gradedSymbolPolynomial_lie_basis (u v : SymbolBasisIndex w ω) :
    F.gradedSymbolPolynomial b ω hlayers w
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ =
      ⁅F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w u),
        F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w v)⁆ := by
  classical
  rw [F.gradedSymbolPolynomial_basis, F.gradedSymbolPolynomial_basis, lie_monomial]
  apply coefficients.injective
  ext α
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [coefficients_monomial]
  by_cases hα : u.val.1 + v.val.1 = α
  · subst α
    rw [Finsupp.single_eq_same]
    rw [F.associatedGradedBasis_bracket]
    by_cases hd : Finsupp.weight w (u.val.1 + v.val.1) = ω i
    · have hgrade : ω u.val.2 + ω v.val.2 = ω i := by
        simpa only [map_add, u.property, v.property] using hd
      rw [ite_eq_left hgrade]
      have hc := F.gradedSymbolPolynomial_coefficient b ω hlayers w
        ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆
        ⟨(u.val.1 + v.val.1, i), hd⟩
      exact hc.trans (by rw [F.polynomialSymbolBasis_bracket, ite_eq_left rfl])
    · have hgrade : ω u.val.2 + ω v.val.2 ≠ ω i := by
        simpa only [map_add, u.property, v.property] using hd
      rw [ite_eq_right hgrade]
      exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ _ _ hd
  · rw [Finsupp.single_eq_of_ne (Ne.symm hα), map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w α = ω i
    · have hc := F.gradedSymbolPolynomial_coefficient b ω hlayers w
        ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆
        ⟨(α, i), hd⟩
      exact hc.trans (by rw [F.polynomialSymbolBasis_bracket, ite_eq_right hα])
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ _ _ hd

noncomputable def gradedSymbolPolynomialLie :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ F.AssociatedGraded where
  toLinearMap := F.gradedSymbolPolynomial b ω hlayers w
  map_lie' {x y} := by
    change F.gradedSymbolPolynomial b ω hlayers w ⁅x, y⁆ =
      ⁅F.gradedSymbolPolynomial b ω hlayers w x, F.gradedSymbolPolynomial b ω hlayers w y⁆
    apply linear_map_lie_of_basis (F.polynomialSymbolBasis b ω hlayers w)
      (F.gradedSymbolPolynomial b ω hlayers w) ?_ x y
    intro u v
    have h := F.gradedSymbolPolynomial_lie_basis b ω hlayers w u v
    exact h

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realGradedSymbolPolynomial :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.gradedSymbolPolynomialLie b ω hlayers w))

@[simp] theorem realGradedSymbolPolynomial_coefficient_tmul
    (a : ℝ) (x : F.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w (a ⊗ₜ[ℚ] x)) α =
      a ⊗ₜ[ℚ] coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α := by
  simp only [realGradedSymbolPolynomial, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply]
  have he : F.gradedSymbolPolynomialLie b ω hlayers w x = F.gradedSymbolPolynomial b ω hlayers w x := rfl
  rw [he]
  exact coefficients_realificationLieEquiv_tmul a (F.gradedSymbolPolynomial b ω hlayers w x) α

theorem realGradedSymbolPolynomial_coordinate (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [F.realGradedSymbolPolynomial_coefficient_tmul, Basis.baseChange_repr_tmul,
      F.gradedSymbolPolynomial_coefficient, Basis.baseChange_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realGradedSymbolPolynomial_coordinate_of_ne (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) i = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [F.realGradedSymbolPolynomial_coefficient_tmul, Basis.baseChange_repr_tmul,
      F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w x α i h, zero_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

theorem realGradedSymbolPolynomial_injective :
    Function.Injective (F.realGradedSymbolPolynomial b ω hlayers w) := by
  intro x y h
  apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
  ext z
  rw [← F.realGradedSymbolPolynomial_coordinate, ← F.realGradedSymbolPolynomial_coordinate, h]

theorem realGradedSymbolPolynomial_map_coefficient {W : Type*} [AddCommGroup W] [Module ℚ W]
    (f : F.AssociatedGraded →ₗ[ℚ] W) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (VectorPolynomial.realificationLinearEquiv
      (((VectorPolynomial.map f).comp (F.gradedSymbolPolynomial b ω hlayers w)).baseChange ℝ x)) α =
      f.baseChange ℝ (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, coefficients_realificationLinearEquiv_tmul,
      LinearMap.comp_apply, coefficients_map, F.realGradedSymbolPolynomial_coefficient_tmul,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3.NilpotentLieFiltration

end

end OAI
