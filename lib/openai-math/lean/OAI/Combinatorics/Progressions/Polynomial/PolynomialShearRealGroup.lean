/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.PolynomialShearBCHOver

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem weightedSupportDrop_map (f : R →+* S) {P : MvPolynomial σ R} {n r : ℕ}
    (hP : P ∈ weightedSupportDrop w n r) : map f P ∈ weightedSupportDrop w n r := by
  intro a ha
  exact hP (MvPolynomial.support_map_subset f P ha)

noncomputable def polynomialShearMap (f : R →+* S) (D : PolynomialShearLieAlgebra w R) :
    PolynomialShearLieAlgebra w S :=
  ⟨MvPolynomial.mkDerivation S (fun i => map f (D.val (X i))), fun i => by
    rw [MvPolynomial.mkDerivation_X]
    exact weightedSupportDrop_map f (D.property i)⟩

theorem polynomialShearMap_X (f : R →+* S) (D : PolynomialShearLieAlgebra w R) (i : σ) :
    (polynomialShearMap f D).val (X i) = map f (D.val (X i)) :=
  MvPolynomial.mkDerivation_X _ _ _

theorem polynomialShearMap_apply_map (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) :
    (polynomialShearMap f D).val (map f P) = map f (D.val P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [map_C, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, Derivation.leibniz, smul_eq_mul, map_add,
      polynomialShearMap_X, hP]

theorem polynomialShearMap_add (f : R →+* S) (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (D + E) = polynomialShearMap f D + polynomialShearMap f E := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (D.val (X i) + E.val (X i)) =
    (polynomialShearMap f D).val (X i) + (polynomialShearMap f E).val (X i)
  rw [map_add, polynomialShearMap_X, polynomialShearMap_X]

theorem polynomialShearMap_smul (f : R →+* S) (c : R) (D : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (c • D) = f c • polynomialShearMap f D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (c • D.val (X i)) = f c • (polynomialShearMap f D).val (X i)
  rw [polynomialShearMap_X, ← MvPolynomial.C_mul', ← MvPolynomial.C_mul', map_mul, map_C]

theorem polynomialShearMap_lie (f : R →+* S) (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearMap f ⁅D, E⁆ = ⁅polynomialShearMap f D, polynomialShearMap f E⁆ := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X]
  change map f (D.val (E.val (X i)) - E.val (D.val (X i))) =
    (polynomialShearMap f D).val ((polynomialShearMap f E).val (X i)) -
      (polynomialShearMap f E).val ((polynomialShearMap f D).val (X i))
  rw [map_sub, polynomialShearMap_X, polynomialShearMap_X,
    polynomialShearMap_apply_map, polynomialShearMap_apply_map]

theorem polynomialShearMap_monomial (f : R →+* S) (a : PolynomialShearIndex w) :
    polynomialShearMap f (polynomialShearMonomial w a) = polynomialShearMonomial w a := by
  classical
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMap_X, polynomialShearMonomial_X, polynomialShearMonomial_X]
  split_ifs <;> simp

theorem polynomialShearMap_basis [Fintype σ] (f : R →+* S) (a : PolynomialShearIndex w) :
    polynomialShearMap f (polynomialShearBasis (R := R) w a) =
      polynomialShearBasis (R := S) w a := by
  rw [polynomialShearBasis_eq_monomial, polynomialShearBasis_eq_monomial,
    polynomialShearMap_monomial]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {R S T I : Type*} [CommRing R] [CommRing S] [CommRing T] {w : I → ℕ}

theorem polynomialShearMap_zero (f : R →+* S) :
    polynomialShearMap (w := w) f 0 = 0 := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  simp only [polynomialShearMap_X]
  exact map_zero _

theorem polynomialShearMap_sum {κ : Type*} (f : R →+* S)
    (t : Finset κ) (D : κ → PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (∑ k ∈ t, D k) = ∑ k ∈ t, polynomialShearMap f (D k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, polynomialShearMap_zero]
  | @insert k t hk ih =>
    simp only [Finset.sum_insert hk, polynomialShearMap_add, ih]

theorem polynomialShearMap_comp (f : R →+* S) (g : S →+* T)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearMap g (polynomialShearMap f D) = polynomialShearMap (g.comp f) D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  simp only [polynomialShearMap_X, MvPolynomial.map_map]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {σ : Type*} (w : σ → ℕ)

noncomputable def polynomialShearRationalRealMap :
    PolynomialShearLieAlgebra w ℚ →ₗ[ℚ] PolynomialShearLieAlgebra w ℝ where
  toFun := polynomialShearMap (algebraMap ℚ ℝ)
  map_add' := polynomialShearMap_add _
  map_smul' c D := by
    rw [polynomialShearMap_smul]
    exact IsScalarTower.algebraMap_smul ℝ c _

noncomputable def polynomialShearRealificationMap :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ[ℝ] PolynomialShearLieAlgebra w ℝ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℝ _ (polynomialShearRationalRealMap w))

theorem polynomialShearRealificationMap_tmul (r : ℝ) (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearRealificationMap w (r ⊗ₜ[ℚ] D) =
      r • polynomialShearMap (algebraMap ℚ ℝ) D := rfl

noncomputable def polynomialShearRealificationHom :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ⁅ℝ⁆ PolynomialShearLieAlgebra w ℝ where
  toLinearMap := polynomialShearRealificationMap w
  map_lie' := by
    intro x y
    change polynomialShearRealificationMap w ⁅x, y⁆ =
      ⁅polynomialShearRealificationMap w x, polynomialShearRealificationMap w y⁆
    induction x using TensorProduct.inductionOn with
    | tmul r D =>
      induction y using TensorProduct.inductionOn with
      | tmul t E =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, polynomialShearRealificationMap_tmul,
          polynomialShearMap_lie, smul_lie, lie_smul, smul_smul, mul_comm]
      | add y z hy hz => simp only [LieRing.lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [LieRing.add_lie, map_add, hx, hz]

variable [Fintype σ]

theorem polynomialShearRealificationHom_basis (a : PolynomialShearIndex w) :
    polynomialShearRealificationHom w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) =
      polynomialShearBasis (R := ℝ) w a := by
  change polynomialShearRealificationMap w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) = _
  rw [Basis.baseChange_apply, polynomialShearRealificationMap_tmul, polynomialShearMap_basis, one_smul]

noncomputable def polynomialShearRealificationLinearEquiv :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) ≃ₗ[ℝ] PolynomialShearLieAlgebra w ℝ :=
  ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr.trans
    (polynomialShearBasis (R := ℝ) w).repr.symm

theorem polynomialShearRealificationMap_eq :
    (polynomialShearRealificationHom w).toLinearMap =
      (polynomialShearRealificationLinearEquiv w).toLinearMap := by
  apply ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).ext
  intro a
  change polynomialShearRealificationHom w ((polynomialShearBasis (R := ℚ) w).baseChange ℝ a) = _
  rw [polynomialShearRealificationHom_basis]
  change polynomialShearBasis (R := ℝ) w a =
    (polynomialShearBasis (R := ℝ) w).repr.symm
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ) a))
  apply (polynomialShearBasis (R := ℝ) w).repr.injective
  rw [LinearEquiv.apply_symm_apply, Basis.repr_self, Basis.repr_self]

noncomputable def polynomialShearRealificationEquiv :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) ≃ₗ⁅ℝ⁆ PolynomialShearLieAlgebra w ℝ :=
  LieEquiv.ofBijective (polynomialShearRealificationHom w) (by
    change Function.Bijective (polynomialShearRealificationHom w).toLinearMap
    rw [polynomialShearRealificationMap_eq]
    exact (polynomialShearRealificationLinearEquiv w).bijective)

theorem polynomialShearRealificationEquiv_tmul (r : ℝ) (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearRealificationEquiv w (r ⊗ₜ[ℚ] D) =
      r • polynomialShearMap (algebraMap ℚ ℝ) D := rfl

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem weightedSupportLE_map (f : R →+* S) {P : MvPolynomial σ R} {n : ℕ}
    (hP : P ∈ weightedSupportLE w n) : map f P ∈ weightedSupportLE w n := by
  intro a ha
  exact hP (MvPolynomial.support_map_subset f P ha)

theorem polynomialShearMap_pow_apply (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (k : ℕ) (P : MvPolynomial σ R) :
    ((polynomialShearMap f D).val.toLinearMap ^ k) (map f P) =
      map f ((D.val.toLinearMap ^ k) P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact polynomialShearMap_apply_map f D _

variable [Algebra ℚ R] [Algebra ℚ S]

theorem polynomialShearExp_map (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) :
    map f (polynomialShearExp D P) = polynomialShearExp (polynomialShearMap f D) (map f P) := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExp_eq_sum D hp,
    polynomialShearExp_eq_sum (polynomialShearMap f D) (weightedSupportLE_map f hp), map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, polynomialShearMap_pow_apply]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

noncomputable def polynomialShearRealificationRatHom :
    (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) →ₗ⁅ℚ⁆ PolynomialShearLieAlgebra w ℝ where
  toLinearMap := (polynomialShearRealificationEquiv w).toLinearEquiv.toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro D E
    exact (polynomialShearRealificationEquiv w).map_lie D E

noncomputable def polynomialShearRealGroupEquiv (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Group ≃*
      (polynomialShearRatFiltration (R := ℝ) w s hw).Group where
  toFun g := ⟨polynomialShearRealificationEquiv w g.coord⟩
  invFun g := ⟨(polynomialShearRealificationEquiv w).symm g.coord⟩
  left_inv g := NilpotentLieBCHGroup.ext ((polynomialShearRealificationEquiv w).symm_apply_apply g.coord)
  right_inv g := NilpotentLieBCHGroup.ext ((polynomialShearRealificationEquiv w).apply_symm_apply g.coord)
  map_mul' g h :=
    NilpotentLieBCHGroup.ext (map_lieBCH (polynomialShearRealificationRatHom w) s g.coord h.coord)

noncomputable def polynomialShearRealAutEquiv (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Group ≃* WeightedLoweringAut w ℝ :=
  (polynomialShearRealGroupEquiv w s hw).trans (polynomialShearBCHEquivOver w s hw)

theorem polynomialShearRealAutEquiv_apply (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) :
    polynomialShearRealAutEquiv w s hw g =
      polynomialShearExpAut (polynomialShearRealificationEquiv w g.coord) := rfl

theorem polynomialShearRealAutEquiv_rational (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).Group) (P : MvPolynomial σ ℚ) :
    (polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val
        (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      MvPolynomial.map (algebraMap ℚ ℝ) ((polynomialShearBCHEquiv w s hw g).val P) := by
  change polynomialShearExp (polynomialShearRealificationEquiv w ((1 : ℝ) ⊗ₜ[ℚ] g.coord))
      (MvPolynomial.map (algebraMap ℚ ℝ) P) =
    MvPolynomial.map (algebraMap ℚ ℝ) (polynomialShearExp g.coord P)
  rw [polynomialShearRealificationEquiv_tmul, one_smul]
  exact (polynomialShearExp_map (algebraMap ℚ ℝ) g.coord P).symm

end Erdos3

end

end OAI
