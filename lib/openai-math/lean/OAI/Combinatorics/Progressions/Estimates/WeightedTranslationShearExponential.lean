/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_direction_add (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (x + z) P =
      scalarDirectionalDerivative x P + scalarDirectionalDerivative z P := by
  simp only [scalarDirectionalDerivative_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem scalarDirectionalDerivative_direction_smul (r : ℚ) (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (r • x) P = r • scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

theorem scalarDirectionalDerivative_direction_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

theorem scalarDirectionalDerivative_commute (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative x (scalarDirectionalDerivative z P) =
      scalarDirectionalDerivative z (scalarDirectionalDerivative x P) := by
  have h : ⁅scalarDirectionalDerivative x, scalarDirectionalDerivative z⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, scalarDirectionalDerivative_X,
      scalarDirectionalDerivative_C, sub_self, Derivation.zero_apply]
  have hh := congrArg (fun D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) => D P) h
  exact sub_eq_zero.mp hh

@[ext] structure PolynomialTranslationLie (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationLie

noncomputable def toProd : PolynomialTranslationLie σ ≃ (σ → ℚ) × MvPolynomial σ ℚ where
  toFun x := (x.base, x.polynomial)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (PolynomialTranslationLie σ) := toProd.addCommGroup
noncomputable instance : Module ℚ (PolynomialTranslationLie σ) :=
  { toProd with map_add' _ _ := rfl : PolynomialTranslationLie σ ≃+ (σ → ℚ) × MvPolynomial σ ℚ }.module ℚ

noncomputable def toProdl : PolynomialTranslationLie σ ≃ₗ[ℚ] (σ → ℚ) × MvPolynomial σ ℚ :=
  { toProd with map_add' _ _ := rfl, map_smul' _ _ := rfl }

omit [Fintype σ] in
@[simp] theorem base_zero : (0 : PolynomialTranslationLie σ).base = 0 := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_zero : (0 : PolynomialTranslationLie σ).polynomial = 0 := rfl
omit [Fintype σ] in
@[simp] theorem base_add (x y : PolynomialTranslationLie σ) : (x+y).base = x.base+y.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_add (x y : PolynomialTranslationLie σ) : (x+y).polynomial = x.polynomial+y.polynomial := rfl
omit [Fintype σ] in
@[simp] theorem base_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).base = r • x.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).polynomial = r • x.polynomial := rfl

noncomputable instance : Bracket (PolynomialTranslationLie σ) (PolynomialTranslationLie σ) where
  bracket x y := ⟨0, scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial⟩

@[simp] theorem base_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.base = 0 := rfl
@[simp] theorem polynomial_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.polynomial =
    scalarDirectionalDerivative x.base y.polynomial - scalarDirectionalDerivative y.base x.polynomial := rfl

noncomputable instance : LieRing (PolynomialTranslationLie σ) where
  add_lie x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_add x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_self x := by ext <;> simp
  leibniz_lie x y z := by
    ext
    · simp
    · simp only [polynomial_lie, base_lie, polynomial_add, map_sub,
        scalarDirectionalDerivative_direction_zero, sub_zero, zero_sub]
      rw [scalarDirectionalDerivative_commute x.base y.base,
        scalarDirectionalDerivative_commute x.base z.base,
        scalarDirectionalDerivative_commute y.base z.base]
      abel_nf

noncomputable instance : LieAlgebra ℚ (PolynomialTranslationLie σ) where
  lie_smul r x y := by
    ext <;> simp [scalarDirectionalDerivative_direction_smul, smul_sub]

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_weight_drop (w : σ → ℕ) (x : σ → ℚ) (k : ℕ)
    (hx : ∀ i, w i < k → x i = 0) {n r : ℕ} {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportDrop w n r) :
    scalarDirectionalDerivative x P ∈ weightedSupportDrop w n (r + k) := by
  apply weightedDerivation_apply w (scalarDirectionalDerivative x) k _ hP
  intro i
  rw [scalarDirectionalDerivative_X]
  by_cases hi : k ≤ w i
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa using hi))
  · rw [hx i (by omega), map_zero]
    exact Submodule.zero_mem _

namespace PolynomialTranslationLie

noncomputable def weightedLayer (w : σ → ℕ) (d k : ℕ) : Submodule ℚ (PolynomialTranslationLie σ) where
  carrier := {x | (∀ i, w i < k → x.base i = 0) ∧
    x.polynomial ∈ weightedSupportDrop w d k}
  zero_mem' := ⟨by simp, Submodule.zero_mem _⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
      Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨fun i hi => by simp [hx.1 i hi], Submodule.smul_mem _ r hx.2⟩

omit [Fintype σ] in
theorem mem_weightedLayer (w : σ → ℕ) (d k : ℕ) (x : PolynomialTranslationLie σ) :
    x ∈ weightedLayer w d k ↔ (∀ i, w i < k → x.base i = 0) ∧
      x.polynomial ∈ weightedSupportDrop w d k := Iff.rfl

omit [Fintype σ] in
theorem weightedLayer_antitone (w : σ → ℕ) (d : ℕ) : Antitone (weightedLayer w d) := by
  intro i j hij x hx
  exact ⟨fun a ha => hx.1 a (ha.trans_le hij), weightedSupportDrop_antitone hij hx.2⟩

theorem weightedLayer_lie_mem (w : σ → ℕ) (d : ℕ) {i j : ℕ}
    {x y : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d i)
    (hy : y ∈ weightedLayer w d j) : ⁅x,y⁆ ∈ weightedLayer w d (i+j) := by
  refine ⟨by simp, ?_⟩
  change scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial ∈ _
  apply Submodule.sub_mem
  · simpa only [Nat.add_comm j i] using scalarDirectionalDerivative_weight_drop w x.base i hx.1 hy.2
  · exact scalarDirectionalDerivative_weight_drop w y.base j hy.1 hx.2

omit [Fintype σ] in
theorem weightedLayer_terminal (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    weightedLayer w d (d+1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply PolynomialTranslationLie.ext
  · funext i
    exact hx.1 i (Nat.lt_succ_of_le (hw i))
  · exact weightedSupportDrop_eq_zero (Nat.lt_succ_self d) hx.2

noncomputable def weightedSubalgebra (w : σ → ℕ) (d : ℕ) : LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { weightedLayer w d 1 with
    lie_mem' := fun hx hy => weightedLayer_antitone w d (by omega : 1 ≤ 1+1)
      (weightedLayer_lie_mem w d hx hy) }

@[simp] theorem mem_weightedSubalgebra (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    x ∈ weightedSubalgebra w d ↔ x ∈ weightedLayer w d 1 := Iff.rfl

noncomputable def weightedFiltration (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    NilpotentLieFiltration (weightedSubalgebra w d) d where
  layer k := (weightedLayer w d k).comap (weightedSubalgebra w d).subtype
  antitone := fun i j hij x hx => weightedLayer_antitone w d hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => weightedLayer_lie_mem w d hx hy
  terminal := by
    rw [weightedLayer_terminal w d hw]
    exact LinearMap.ker_eq_bot.mpr (weightedSubalgebra w d).subtype_injective

noncomputable def weightedCoordinates (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ[ℚ] (σ → ℚ) × weightedSupportLE (R := ℚ) w d where
  toFun x := (x.val.base, ⟨x.val.polynomial, weightedSupportDrop_le x.property.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weightedCoordinates_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (weightedCoordinates w d) := by
  intro x y h
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · exact congrArg Prod.fst h
  · exact congrArg (fun z => (z.2 : MvPolynomial σ ℚ)) h

theorem weightedSubalgebra_finite (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Module.Finite ℚ (weightedSubalgebra w d) := by
  let := weightedSupportLE_moduleFinite (R := ℚ) w hw d
  exact Module.Finite.of_injective (weightedCoordinates w d) (weightedCoordinates_injective w d)

theorem weightedSubalgebra_finrank_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Module.finrank ℚ (weightedSubalgebra w d) ≤
      Fintype.card σ + (Fintype.card σ + 1)^d := by
  let := weightedSupportLE_moduleFinite (R := ℚ) w hw d
  have h := LinearMap.finrank_le_finrank_of_injective (weightedCoordinates_injective w d)
  calc
    Module.finrank ℚ (weightedSubalgebra w d) ≤
      Module.finrank ℚ ((σ → ℚ) × weightedSupportLE (R := ℚ) w d) := h
    _ = Fintype.card σ + Module.finrank ℚ (weightedSupportLE (R := ℚ) w d) := by
      rw [Module.finrank_prod, Module.finrank_pi_fintype]
      simp
    _ ≤ _ := Nat.add_le_add_left (weightedSupportLE_finrank_le w hw d) _

theorem weightedSubalgebra_nilpotent (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    LieRing.IsNilpotent (weightedSubalgebra w d) :=
  LieModule.IsNilpotent.mk (weightedSubalgebra w d) (weightedFiltration w d hw).lowerCentralSeries_eq_bot

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ : Type*} [Fintype σ]

def shearWeight (w : σ → ℕ) (d : ℕ) : σ ⊕ Unit → ℕ := Sum.elim w (fun _ => d)

noncomputable def shearDerivation (x : PolynomialTranslationLie σ) :
    Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ) (MvPolynomial (σ ⊕ Unit) ℚ) :=
  mkDerivation ℚ (Sum.elim (fun i => C (x.base i)) (fun _ => rename Sum.inl x.polynomial))

omit [Fintype σ] in
@[simp] theorem shearDerivation_X_inl (x : PolynomialTranslationLie σ) (i : σ) :
    shearDerivation x (X (Sum.inl i)) = C (x.base i) := mkDerivation_X _ _ _

omit [Fintype σ] in
@[simp] theorem shearDerivation_X_inr (x : PolynomialTranslationLie σ) (u : Unit) :
    shearDerivation x (X (Sum.inr u)) = rename Sum.inl x.polynomial := mkDerivation_X _ _ _

theorem shearDerivation_rename (x : PolynomialTranslationLie σ) (P : MvPolynomial σ ℚ) :
    shearDerivation x (rename Sum.inl P) =
      rename Sum.inl (scalarDirectionalDerivative x.base P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.derivation_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, rename_X, Derivation.leibniz, smul_eq_mul,
        shearDerivation_X_inl, scalarDirectionalDerivative_X, map_add, rename_C, hP]

noncomputable def shearDerivationHom : PolynomialTranslationLie σ →ₗ⁅ℚ⁆
    Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ) (MvPolynomial (σ ⊕ Unit) ℚ) where
  toFun := shearDerivation
  map_add' x y := by
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Pi.add_apply]
  map_smul' r x := by
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Derivation.smul_apply, Pi.smul_apply, Algebra.smul_def]
  map_lie' := by
    intro x y
    apply MvPolynomial.derivation_ext
    intro i
    cases i <;> simp [Derivation.commutator_apply, MvPolynomial.derivation_C,
      shearDerivation_rename]

theorem shearDerivationHom_injective : Function.Injective (shearDerivationHom (σ := σ)) := by
  intro x y h
  apply PolynomialTranslationLie.ext
  · funext i
    have hh := congrArg (fun D : Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ)
      (MvPolynomial (σ ⊕ Unit) ℚ) => D (X (Sum.inl i))) h
    simpa [shearDerivationHom] using hh
  · apply MvPolynomial.rename_injective Sum.inl Sum.inl_injective
    have hh := congrArg (fun D : Derivation ℚ (MvPolynomial (σ ⊕ Unit) ℚ)
      (MvPolynomial (σ ⊕ Unit) ℚ) => D (X (Sum.inr ()))) h
    simpa [shearDerivationHom] using hh

omit [Fintype σ] in

theorem shearDerivation_mem_drop (w : σ → ℕ) (d k : ℕ)
    {x : PolynomialTranslationLie σ} (hx : x ∈ weightedLayer w d k) :
    shearDerivation x ∈ polynomialDerivationDrop (shearWeight w d) k := by
  intro i
  cases i with
  | inl i =>
      rw [shearDerivation_X_inl]
      by_cases hi : k ≤ w i
      · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simpa [shearWeight] using hi))
      · rw [hx.1 i (by omega), map_zero]
        exact Submodule.zero_mem _
  | inr u =>
      rw [shearDerivation_X_inr]
      exact weightedSupportDrop_rename Sum.inl (fun _ => rfl) hx.2

noncomputable def weightedShearEmbedding (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ⁅ℚ⁆ PolynomialShearLieAlgebra (shearWeight w d) ℚ where
  toFun x := ⟨shearDerivationHom x.val, shearDerivation_mem_drop w d 1 x.property⟩
  map_add' x y := Subtype.ext (shearDerivationHom.map_add x.val y.val)
  map_smul' r x := Subtype.ext (shearDerivationHom.map_smul r x.val)
  map_lie' := by
    intro x y
    exact Subtype.ext (shearDerivationHom.map_lie x.val y.val)

theorem weightedShearEmbedding_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (weightedShearEmbedding w d) := by
  intro x y h
  apply Subtype.ext
  exact shearDerivationHom_injective (congrArg Subtype.val h)

theorem weightedShearEmbedding_filtered (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (k : ℕ) {x : weightedSubalgebra w d}
    (hx : x ∈ (weightedFiltration w d hw).layer k) :
    weightedShearEmbedding w d x ∈ polynomialShearLayer (R := ℚ) (shearWeight w d) k :=
  shearDerivation_mem_drop w d k hx

theorem weightedShearEmbedding_apply_drop (w : σ → ℕ) (d k : ℕ)
    {x : weightedSubalgebra w d} (hx : x.val ∈ weightedLayer w d k)
    {n r : ℕ} {P : MvPolynomial (σ ⊕ Unit) ℚ}
    (hP : P ∈ weightedSupportDrop (shearWeight w d) n r) :
    (weightedShearEmbedding w d x).val P ∈ weightedSupportDrop (shearWeight w d) n (r+k) :=
  weightedDerivation_apply _ _ k (shearDerivation_mem_drop w d k hx) hP

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem shearWeight_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    ∀ i, shearWeight w d i ≤ d := by
  intro i
  cases i with
  | inl i => exact hw i
  | inr _ => exact le_rfl

noncomputable def weightedShearGroupHom (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    (weightedFiltration w d hw).Group →* WeightedLoweringAut (shearWeight w d) ℚ :=
  (polynomialShearBCHEquiv _ d (shearWeight_le w d hw)).toMonoidHom.comp
    (NilpotentLieBCHGroup.map (weightedShearEmbedding w d))

@[simp] theorem weightedShearGroupHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).Group) :
    weightedShearGroupHom w d hw g = polynomialShearExpAut (weightedShearEmbedding w d g.coord) := rfl

theorem weightedShearGroupHom_injective (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    Function.Injective (weightedShearGroupHom w d hw) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply weightedShearEmbedding_injective w d
  have hh := (polynomialShearBCHEquiv _ d (shearWeight_le w d hw)).injective heq
  exact congrArg NilpotentLieBCHGroup.coord hh

noncomputable def weightedShearRealGroupHom (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) :
    (weightedFiltration w d hw).realification.Group →*
      WeightedLoweringAut (shearWeight w d) ℝ :=
  (polynomialShearRealAutEquiv _ d (shearWeight_le w d hw)).toMonoidHom.comp
    (NilpotentLieBCHGroup.mapReal (realificationLieHom (weightedShearEmbedding w d)))

@[simp] theorem weightedShearRealGroupHom_apply (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).realification.Group) :
    weightedShearRealGroupHom w d hw g = polynomialShearExpAut
      (polynomialShearRealificationEquiv (shearWeight w d)
        (realificationLieHom (weightedShearEmbedding w d) g.coord)) := rfl

theorem weightedShearRealEmbedding_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (realificationLieHom (weightedShearEmbedding w d)) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (weightedShearEmbedding w d).toLinearMap (weightedShearEmbedding_injective w d)

theorem weightedShearRealGroupHom_injective (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    Function.Injective (weightedShearRealGroupHom w d hw) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply weightedShearRealEmbedding_injective w d
  have hh := (polynomialShearRealAutEquiv _ d (shearWeight_le w d hw)).injective heq
  exact congrArg NilpotentLieBCHGroup.coord hh

theorem weightedShearRealGroupHom_rational (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).Group)
    (P : MvPolynomial (σ ⊕ Unit) ℚ) :
    (weightedShearRealGroupHom w d hw (NilpotentLieBCHGroup.realificationHom g)).val
      (MvPolynomial.map (algebraMap ℚ ℝ) P) =
    MvPolynomial.map (algebraMap ℚ ℝ) ((weightedShearGroupHom w d hw g).val P) := by
  exact polynomialShearRealAutEquiv_rational (shearWeight w d) d
    (shearWeight_le w d hw) (NilpotentLieBCHGroup.map (weightedShearEmbedding w d) g) P

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def realShearEmbedding (w : σ → ℕ) (d : ℕ) :
    (ℝ ⊗[ℚ] weightedSubalgebra w d) →ₗ⁅ℝ⁆ PolynomialShearLieAlgebra (shearWeight w d) ℝ :=
  (polynomialShearRealificationEquiv (shearWeight w d)).toLieHom.comp
    (realificationLieHom (weightedShearEmbedding w d))

@[simp] theorem realShearEmbedding_tmul (w : σ → ℕ) (d : ℕ)
    (r : ℝ) (x : weightedSubalgebra w d) :
    realShearEmbedding w d (r ⊗ₜ[ℚ] x) =
      r • polynomialShearMap (algebraMap ℚ ℝ) (weightedShearEmbedding w d x) := rfl

theorem realShearEmbedding_shape (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) :
    ∃ b : σ → ℝ, ∃ P : MvPolynomial σ ℝ,
      (∀ i, (realShearEmbedding w d x).val (X (Sum.inl i)) = C (b i)) ∧
      (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      refine ⟨fun i => r * (x.val.base i : ℝ),
        r • MvPolynomial.map (algebraMap ℚ ℝ) x.val.polynomial, ?_, ?_⟩
      · intro i
        rw [realShearEmbedding_tmul]
        change r • (polynomialShearMap (algebraMap ℚ ℝ)
          (weightedShearEmbedding w d x)).val (X (Sum.inl i)) = _
        rw [polynomialShearMap_X]
        change r • MvPolynomial.map (algebraMap ℚ ℝ)
          (x.val.shearDerivation (X (Sum.inl i))) = _
        rw [shearDerivation_X_inl, map_C]
        simp [Algebra.smul_def]
      · rw [realShearEmbedding_tmul]
        change r • (polynomialShearMap (algebraMap ℚ ℝ)
          (weightedShearEmbedding w d x)).val (X (Sum.inr ())) = _
        rw [polynomialShearMap_X]
        change r • MvPolynomial.map (algebraMap ℚ ℝ)
          (x.val.shearDerivation (X (Sum.inr ()))) = _
        rw [shearDerivation_X_inr]
        simp [MvPolynomial.map_rename]
  | add x y hx hy =>
      obtain ⟨bx, Px, hbx, hPx⟩ := hx
      obtain ⟨by', Py, hby, hPy⟩ := hy
      refine ⟨bx + by', Px + Py, ?_, ?_⟩
      · intro i
        rw [map_add]
        change (realShearEmbedding w d x).val (X (Sum.inl i)) +
          (realShearEmbedding w d y).val (X (Sum.inl i)) = _
        rw [hbx, hby]
        simp
      · rw [map_add]
        change (realShearEmbedding w d x).val (X (Sum.inr ())) +
          (realShearEmbedding w d y).val (X (Sum.inr ())) = _
        rw [hPx, hPy, map_add]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem shearDerivation_pow_X_inr (x : PolynomialTranslationLie σ) (n : ℕ) :
    (x.shearDerivation.toLinearMap ^ (n+1)) (X (Sum.inr ())) =
      rename Sum.inl ((scalarDirectionalDerivative x.base).toLinearMap ^ n $ x.polynomial) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change shearDerivation x (rename Sum.inl _) = _
      rw [shearDerivation_rename, pow_succ', Module.End.mul_apply]
      rfl

omit [Fintype σ] in
theorem shearDerivation_pow_X_inl (x : PolynomialTranslationLie σ) (n : ℕ) (i : σ) :
    (x.shearDerivation.toLinearMap ^ (n+2)) (X (Sum.inl i)) = 0 := by
  induction n with
  | zero =>
      rw [show 0+2=1+1 by omega, pow_succ', Module.End.mul_apply]
      simp [MvPolynomial.derivation_C]
  | succ n ih =>
      rw [show n+1+2=(n+2)+1 by omega, pow_succ', Module.End.mul_apply, ih, map_zero]

theorem weightedShearExp_X_inr (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) (N : ℕ) (hN : d ≤ N) :
    (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inr ())) =
      X (Sum.inr ()) + rename Sum.inl
        (∑ k ∈ Finset.range N, ((k+1).factorial : ℚ)⁻¹ •
          ((scalarDirectionalDerivative x.val.base).toLinearMap ^ k) x.val.polynomial) := by
  rw [polynomialShearExpAut_apply,
    polynomialShearExp_eq_sum _ (weightedSupportLE_mono hN
      (weightedSupportLE_X (shearWeight w d) (Sum.inr ()))), Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul, map_sum, map_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact shearDerivation_pow_X_inr x.val k

theorem weightedShearExp_X_inl (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) (i : σ) :
    (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inl i)) =
      X (Sum.inl i) + C (x.val.base i) := by
  rw [polynomialShearExpAut_apply,
    polynomialShearExp_eq_sum _ (weightedSupportLE_mono (Nat.le_add_right (w i) 2)
      (weightedSupportLE_X (shearWeight w d) (Sum.inl i))),
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∑ k ∈ Finset.range (w i + 1),
      ((k+1+1).factorial : ℚ)⁻¹ •
      ((weightedShearEmbedding w d x).val.toLinearMap ^ (k+1+1)) (X (Sum.inl i)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    change ((k+1+1).factorial : ℚ)⁻¹ •
      (x.val.shearDerivation.toLinearMap ^ (k+2)) (X (Sum.inl i)) = 0
    rw [shearDerivation_pow_X_inl, smul_zero]
  rw [hz]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero,
    pow_one, Module.End.one_apply, one_smul, zero_add]
  change x.val.shearDerivation (X (Sum.inl i)) + X (Sum.inl i) = _
  rw [shearDerivation_X_inl, add_comm]

end Erdos3.PolynomialTranslationLie

end

end OAI
