/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
import OAI.Combinatorics.Progressions.Linear.NativePairSymbolProjection

namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module MvPolynomial PolynomialTranslationLie

theorem polynomial_eq_constant (P : MvPolynomial (Fin 0) ℚ) :
    P = C (P.coeff 0) := by
  ext α
  have hα : α = 0 := Subsingleton.elim _ _
  subst α
  simp

noncomputable def constantCoefficient (s : ℕ) : weightedSubalgebra weight s →ₗ[ℚ] ℚ where
  toFun x := x.val.polynomial.coeff 0
  map_add' x y := by change (x.val.polynomial + y.val.polynomial).coeff 0 = _; simp
  map_smul' r x := by change (r • x.val.polynomial).coeff 0 = _; simp

@[simp] theorem constantCoefficient_apply (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficient s x = x.val.polynomial.coeff 0 := rfl

theorem constantCoefficient_injective (s : ℕ) : Function.Injective (constantCoefficient s) := by
  intro x y hxy
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · exact Subsingleton.elim _ _
  · rw [polynomial_eq_constant x.val.polynomial, polynomial_eq_constant y.val.polynomial]
    exact congrArg C hxy

theorem constantCoefficient_eq_zero_iff (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficient s x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact constantCoefficient_injective s (hx.trans (map_zero (constantCoefficient s)).symm)
  · rintro rfl
    exact map_zero _

theorem lie_eq_zero (s : ℕ) (x y : weightedSubalgebra weight s) : ⁅x, y⁆ = 0 := by
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · rfl
  · change scalarDirectionalDerivative x.val.base y.val.polynomial -
      scalarDirectionalDerivative y.val.base x.val.polynomial = 0
    simp [scalarDirectionalDerivative_apply]

theorem constantCoefficient_lie (s : ℕ) (x y : weightedSubalgebra weight s) :
    constantCoefficient s ⁅x, y⁆ = 0 := by
  rw [lie_eq_zero, map_zero]

section ScalarLieHom

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def constantCoefficientLie (s : ℕ) : weightedSubalgebra weight s →ₗ⁅ℚ⁆ ℚ where
  toLinearMap := constantCoefficient s
  map_lie' {x y} := by
    change constantCoefficient s ⁅x, y⁆ = ⁅constantCoefficient s x, constantCoefficient s y⁆
    rw [constantCoefficient_lie]
    simp only [LieRing.of_associative_ring_bracket, mul_comm, sub_self]

@[simp] theorem constantCoefficientLie_apply (s : ℕ) (x : weightedSubalgebra weight s) :
    constantCoefficientLie s x = constantCoefficient s x := rfl

end ScalarLieHom

theorem mem_top (s : ℕ) (x : weightedSubalgebra weight s) :
    x ∈ (weightedFiltration weight s (weight_le s)).layer s := by
  change (∀ i, weight i < s → x.val.base i = 0) ∧
    x.val.polynomial ∈ weightedSupportDrop weight s s
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  intro α _
  have hα : α = 0 := Subsingleton.elim _ _
  change Finsupp.weight weight α + s ≤ s
  simp only [hα, map_zero, zero_add, le_refl]

theorem top_layer_eq_top (s : ℕ) : (nilmanifold s).filtration.layer s = ⊤ := by
  apply top_unique
  intro x _
  exact mem_top s x

@[simp] theorem constantCoefficient_centralRationalElement (s : ℕ) (hs : 0 < s) (q : ℚ) :
    constantCoefficient s (centralRationalElement weight s hs q) = q := by
  change (C q : MvPolynomial (Fin 0) ℚ).coeff 0 = q
  simp

theorem eq_constantCoefficient_smul_central (s : ℕ) (hs : 0 < s)
    (x : weightedSubalgebra weight s) :
    x = constantCoefficient s x • centralRationalElement weight s hs 1 := by
  apply constantCoefficient_injective s
  rw [map_smul, constantCoefficient_centralRationalElement, smul_eq_mul, mul_one]

theorem frequency_eq_constantCoefficient (s : ℕ) (hs : 0 < s)
    (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
    (hη : η (centralRationalElement weight s hs 1) = 1) :
    η = constantCoefficient s := by
  ext x
  conv_lhs => rw [eq_constantCoefficient_smul_central s hs x]
  rw [map_smul, hη, smul_eq_mul, mul_one]

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem projection_filtered (F : NilpotentLieFiltration L s)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) :
    ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration weight s (weight_le s)).layer j := by
  intro j x hx
  by_cases hj : j ≤ s
  · exact (weightedFiltration weight s (weight_le s)).antitone hj (mem_top s (φ x))
  · have hz : x ∈ F.layer (s + 1) := F.antitone (by omega) hx
    rw [F.terminal] at hz
    have hx0 : x = 0 := hz
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

noncomputable def gradedProjection (F : NilpotentLieFiltration L s)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
  F.homogeneousGradedProjection (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered F φ)

theorem gradedProjection_image_eq_bot
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF ((constantCoefficient s).comp φ.toLinearMap) x = 0) :
    W.map (gradedProjection F φ) = ⊥ := by
  apply bot_unique
  intro y hy
  change y = 0
  apply (constantCoefficient_eq_zero_iff s y).mp
  exact F.homogeneousGradedProjection_top_frequency_zero
    (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered F φ)
    b ω hF W hW (constantCoefficient s) hη hy (mem_top s y)

theorem gradedProjection_eq_zero
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hη : ∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF ((constantCoefficient s).comp φ.toLinearMap) x = 0)
    (x : F.AssociatedGraded) (hx : x ∈ W) : gradedProjection F φ x = 0 := by
  have hm : gradedProjection F φ x ∈ W.map (gradedProjection F φ) := ⟨x, hx, rfl⟩
  rw [gradedProjection_image_eq_bot F b ω hF φ W hW hη] at hm
  exact (LieSubalgebra.mem_bot _).mp hm

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

noncomputable def projectedScalarFunctional
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  (constantCoefficient s).comp (gradedProjection F φ).toLinearMap

theorem projectedScalarFunctional_lie
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (x y : F.AssociatedGraded) :
    projectedScalarFunctional F φ ⁅x, y⁆ = 0 := by
  change constantCoefficient s (gradedProjection F φ ⁅x, y⁆) = 0
  rw [(gradedProjection F φ).map_lie, constantCoefficient_lie]

theorem controlledFactorization_approximation [Fintype ι]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (hs : 0 < s)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) ≤ p)
    (hfactor : F.ControlledSymbolFactorization b ω hF
      ((constantCoefficient s).comp φ.toLinearMap) T X p) :
    PolynomialRationalApproximation T (Real.exp ((p + 3) ^ 3))
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) (projectedScalarFunctional F φ) X) := by
  obtain ⟨m, E, P, Q, W, v, hm, hmp, hprod, hE, hQ, _, hW, _, hη, hP⟩ := hfactor
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hθH : ∀ i, RationalHeightLE
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) H :=
    fun i => rationalHeightLE_ceil_exp (hθ i)
  have hc : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hcube : 0 ≤ p ^ 3 := by positivity
  have hden : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
    calc
      _ ≤ (Real.exp (p + 1)) ^ Fintype.card ι * Real.exp p := by
        push_cast
        gcongr
      _ = Real.exp ((Fintype.card ι : ℝ) * (p + 1) + p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hn := mul_le_mul_of_nonneg_right hdim (show 0 ≤ p + 1 by linarith)
        nlinarith [sq_nonneg p]
  have hslow : (Fintype.card ι : ℝ) * H * Real.exp p ≤ Real.exp ((p + 3) ^ 3) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  apply F.scalarSymbolPolynomial_approximation_of_factorization b ω hF (fun _ : σ => 1)
    (projectedScalarFunctional F φ) (projectedScalarFunctional_lie F φ) hs T hT
    (Real.exp ((p + 3) ^ 3)) (Real.exp p) (Real.exp_nonneg p) hm hθH hden hslow
    E P Q X hprod hE hQ W _ hP
  intro x hx
  change constantCoefficient s (gradedProjection F φ x) = 0
  rw [gradedProjection_eq_zero F b ω hF φ W hW hη x hx, map_zero]

theorem controlledFactorization_approximation_of_normalized_frequency [Fintype ι]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra weight s) (hs : 0 < s)
    (η : weightedSubalgebra weight s →ₗ[ℚ] ℚ)
    (hη : η (centralRationalElement weight s hs 1) = 1)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ)
    (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hθ : ∀ i, rationalLogHeight
      (projectedScalarFunctional F φ (F.associatedGradedBasis b ω hF i)) ≤ p)
    (hfactor : F.ControlledSymbolFactorization b ω hF (η.comp φ.toLinearMap) T X p) :
    PolynomialRationalApproximation T (Real.exp ((p + 3) ^ 3))
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) (projectedScalarFunctional F φ) X) := by
  rw [frequency_eq_constantCoefficient s hs η hη] at hfactor
  exact controlledFactorization_approximation F b ω hF φ hs T hT X p hp hdim hθ hfactor

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module MvPolynomial PolynomialTranslationLie VectorPolynomial
open scoped TensorProduct

def constantBasisIndex (s : ℕ) (hs : 0 < s) : WeightedBasisIndex weight s :=
  Sum.inr ⟨0, by change Finsupp.weight weight 0 < s; simpa only [map_zero] using hs⟩

theorem constantBasisIndex_unique (s : ℕ) (hs : 0 < s)
    (i : WeightedBasisIndex weight s) : i = constantBasisIndex s hs := by
  cases i with
  | inl i => exact Fin.elim0 i
  | inr a =>
    apply congrArg Sum.inr
    exact Subtype.ext (Subsingleton.elim _ _)

@[simp] theorem constantBasisIndex_grade (s : ℕ) (hs : 0 < s) :
    weightedBasisGrade weight s (constantBasisIndex s hs) = s := by
  simp only [constantBasisIndex, weightedBasisGrade_inr, map_zero, Nat.sub_zero]

theorem constantCoefficient_eq_basis_coord (s : ℕ) (hs : 0 < s) :
    constantCoefficient s = (weightedBasis weight s weight_pos).coord (constantBasisIndex s hs) :=
  rfl

theorem constantCoefficient_eq_basis_repr (s : ℕ) (hs : 0 < s)
    (x : weightedSubalgebra weight s) :
    constantCoefficient s x =
      (weightedBasis weight s weight_pos).repr x (constantBasisIndex s hs) := rfl

theorem realify_constantCoefficient_eq_basis_coord (s : ℕ) (hs : 0 < s) :
    realifyFunctional (constantCoefficient s) =
      ((weightedBasis weight s weight_pos).baseChange ℝ).coord (constantBasisIndex s hs) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, Basis.coord_apply, Basis.baseChange_repr_tmul]
    rw [constantCoefficient_eq_basis_repr s hs]
    simp [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realify_constantCoefficient_eq_basis_repr (s : ℕ) (hs : 0 < s)
    (x : ℝ ⊗[ℚ] weightedSubalgebra weight s) :
    realifyFunctional (constantCoefficient s) x =
      ((weightedBasis weight s weight_pos).baseChange ℝ).repr x (constantBasisIndex s hs) := by
  rw [realify_constantCoefficient_eq_basis_coord s hs]
  rfl

theorem constantCoefficient_coordinate_ofCoordinates {U : Type*}
    (s : ℕ) (hs : 0 < s) [Fintype (WeightedBasisIndex weight s)]
    (P : WeightedBasisIndex weight s → MvPolynomial U ℝ) :
    coordinate (realifyFunctional (constantCoefficient s)).toAddMonoidHom
        (ofCoordinates (R := ℚ) ((weightedBasis weight s weight_pos).baseChange ℝ) P) =
      P (constantBasisIndex s hs) := by
  rw [realify_constantCoefficient_eq_basis_coord s hs, coordinate_ofCoordinates]

end Erdos3.OrdinaryPolynomialPhase

end

section

namespace Erdos3.OrdinaryPolynomialPhase

open Module PolynomialTranslationLie RationalFilteredNilmanifold

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {e : ℕ}

noncomputable def pairScalarFunctional (s : ℕ)
    (D : RationalFilteredNilmanifold L s e) :
    (pi (pairModels (nilmanifold s) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  (constantCoefficient s).comp
    (gradedProjection (pi (pairModels (nilmanifold s) D)).filtration
      (liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true)).toLinearMap

theorem pairScalarFunctional_basis_logHeight
    (s : ℕ) (hs : 0 < s) (D : RationalFilteredNilmanifold L s e)
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra weight s) L))
    (ω : ι → ℕ)
    (hF : ∀ j, (pi (pairModels (nilmanifold s) D)).filtration.layer j =
      Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (nilmanifold s) D)).basis.repr (b i) j) ≤ p) (i : ι) :
    rationalLogHeight (pairScalarFunctional s D
      ((pi (pairModels (nilmanifold s) D)).filtration.associatedGradedBasis b ω hF i)) ≤ p := by
  let := weightedBasisIndex_finite weight s weight_pos
  let : Fintype (WeightedBasisIndex weight s) := Fintype.ofFinite _
  let a : {a : Fin 0 →₀ ℕ | Finsupp.weight weight a < s} :=
    ⟨0, by change Finsupp.weight weight 0 < s; simpa only [map_zero] using hs⟩
  let N := (pi (pairModels (nilmanifold s) D)).filtration
  let φ : PairAlgebra (weightedSubalgebra weight s) L →ₗ⁅ℚ⁆ weightedSubalgebra weight s :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra weight s) L) true
  change rationalLogHeight ((weightedBasis weight s weight_pos).repr
    (N.homogeneousGradedProjection (weightedFiltration weight s (weight_le s))
      (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
      (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
      (weightedBasis_homogeneous_brackets weight s weight_pos) φ
      (projection_filtered N φ) (N.associatedGradedBasis b ω hF i)) (Sum.inr a)) ≤ p
  rw [N.homogeneousGradedProjection_basis_repr (weightedFiltration weight s (weight_le s))
    (weightedBasis weight s weight_pos) (weightedBasisGrade weight s)
    (weightedFiltration_layer_eq_span weight s weight_pos (weight_le s))
    (weightedBasis_homogeneous_brackets weight s weight_pos) φ (projection_filtered N φ)
    b ω hF i (Sum.inr a)]
  split_ifs
  · exact pairTranslationProjection_coordinate_logHeight weight s weight_pos
      (weight_le s) D (b i) (hb i) (Sum.inr a)
  · simpa [rationalLogHeight] using hp

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
