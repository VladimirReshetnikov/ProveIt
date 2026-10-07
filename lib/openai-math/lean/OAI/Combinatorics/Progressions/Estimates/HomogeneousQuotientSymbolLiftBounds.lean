/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

noncomputable def weightedHomogeneousPart (w : σ → ℕ) (d : ℕ) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V :=
  (MvPolynomial.weightedHomogeneousComponent w d).rTensor V

theorem weightedHomogeneousPart_tmul (w : σ → ℕ) (d : ℕ)
    (P : MvPolynomial σ R) (v : V) :
    weightedHomogeneousPart w d (P ⊗ₜ[R] v) =
      MvPolynomial.weightedHomogeneousComponent w d P ⊗ₜ[R] v := rfl

theorem coefficients_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedHomogeneousPart w d p) α =
      if Finsupp.weight w α = d then coefficients p α else 0 := by
  classical
  induction p using TensorProduct.inductionOn with
  | tmul polynomial vector =>
    rw [weightedHomogeneousPart_tmul, coefficients_tmul,
      MvPolynomial.coeff_weightedHomogeneousComponent, coefficients_tmul]
    split <;> simp_all
  | add first second hfirst hsecond =>
    simp only [map_add, Finsupp.add_apply, hfirst, hsecond]
    split <;> simp

theorem weightedHomogeneousPart_monomial (w : σ → ℕ) (d : ℕ)
    (α : σ →₀ ℕ) (v : V) :
    weightedHomogeneousPart w d (monomial (R := R) α v) =
      if Finsupp.weight w α = d then monomial α v else 0 := by
  classical
  apply coefficients.injective
  ext β
  split <;> rename_i hd
  all_goals rw [coefficients_weightedHomogeneousPart]
  by_cases h : α = β
  · subst β
    simp [hd]
  · simp [Ne.symm h]
  by_cases h : α = β
  · subst β
    simp [hd]
  · simp [Ne.symm h]

theorem weightedHomogeneousPart_homogeneous (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≠ d) :
    coefficients (weightedHomogeneousPart w d p) α = 0 := by
  rw [coefficients_weightedHomogeneousPart, ite_eq_right hα]

theorem weightedHomogeneousPart_eq_self {w : σ → ℕ} {d : ℕ}
    {p : VectorPolynomial σ R V}
    (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0) :
    weightedHomogeneousPart w d p = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_weightedHomogeneousPart]
  split
  · rfl
  · exact (hp α ‹_›).symm

theorem coordinate_weightedHomogeneousPart (f : V →+ S) (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) :
    coordinate f (weightedHomogeneousPart w d p) =
      MvPolynomial.weightedHomogeneousComponent w d (coordinate f p) := by
  classical
  ext α
  simp only [coeff_coordinate, coefficients_weightedHomogeneousPart,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  split <;> simp

theorem map_weightedHomogeneousPart (f : V →ₗ[R] W) (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) :
    map f (weightedHomogeneousPart w d p) = weightedHomogeneousPart w d (map f p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_map, coefficients_weightedHomogeneousPart]
  split <;> simp

theorem eval₂_weightedHomogeneousPart [Algebra R S] [Module S V] [IsScalarTower R S V]
    (w : σ → ℕ) (d : ℕ) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (weightedHomogeneousPart w d p) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedHomogeneousPart_monomial]
  apply Finset.sum_congr rfl
  intro α _
  split <;> simp [eval₂_monomial]

theorem eval_weightedHomogeneousPart (w : σ → ℕ) (d : ℕ) (x : σ → R)
    (p : VectorPolynomial σ R V) :
    eval x (weightedHomogeneousPart w d p) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedHomogeneousPart_monomial]
  apply Finset.sum_congr rfl
  intro α _
  split <;> simp [eval_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

noncomputable def weightedRadialPolynomial (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) : VectorPolynomial Unit ℚ V :=
  ∑ α ∈ (coefficients p).support,
    monomial (Finsupp.single () (Finsupp.weight w α))
      ((α.prod fun i n => x i ^ n) • coefficients p α)

theorem weightedRadialPolynomial_eval (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) (r : ℚ) :
    eval (fun _ : Unit => r) (weightedRadialPolynomial w p x) =
      eval₂ (fun i => (r : ℝ) ^ w i * x i) p := by
  classical
  unfold weightedRadialPolynomial
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, eval₂_monomial]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finsupp.prod_single_index (by simp), weighted_monomial_dilation]
  rw [mul_smul, ← Rat.cast_pow, ← IsScalarTower.algebraMap_smul ℝ (r ^ Finsupp.weight w α)]
  rfl

omit [IsScalarTower ℚ ℝ V] in
theorem weightedRadialPolynomial_coefficient (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ) (d : ℕ) :
    coefficients (weightedRadialPolynomial w p x) (Finsupp.single () d) =
      ∑ α ∈ (coefficients p).support,
        if Finsupp.weight w α = d then
          (α.prod fun i n => x i ^ n) • coefficients p α else 0 := by
  classical
  simp only [weightedRadialPolynomial, map_sum, Finsupp.finsetSum_apply,
    coefficients_monomial, Finsupp.single_apply, (Finsupp.single_injective ()).eq_iff]

theorem weightedRadialPolynomial_eq_zero (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (x : σ → ℝ)
    (hp : ∀ r : ℚ, eval₂ (fun i => (r : ℝ) ^ w i * x i) p = 0) :
    weightedRadialPolynomial w p x = 0 := by
  apply eq_zero_of_eval_zero
  intro r
  have hr : r = fun _ : Unit => r () := by funext i; cases i; rfl
  rw [hr, weightedRadialPolynomial_eval]
  exact hp (r ())

theorem eval₂_weightedHomogeneousPart_eq_zero_on (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (hp : ∀ x ∈ K, eval₂ x p = 0) (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) = 0 := by
  have hz := weightedRadialPolynomial_eq_zero w p x (fun r => hp _ (hK x hx r))
  have hc := congrArg (fun q : VectorPolynomial Unit ℚ V =>
    coefficients q (Finsupp.single () d)) hz
  rw [eval₂_weightedHomogeneousPart]
  simpa only [weightedRadialPolynomial_coefficient, map_zero, Finsupp.zero_apply] using hc

theorem eval₂_weightedHomogeneousPart_eq_on (w : σ → ℕ)
    (p q : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (hpq : ∀ x ∈ K, eval₂ x p = eval₂ x q)
    (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) =
      eval₂ x (weightedHomogeneousPart w d q) := by
  have hzero : ∀ y ∈ K, eval₂ y (p - q) = 0 := by
    intro y hy
    rw [map_sub, hpq y hy, sub_self]
  have h := eval₂_weightedHomogeneousPart_eq_zero_on w (p - q) K hK hzero d x hx
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

theorem eval₂_weightedHomogeneousPart_decomposition_on (w : σ → ℕ)
    (p a c : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (d : ℕ) (hp : ∀ α, Finsupp.weight w α ≠ d → coefficients p α = 0)
    (hdecomp : ∀ x ∈ K, eval₂ x p = eval₂ x a + eval₂ x c)
    (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x p = eval₂ x (weightedHomogeneousPart w d a) +
      eval₂ x (weightedHomogeneousPart w d c) := by
  have heq : ∀ y ∈ K, eval₂ y p = eval₂ y (a + c) := by
    intro y hy
    simpa only [map_add] using hdecomp y hy
  have h := eval₂_weightedHomogeneousPart_eq_on w p (a + c) K hK heq d x hx
  simpa only [weightedHomogeneousPart_eq_self hp, map_add] using h

theorem eval₂_weightedHomogeneousPart_mem_on (w : σ → ℕ)
    (p : VectorPolynomial σ ℚ V) (K : Set (σ → ℝ))
    (hK : ∀ x ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * x i) ∈ K)
    (S : Submodule ℝ V) (hp : ∀ x ∈ K, eval₂ x p ∈ S)
    (d : ℕ) (x : σ → ℝ) (hx : x ∈ K) :
    eval₂ x (weightedHomogeneousPart w d p) ∈ S := by
  have hzero : ∀ y ∈ K, eval₂ y (map (S.mkQ.restrictScalars ℚ) p) = 0 := by
    intro y hy
    rw [eval₂_map]
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hp y hy)
  have h := eval₂_weightedHomogeneousPart_eq_zero_on w
    (map (S.mkQ.restrictScalars ℚ) p) K hK hzero d x hx
  rw [← map_weightedHomogeneousPart, eval₂_map] at h
  exact (Submodule.Quotient.mk_eq_zero S).mp h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def homogeneousQuotientGradedPolynomial (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  map (((basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k).comp S).restrictScalars ℚ) p

theorem homogeneousQuotientGradedPolynomial_coefficient (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (α : σ →₀ ℕ) :
    coefficients (F.homogeneousQuotientGradedPolynomial b ω hF k S p) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (coefficients p α)) := by
  rw [homogeneousQuotientGradedPolynomial, coefficients_map]
  rfl

theorem homogeneousQuotientGradedPolynomial_eval (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (t : σ → ℝ) :
    eval₂ t (F.homogeneousQuotientGradedPolynomial b ω hF k S p) =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (eval₂ t p)) := by
  exact eval₂_map _ t p

theorem homogeneousQuotientGradedPolynomial_graded (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) :
    F.homogeneousQuotientGradedPolynomial b ω hF k S p ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  apply homogeneous_mem_gradedPolynomialSubmodule _ _ _ k
  · intro α hα
    rw [F.homogeneousQuotientGradedPolynomial_coefficient, hhom α hα, map_zero, map_zero]
  · intro α
    rw [F.homogeneousQuotientGradedPolynomial_coefficient]
    exact basisCoordinateProjection_idempotent _ _ _

noncomputable def homogeneousQuotientSymbolLift (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    F.RealPolynomialSymbol w :=
  F.realSymbolOfGradedPolynomial b ω hF w
    (F.homogeneousQuotientGradedPolynomial b ω hF k S p)

theorem homogeneousQuotientSymbolLift_coordinate (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z =
      if ω z.val.2 = k then
        ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
          (S (coefficients p z.val.1)) z.val.2 else 0 := by
  rw [homogeneousQuotientSymbolLift, F.realSymbolOfGradedPolynomial_coordinate,
    F.homogeneousQuotientGradedPolynomial_coefficient, basisGradeProjection_repr]

theorem realGradedSymbolPolynomial_homogeneousQuotientSymbolLift (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) :
    F.realGradedSymbolPolynomial b ω hF w
        (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
      F.homogeneousQuotientGradedPolynomial b ω hF k S p := by
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w _
    (F.homogeneousQuotientGradedPolynomial_graded b ω hF w k S p hhom)

theorem homogeneousQuotientSymbolLift_eval (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (hhom : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hF w
      (F.homogeneousQuotientSymbolLift b ω hF w k S p)) =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
        (S (eval₂ t p)) := by
  rw [F.realGradedSymbolPolynomial_homogeneousQuotientSymbolLift b ω hF w k S p hhom]
  exact F.homogeneousQuotientGradedPolynomial_eval b ω hF k S p t

theorem homogeneousQuotientSymbolLift_pure (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
      (fun z => ω z.val.2) k (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
      F.homogeneousQuotientSymbolLift b ω hF w k S p := by
  apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
  ext z
  rw [basisGradeProjection_repr, F.homogeneousQuotientSymbolLift_coordinate]
  split_ifs <;> rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators TensorProduct

theorem linearMap_abs_repr_le {V W ι κ : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [Fintype ι]
    (b : Basis ι ℝ V) (c : Basis κ ℝ W) (S : V →ₗ[ℝ] W)
    {A B : ℝ} (hA : 0 ≤ A)
    (hS : ∀ i j, |c.repr (S (b j)) i| ≤ B)
    (x : V) (hx : ∀ j, |b.repr x j| ≤ A) (i : κ) :
    |c.repr (S x) i| ≤ (Fintype.card ι : ℝ) * B * A := by
  classical
  have he : c.repr (S x) i = ∑ j, b.repr x j * c.repr (S (b j)) i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  calc
    |∑ j, b.repr x j * c.repr (S (b j)) i| ≤
        ∑ j, |b.repr x j * c.repr (S (b j)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, A * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hx j) (hS i j) (abs_nonneg _) hA
    _ = _ := by simp; ring

namespace VectorPolynomial

theorem weightedHomogeneousPart_coordinateBound {σ ι V : Type*}
    [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    (b : Basis ι ℝ V) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M : ℝ} (hM : 0 ≤ M) (p : VectorPolynomial σ ℚ V)
    (hp : ∀ α i, |b.repr (coefficients p α) i| ≤ M / monomialScale T α)
    (w : σ → ℕ) (k : ℕ) :
    ∀ α i, |b.repr (coefficients (weightedHomogeneousPart w k p) α) i| ≤
      M / monomialScale T α := by
  intro α i
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α i
  · simpa using div_nonneg hM (monomialScale_pos T hT α).le

theorem weightedHomogeneousPart_coordinateGrid {σ ι V : Type*}
    [AddCommGroup V] [Module ℚ V] [Module ℝ V]
    (b : Basis ι ℝ V) (p : VectorPolynomial σ ℚ V) (q : ℕ)
    (hp : ∀ α, (fun i => b.repr (coefficients p α) i) ∈ realDenominatorGrid q)
    (w : σ → ℕ) (k : ℕ) :
    ∀ α, (fun i => b.repr (coefficients (weightedHomogeneousPart w k p) α) i) ∈
      realDenominatorGrid q := by
  intro α
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α
  · refine ⟨0, ?_⟩
    ext i
    simp

variable {σ ι κ V W : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [LieRing W] [LieAlgebra ℚ W] [LieAlgebra ℝ W]

theorem CoefficientBound.map [Fintype ι] (b : Basis ι ℝ V) (c : Basis κ ℝ W)
    (S : V →ₗ[ℝ] W) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M B : ℝ} (hM : 0 ≤ M)
    (hS : ∀ i j, |c.repr (S (b j)) i| ≤ B)
    {p : VectorPolynomial σ ℚ V} (hp : CoefficientBound b T M p) :
    CoefficientBound c T ((Fintype.card ι : ℝ) * B * M)
      (VectorPolynomial.map (S.restrictScalars ℚ) p) := by
  intro α i
  rw [coefficients_map]
  exact (linearMap_abs_repr_le b c S
    (div_nonneg hM (monomialScale_pos T hT α).le) hS
    (coefficients p α) (hp α) i).trans_eq (by ring)

theorem CoefficientBound.gradeProjection (b : Basis ι ℝ V) (ω : ι → ℕ) (k : ℕ)
    (T : σ → ℝ) {M : ℝ} {p : VectorPolynomial σ ℚ V}
    (hp : CoefficientBound b T M p) :
    CoefficientBound b T M
      (VectorPolynomial.map ((basisGradeProjection b ω k).restrictScalars ℚ) p) := by
  intro α i
  rw [coefficients_map]
  exact (basisCoordinateProjection_abs_repr_le b {i | ω i = k}
    (coefficients p α) i).trans (hp α i)

theorem CoefficientGrid.gradeProjection (b : Basis ι ℝ V) (ω : ι → ℕ) (k : ℕ)
    {q : ℕ} {p : VectorPolynomial σ ℚ V} (hp : CoefficientGrid b q p) :
    CoefficientGrid b q (VectorPolynomial.map ((basisGradeProjection b ω k).restrictScalars ℚ) p) := by
  intro α
  rw [coefficients_map]
  exact basisCoordinateProjection_real_grid b {i | ω i = k} q _ (hp α)

theorem CoefficientBound.weightedHomogeneousPart (b : Basis ι ℝ V)
    (T : σ → ℝ) (hT : ∀ j, 0 < T j) {M : ℝ} (hM : 0 ≤ M)
    {p : VectorPolynomial σ ℚ V} (hp : CoefficientBound b T M p)
    (w : σ → ℕ) (k : ℕ) :
    CoefficientBound b T M (weightedHomogeneousPart w k p) :=
  weightedHomogeneousPart_coordinateBound b T hT hM p hp w k

theorem CoefficientGrid.weightedHomogeneousPart (b : Basis ι ℝ V)
    {q : ℕ} {p : VectorPolynomial σ ℚ V} (hp : CoefficientGrid b q p)
    (w : σ → ℕ) (k : ℕ) :
    CoefficientGrid b q (weightedHomogeneousPart w k p) :=
  weightedHomogeneousPart_coordinateGrid b p q hp w k

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι κ L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousQuotientGradedPolynomial_coefficientBound [Fintype κ]
    (eQ : Basis κ ℝ Q) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q) (T : σ → ℝ) (hT : ∀ j, 0 < T j)
    {M B : ℝ} (hM : 0 ≤ M)
    (hS : ∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i| ≤ B)
    (hp : ∀ α j, |eQ.repr (coefficients p α) j| ≤ M / monomialScale T α) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T
      ((Fintype.card κ : ℝ) * B * M)
      (F.homogeneousQuotientGradedPolynomial b ω hF k S p) := by
  intro α i
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  apply (basisCoordinateProjection_abs_repr_le
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) {i | ω i = k}
    (S (coefficients p α)) i).trans
  exact (linearMap_abs_repr_le eQ _ S
    (div_nonneg hM (monomialScale_pos T hT α).le) hS
    (coefficients p α) (hp α) i).trans_eq (by ring)

theorem homogeneousQuotientGradedPolynomial_coefficientGrid [Fintype κ] [Fintype ι]
    (eQ : Basis κ ℝ Q) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q) (qS qP : ℕ)
    (hS : ∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i) ∈ realDenominatorGrid qS)
    (hp : ∀ α, (fun j => eQ.repr (coefficients p α) j) ∈ realDenominatorGrid qP) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP)
      (F.homogeneousQuotientGradedPolynomial b ω hF k S p) := by
  intro α
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  apply basisCoordinateProjection_real_grid _ {i | ω i = k}
  have h := linear_lift_grid_of_coefficients
    ((((F.associatedGradedBasis b ω hF).baseChange ℝ).equivFun.toLinearMap).comp S)
    eQ (fun j => eQ.repr (coefficients p α) j) qP qS (hp α) hS
  simpa only [Basis.sum_repr, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Basis.equivFun_apply] using h

theorem homogeneousQuotientGradedPolynomial_rational_coefficientGrid
    {Q₀ : Type*} [AddCommGroup Q₀] [Module ℚ Q₀]
    [Fintype κ] [DecidableEq κ] [Fintype ι]
    (eQ : Basis κ ℚ Q₀) (k : ℕ) (S : Q₀ →ₗ[ℚ] F.AssociatedGraded)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] Q₀)) (qP : ℕ)
    (hp : ∀ α, (eQ.baseChange ℝ).equivFun (coefficients p α) ∈ realDenominatorGrid qP) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ)
      (matrixDenominator (LinearMap.toMatrix eQ (F.associatedGradedBasis b ω hF) S) * qP)
      (F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ) p) := by
  intro α
  rw [F.homogeneousQuotientGradedPolynomial_coefficient]
  exact basisCoordinateProjection_real_grid _ {i | ω i = k} _ _
    (realified_linear_coordinate_grid eQ (F.associatedGradedBasis b ω hF) S qP
      (coefficients p α) (hp α))

theorem homogeneousQuotientGradedPolynomial_rational_coefficientGrid_of_columns
    {Q₀ : Type*} [AddCommGroup Q₀] [Module ℚ Q₀]
    [Fintype κ] [Fintype ι]
    (eQ : Basis κ ℚ Q₀) (k : ℕ) (S : Q₀ →ₗ[ℚ] F.AssociatedGraded)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] Q₀)) (qS qP : ℕ)
    (hS : ∀ j, (fun i => (F.associatedGradedBasis b ω hF).repr (S (eQ j)) i) ∈
      denominatorGrid qS)
    (hp : ∀ α, (eQ.baseChange ℝ).equivFun (coefficients p α) ∈ realDenominatorGrid qP) :
    CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) (qS * qP)
      (F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ) p) := by
  apply F.homogeneousQuotientGradedPolynomial_coefficientGrid b ω hF
    (eQ.baseChange ℝ) k (S.baseChange ℝ) p qS qP _ hp
  intro j
  simp only [scalarExtension_basis_coordinates]
  exact (real_cast_mem_denominatorGrid_iff qS _).mpr (hS j)

theorem homogeneousQuotientGradedPolynomial_rational_coefficientBound
    {Q₀ : Type*} [AddCommGroup Q₀] [Module ℚ Q₀]
    [Fintype κ] [DecidableEq κ] [Fintype ι]
    (eQ : Basis κ ℚ Q₀) (k : ℕ) (S : Q₀ →ₗ[ℚ] F.AssociatedGraded)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] Q₀))
    (T : σ → ℝ) (hT : ∀ j, 0 < T j) {M : ℝ} (hM : 0 ≤ M) {H : ℕ}
    (hS : ∀ i j, RationalHeightLE
      (LinearMap.toMatrix eQ (F.associatedGradedBasis b ω hF) S i j) H)
    (hp : ∀ α j, |(eQ.baseChange ℝ).repr (coefficients p α) j| ≤
      M / monomialScale T α) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T
      ((Fintype.card κ : ℝ) * H * M)
      (F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ) p) := by
  apply F.homogeneousQuotientGradedPolynomial_coefficientBound b ω hF
    (eQ.baseChange ℝ) k (S.baseChange ℝ) p T hT hM _ hp
  intro i j
  simpa only [scalarExtension_basis_coordinates, LinearMap.toMatrix_apply] using
    (hS i j).abs_real_le

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

theorem coefficient_coordinateGrid_of_scalar
    {σ η Q : Type*} [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q]
    (eQ : Basis η ℝ Q) (p : VectorPolynomial σ ℚ Q) (q : ℕ)
    (hp : ∀ j, realPolynomialCoefficientGrid q
      (coordinate (eQ.coord j).toAddMonoidHom p)) :
    ∀ α, (fun j => eQ.repr (coefficients p α) j) ∈ realDenominatorGrid q := by
  classical
  choose a ha using hp
  intro α
  refine ⟨fun j => a j α, ?_⟩
  funext j
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply,
    Pi.smul_apply, smul_eq_mul] using
    congrFun (ha j) α

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι η L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousQuotientSymbolLift_coordinateBound [Fintype η]
    (eQ : Basis η ℝ Q) (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    {M B : ℝ} (hM : 0 ≤ M)
    (hS : ∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i| ≤ B)
    (hp : ∀ α j, |eQ.repr (coefficients p α) j| ≤ M)
    (z : SymbolBasisIndex w ω) :
    |((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z| ≤
      (Fintype.card η : ℝ) * B * M := by
  have h := linearMap_abs_repr_le eQ
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) S hM hS
    (coefficients p z.val.1) (hp z.val.1) z.val.2
  rw [F.homogeneousQuotientSymbolLift_coordinate]
  split_ifs
  · exact h
  · simpa only [abs_zero] using (abs_nonneg _).trans h

theorem homogeneousQuotientSymbolLift_coordinateGrid [Fintype η] [Fintype ι]
    (eQ : Basis η ℝ Q) (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (qS qP : ℕ)
    (hS : ∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i) ∈ realDenominatorGrid qS)
    (hp : ∀ α, (fun j => eQ.repr (coefficients p α) j) ∈ realDenominatorGrid qP) :
    (fun z => ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z) ∈
      realDenominatorGrid (qS * qP) := by
  classical
  have hg := F.homogeneousQuotientGradedPolynomial_coefficientGrid
    b ω hF eQ k S p qS qP hS hp
  choose a ha using hg
  refine ⟨fun z => a z.val.1 z.val.2, ?_⟩
  funext z
  change (a z.val.1 z.val.2 : ℝ) = (qS * qP : ℕ) *
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z
  rw [homogeneousQuotientSymbolLift, F.realSymbolOfGradedPolynomial_coordinate]
  exact congrFun (ha z.val.1) z.val.2

theorem homogeneousQuotientSymbolLift_coordinateGrid_of_scalar [Fintype η] [Fintype ι]
    (eQ : Basis η ℝ Q) (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q)
    (qS qP : ℕ)
    (hS : ∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (S (eQ j)) i) ∈ realDenominatorGrid qS)
    (hp : ∀ j, realPolynomialCoefficientGrid qP
      (coordinate (eQ.coord j).toAddMonoidHom p)) :
    (fun z => ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) z) ∈
      realDenominatorGrid (qS * qP) :=
  F.homogeneousQuotientSymbolLift_coordinateGrid b ω hF eQ w k S p qS qP hS
    (coefficient_coordinateGrid_of_scalar eQ p qP hp)

end NilpotentLieFiltration
end Erdos3

end

end OAI
