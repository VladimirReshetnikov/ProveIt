import Mathlib.LinearAlgebra.StdBasis
import OAI.Combinatorics.Progressions.Estimates.SquarefreeStructureHeight
import OAI.Combinatorics.Progressions.Geometry.SupportedQuotientFamilyFaithful
import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
import OAI.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
import OAI.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positiveCoefficientLayer (a : BoxedDegreeIndex bound) : Submodule ℚ L := by
  classical
  exact if boxedDegreeMonomial a = 0 then ⊥ else F.layer (fun i => (a i).val)

theorem mem_positiveCoefficientLayer (a : BoxedDegreeIndex bound) (x : L) :
    x ∈ F.positiveCoefficientLayer a ↔
      x ∈ F.layer (fun i => (a i).val) ∧ (boxedDegreeMonomial a = 0 → x = 0) := by
  classical
  by_cases ha : boxedDegreeMonomial a = 0
  · have hzero : (fun i => (a i).val) = 0 := by
      funext i
      have h := congrArg (fun b : σ →₀ ℕ => b i) ha
      simpa only [boxedDegreeMonomial_apply, Finsupp.zero_apply, Pi.zero_apply] using h
    simp [positiveCoefficientLayer, ha, hzero, F.zero_eq_top]
  · simp [positiveCoefficientLayer, ha]

theorem boxedPolynomial_positive (f : ∀ a : BoxedDegreeIndex bound, F.positiveCoefficientLayer a) :
    boxedPolynomial (fun a => (f a).val) ∈ F.positivePolynomialAlgebra := by
  constructor
  · intro a
    by_cases ha : (fun i => a i) ≤ bound
    · obtain ⟨b, rfl⟩ := exists_boxedDegreeMonomial a ha
      rw [boxedPolynomial_coefficient]
      simpa only [boxedDegreeMonomial_apply] using
        ((F.mem_positiveCoefficientLayer b (f b).val).mp (f b).property).1
    · rw [boxedPolynomial_coefficient_outside _ a ha]
      exact Submodule.zero_mem _
  · obtain ⟨b, hb⟩ := exists_boxedDegreeMonomial (bound := bound) 0 (fun i => Nat.zero_le _)
    rw [← hb, boxedPolynomial_coefficient]
    exact ((F.mem_positiveCoefficientLayer b (f b).val).mp (f b).property).2 hb

noncomputable def positivePolynomialCoefficientEquiv :
    F.positivePolynomialAlgebra ≃ₗ[ℚ] (∀ a : BoxedDegreeIndex bound, F.positiveCoefficientLayer a) where
  toFun p a := ⟨coefficients p.val (boxedDegreeMonomial a),
    (F.mem_positiveCoefficientLayer a _).mpr ⟨by
      simpa only [boxedDegreeMonomial_apply] using p.property.1 (boxedDegreeMonomial a),
      fun ha => by rw [ha]; exact p.property.2⟩⟩
  invFun f := ⟨boxedPolynomial (fun a => (f a).val), F.boxedPolynomial_positive f⟩
  left_inv p := by
    apply F.positivePolynomialCoordinates_injective
    funext a
    exact boxedPolynomial_coefficient _ a
  right_inv f := by
    funext a
    apply Subtype.ext
    exact boxedPolynomial_coefficient _ a
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

theorem positivePolynomialCoefficientEquiv_apply
    (p : F.positivePolynomialAlgebra) (a : BoxedDegreeIndex bound) :
    (F.positivePolynomialCoefficientEquiv p a).val = coefficients p.val (boxedDegreeMonomial a) := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialBasis : Basis (Σ a, κ a) ℚ F.positivePolynomialAlgebra := by
  classical
  exact (Pi.basis b).map F.positivePolynomialCoefficientEquiv.symm

theorem positivePolynomialBasis_repr (p : F.positivePolynomialAlgebra) (j : Σ a, κ a) :
    (F.positivePolynomialBasis b).repr p j =
      (b j.1).repr (F.positivePolynomialCoefficientEquiv p j.1) j.2 := by
  classical
  rfl

theorem positivePolynomialBasis_coefficient_self (a : BoxedDegreeIndex bound) (j : κ a) :
    coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial a) = (b a j).val := by
  classical
  change (F.positivePolynomialCoefficientEquiv (F.positivePolynomialBasis b ⟨a, j⟩) a).val = _
  simp only [positivePolynomialBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, Pi.single_eq_same]

theorem positivePolynomialBasis_coefficient_ne (a c : BoxedDegreeIndex bound)
    (h : a ≠ c) (j : κ a) :
    coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial c) = 0 := by
  classical
  change (F.positivePolynomialCoefficientEquiv (F.positivePolynomialBasis b ⟨a, j⟩) c).val = _
  simp only [positivePolynomialBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, Pi.single_eq_of_ne (Ne.symm h), ZeroMemClass.coe_zero]

theorem positivePolynomialBasis_monomial (j : Σ a, κ a) :
    (F.positivePolynomialBasis b j).val = monomial (boxedDegreeMonomial j.1) (b j.1 j.2).val := by
  classical
  apply coefficients.injective
  ext a
  by_cases ha : (fun i => a i) ≤ bound
  · obtain ⟨c, rfl⟩ := exists_boxedDegreeMonomial a ha
    by_cases hc : j.1 = c
    · subst c
      rw [F.positivePolynomialBasis_coefficient_self, coefficients_monomial, Finsupp.single_eq_same]
    · rw [F.positivePolynomialBasis_coefficient_ne b _ _ hc]
      simp [boxedDegreeMonomial_injective.ne hc]
  · have hp : coefficients (F.positivePolynomialBasis b j).val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using
        (F.positivePolynomialBasis b j).property.1 a
    have hne : boxedDegreeMonomial j.1 ≠ a := by
      intro h
      apply ha
      simpa only [h] using boxedDegreeMonomial_le j.1
    simp [hp, hne]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialSupport (S : Set (σ →₀ ℕ)) : Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport S).comap F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialSupport_eq_span (S : Set (σ →₀ ℕ)) :
    F.positivePolynomialSupport S =
      Submodule.span ℚ (F.positivePolynomialBasis b '' {j | boxedDegreeMonomial j.1 ∈ S}) := by
  ext p
  rw [basis_mem_span_image_iff]
  constructor
  · intro hp j hj
    have hz : F.positivePolynomialCoefficientEquiv p j.1 = 0 := Subtype.ext (hp _ hj)
    rw [F.positivePolynomialBasis_repr, hz, map_zero, Finsupp.zero_apply]
  · intro hp a ha
    change coefficients p.val a = 0
    by_cases hbox : (fun i => a i) ≤ bound
    · obtain ⟨c, rfl⟩ := exists_boxedDegreeMonomial a hbox
      have hz : F.positivePolynomialCoefficientEquiv p c = 0 := by
        apply (b c).repr.injective
        ext j
        simpa only [F.positivePolynomialBasis_repr, map_zero, Finsupp.zero_apply] using hp ⟨c, j⟩ ha
      exact congrArg Subtype.val hz
    · simpa only [F.terminal _ hbox, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialSupportedBasis (S : Set (σ →₀ ℕ)) :
    Basis {j : Σ a, κ a // boxedDegreeMonomial j.1 ∈ S} ℚ (F.positivePolynomialSupport S) :=
  supportedSubmoduleBasis (F.positivePolynomialBasis b) _ _ (F.positivePolynomialSupport_eq_span b S)

theorem positivePolynomialSupportedBasis_coe (S : Set (σ →₀ ℕ))
    (j : {j : Σ a, κ a // boxedDegreeMonomial j.1 ∈ S}) :
    (F.positivePolynomialSupportedBasis b S j).val = F.positivePolynomialBasis b j.val :=
  supportedSubmoduleBasis_coe _ _ _ _ j

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial

variable {σ ν L : Type*} [Fintype σ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
  (hb : ∀ a j k, RationalHeightLE (e.repr (b a j).val k) H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)

include hH hb hc in
theorem positivePolynomialBasis_bracket_coefficient_height
    (x y : Σ a, κ a) (a : BoxedDegreeIndex bound) (k : ν) :
    RationalHeightLE (e.repr
      (F.positivePolynomialCoefficientEquiv ⁅F.positivePolynomialBasis b x,
        F.positivePolynomialBasis b y⁆ a).val k)
      (squarefreeBracketHeight (Fintype.card ν) H) := by
  classical
  rw [F.positivePolynomialCoefficientEquiv_apply]
  change RationalHeightLE (e.repr (coefficients
    ⁅(F.positivePolynomialBasis b x).val, (F.positivePolynomialBasis b y).val⁆
    (boxedDegreeMonomial a)) k) _
  rw [F.positivePolynomialBasis_monomial, F.positivePolynomialBasis_monomial, lie_monomial]
  by_cases ha : boxedDegreeMonomial x.1 + boxedDegreeMonomial y.1 = boxedDegreeMonomial a
  · rw [ha, coefficients_monomial, Finsupp.single_eq_same]
    exact lie_bracket_coordinate_height e hc _ _ (hb x.1 x.2) (hb y.1 y.2) k
  · simp only [coefficients_monomial, Finsupp.single_apply, ha, ite_false, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (squarefreeBracketHeight_pos _ hH)

include hH hb hc in
theorem positivePolynomialBasis_structure_height [∀ a, Fintype (κ a)]
    (hκ : ∀ a, Fintype.card (κ a) ≤ Fintype.card ν) (x y z : Σ a, κ a) :
    RationalHeightLE (lieStructureConstants (F.positivePolynomialBasis b) x y z)
      (squarefreeStructureHeight (Fintype.card ν) H) := by
  change RationalHeightLE ((F.positivePolynomialBasis b).repr
    ⁅F.positivePolynomialBasis b x, F.positivePolynomialBasis b y⁆ z) _
  rw [F.positivePolynomialBasis_repr]
  have h := submodule_basis_coordinate_height (F.positiveCoefficientLayer z.1) (b z.1) e hH
    (fun i j => hb z.1 j i)
    (F.positivePolynomialCoefficientEquiv ⁅F.positivePolynomialBasis b x,
      F.positivePolynomialBasis b y⁆ z.1)
    (fun k => F.positivePolynomialBasis_bracket_coefficient_height b e hH hb hc x y z.1 k) z.2
  apply h.mono
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (rationalSolveHeight_mono hH (hκ z.1))) _)

theorem positivePolynomialBasis_evaluation (j : Σ a, κ a) :
    F.positivePolynomialEvaluation (F.positivePolynomialBasis b j) = (b j.1 j.2).val := by
  rw [F.positivePolynomialEvaluation_apply, F.positivePolynomialBasis_monomial]
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

theorem positivePolynomialDownsetIdeal_eq_support :
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule =
      F.positivePolynomialSupport Jᶜ := rfl

theorem positivePolynomialDownsetIdeal_eq_span :
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule =
      Submodule.span ℚ (F.positivePolynomialBasis b '' {j | boxedDegreeMonomial j.1 ∉ J}) :=
  (F.positivePolynomialDownsetIdeal_eq_support J hJ).trans
    (F.positivePolynomialSupport_eq_span b Jᶜ)

noncomputable def positivePolynomialDownsetBasis :
    Basis {j : Σ a, κ a // j ∉ {k | boxedDegreeMonomial k.1 ∉ J}} ℚ
      (F.positivePolynomialAlgebra ⧸ restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) :=
  supportedQuotientBasis (F.positivePolynomialBasis b) _ _
    (F.positivePolynomialDownsetIdeal_eq_span b J hJ)

theorem positivePolynomialDownsetBasis_apply (j) :
    F.positivePolynomialDownsetBasis b J hJ j =
      lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)
        (F.positivePolynomialBasis b j.val) :=
  supportedQuotientBasis_apply _ _ _ _ j

theorem positivePolynomialDownsetBasis_repr (x : F.positivePolynomialAlgebra) (j) :
    (F.positivePolynomialDownsetBasis b J hJ).repr
      (lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) x) j =
        (F.positivePolynomialBasis b).repr x j.val :=
  supportedQuotientBasis_repr_mk _ _ _ _ x j

theorem positivePolynomialDownset_multidegree_span (a : σ → ℕ) :
    (F.positivePolynomialDownsetQuotient J hJ).layer a =
      Submodule.span ℚ (F.positivePolynomialDownsetBasis b J hJ ''
        {j | a ≤ fun i => boxedDegreeMonomial j.val.1 i}) := by
  change (F.positivePolynomialSupport {c : σ →₀ ℕ | a ≤ fun i => c i}).map
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule.mkQ = _
  rw [F.positivePolynomialSupport_eq_span b]
  exact supportedQuotientBasis_map_span _ _ _ _ _

theorem positivePolynomialDownset_degree_span (n : ℕ) :
    (F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n =
      Submodule.span ℚ (F.positivePolynomialDownsetBasis b J hJ ''
        {j | n ≤ ∑ i, boxedDegreeMonomial j.val.1 i}) := by
  change (F.positivePolynomialSupport {c : σ →₀ ℕ | n ≤ ∑ i, c i}).map
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule.mkQ = _
  rw [F.positivePolynomialSupport_eq_span b]
  exact supportedQuotientBasis_map_span _ _ _ _ _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

include b in
theorem positivePolynomial_downset_basis_cover (J K : Set (σ →₀ ℕ))
    (hcover : ∀ a, a ≠ 0 → a ∉ J ∪ K → F.layer (fun i => a i) = ⊥)
    (j : Σ a, κ a) : boxedDegreeMonomial j.1 ∈ J ∨ boxedDegreeMonomial j.1 ∈ K := by
  classical
  rcases j with ⟨a, j⟩
  by_contra hc
  have hz := F.positivePolynomial_support_of_layers (J ∪ K) hcover
    (F.positivePolynomialBasis b ⟨a, j⟩) (boxedDegreeMonomial a) hc
  change coefficients (F.positivePolynomialBasis b ⟨a, j⟩).val (boxedDegreeMonomial a) = 0 at hz
  rw [F.positivePolynomialBasis_coefficient_self] at hz
  exact (b a).ne_zero j (Subtype.ext hz)

noncomputable def positivePolynomialDownsetCosetMap
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) :=
  F.positivePolynomialMultidegree.ordinary.realQuotientCosetMap
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)
    (t := ∑ i, bound i) (by
      rw [F.positivePolynomialMultidegree.ordinary.terminal]
      exact bot_le) Γ

variable [DecidableEq σ] [∀ a, Fintype (κ a)]

theorem positivePolynomial_downset_coset_pair_injective
    (J K : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (hK : IsLowerSet K)
    (hcover : ∀ a, a ≠ 0 → a ∉ J ∪ K → F.layer (fun i => a i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B) :
    Function.Injective (fun x =>
      (F.positivePolynomialDownsetCosetMap J hJ Γ x,
        F.positivePolynomialDownsetCosetMap K hK Γ x)) := by
  classical
  apply F.positivePolynomialMultidegree.ordinary.realQuotientCosetPair_injective
    (F.positivePolynomialBasis b)
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ) _
    {j | boxedDegreeMonomial j.1 ∉ J} (F.positivePolynomialDownsetIdeal_eq_span b J hJ)
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra K hK) _
    {j | boxedDegreeMonomial j.1 ∉ K} (F.positivePolynomialDownsetIdeal_eq_span b K hK)
    _ Γ B hgrid
  intro i
  simpa only [Set.mem_ofPred_eq, not_not] using F.positivePolynomial_downset_basis_cover b J K hcover i

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators

variable {α σ L : Type*} [Fintype α] [DecidableEq α] [Fintype σ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound)
  (J : α → Set (σ →₀ ℕ)) (hJ : ∀ a, IsLowerSet (J a))

noncomputable def positivePolynomialQuotientProduct :=
  NilpotentLieFiltration.pi (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)

noncomputable def positivePolynomialQuotientProductMap :
    F.positivePolynomialAlgebra →ₗ⁅ℚ⁆
      (∀ a, F.positivePolynomialAlgebra ⧸ restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a)) :=
  liePiMap (fun a => lieQuotientMap (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a)))

noncomputable def positivePolynomialQuotientProductRealMap :
    F.positivePolynomialMultidegree.ordinary.realification.Group →*
      (F.positivePolynomialQuotientProduct J hJ).realification.Group :=
  realificationMap (hnil := F.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.positivePolynomialQuotientProduct J hJ).lowerCentralSeries_eq_bot)
    (F.positivePolynomialQuotientProductMap J hJ)

noncomputable def positivePolynomialQuotientProductLattice
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) :
    Subgroup (F.positivePolynomialQuotientProduct J hJ).Group :=
  piBCHSubgroup (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
    (fun a => Γ.map (F.positivePolynomialMultidegree.ordinary.quotientStepHom
      (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
      (by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)))

theorem positivePolynomialQuotientProductRealMap_component
    (g : F.positivePolynomialMultidegree.ordinary.realification.Group) (a : α) :
    realBCHPiEquiv (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary)
      (F.positivePolynomialQuotientProductRealMap J hJ g) a =
        F.positivePolynomialMultidegree.ordinary.realQuotientStepHom
          (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
          (by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le) g := by
  apply NilpotentLieBCHGroup.ext
  exact realification_liePiEval_liePiMap _ g.coord a

variable {κ : BoxedDegreeIndex bound → Type*}
  (b : ∀ c, Basis (κ c) ℚ (F.positiveCoefficientLayer c))

omit [Fintype α] [DecidableEq α] in
include b in
theorem positivePolynomial_quotient_family_basis_cover
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (j : Σ c, κ c) : ∃ a, boxedDegreeMonomial j.1 ∈ J a := by
  classical
  rcases j with ⟨c, j⟩
  by_contra hnone
  have hs : ∀ c, c ≠ 0 → c ∉ ⋃ a, J a → F.layer (fun i => c i) = ⊥ := by
    intro c hc hnot
    exact hcover c hc (fun a ha => hnot (Set.mem_iUnion.mpr ⟨a, ha⟩))
  have hz := F.positivePolynomial_support_of_layers (⋃ a, J a) hs
    (F.positivePolynomialBasis b ⟨c, j⟩) (boxedDegreeMonomial c)
    (fun h => hnone (Set.mem_iUnion.mp h))
  change coefficients (F.positivePolynomialBasis b ⟨c, j⟩).val (boxedDegreeMonomial c) = 0 at hz
  rw [F.positivePolynomialBasis_coefficient_self] at hz
  exact (b c).ne_zero j (Subtype.ext hz)

variable [DecidableEq σ] [∀ c, Fintype (κ c)]

omit [DecidableEq σ] [∀ c, Fintype (κ c)] in
include b in
theorem positivePolynomialQuotientProductRealMap_injective
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥) :
    Function.Injective (F.positivePolynomialQuotientProductRealMap J hJ) := by
  classical
  have hcov (j : Σ c, κ c) : ∃ a, j ∉ {k | boxedDegreeMonomial k.1 ∉ J a} := by
    simpa only [Set.mem_ofPred_eq, not_not] using F.positivePolynomial_quotient_family_basis_cover J b hcover j
  intro g h heq
  apply F.positivePolynomialMultidegree.ordinary.realQuotientFamily_joint_injective
    (t := ∑ i, bound i)
    (F.positivePolynomialBasis b)
    (fun a => restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
    (fun a => by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)
    (fun a => {k | boxedDegreeMonomial k.1 ∉ J a})
    (fun a => F.positivePolynomialDownsetIdeal_eq_span b (J a) (hJ a)) hcov
  funext a
  simpa only [F.positivePolynomialQuotientProductRealMap_component] using
    congrArg (fun x => realBCHPiEquiv
      (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary) x a) heq

theorem positivePolynomialQuotientProduct_lattice_detect
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B)
    (g : F.positivePolynomialMultidegree.ordinary.realification.Group)
    (hg : F.positivePolynomialQuotientProductRealMap J hJ g ∈
      (F.positivePolynomialQuotientProductLattice J hJ Γ).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  apply F.positivePolynomialMultidegree.ordinary.realQuotientFamily_lattice_detect
    (t := ∑ i, bound i)
    (F.positivePolynomialBasis b)
    (fun a => restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra (J a) (hJ a))
    (fun a => by rw [F.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le)
    (fun a => {k | boxedDegreeMonomial k.1 ∉ J a})
    (fun a => F.positivePolynomialDownsetIdeal_eq_span b (J a) (hJ a))
    (fun j => by simpa only [Set.mem_ofPred_eq, not_not] using
      F.positivePolynomial_quotient_family_basis_cover J b hcover j) Γ B hgrid g
  intro a
  have ha := (realBCHPiEquiv_mem_lattice
    (fun a => (F.positivePolynomialDownsetQuotient (J a) (hJ a)).ordinary) _ _).mp hg a
  simpa only [F.positivePolynomialQuotientProductRealMap_component] using ha

theorem positivePolynomialQuotientProduct_lattice_cover
    (hcover : ∀ c, c ≠ 0 → (∀ a, c ∉ J a) → F.layer (fun i => c i) = ⊥)
    (Γ : Subgroup F.positivePolynomialMultidegree.ordinary.Group) (B : ℕ)
    (hgrid : bchSubgroupCoordinates (F.positivePolynomialBasis b) Γ = scaledIntegerGrid B) :
    (F.positivePolynomialQuotientProductLattice J hJ Γ).map realificationHom ⊓
      (F.positivePolynomialQuotientProductRealMap J hJ).range ≤
        (Γ.map realificationHom).map (F.positivePolynomialQuotientProductRealMap J hJ) := by
  rintro y ⟨hy, g, rfl⟩
  exact Subgroup.mem_map.mpr ⟨g,
    F.positivePolynomialQuotientProduct_lattice_detect J hJ b hcover Γ B hgrid g hy, rfl⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))
  (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetMultidegreeBasis (a : σ → ℕ) :
    Basis (Fin (finrank ℚ ((F.positivePolynomialDownsetQuotient J hJ).layer a))) ℚ
      ((F.positivePolynomialDownsetQuotient J hJ).layer a) := by
  classical
  let c := supportedSubmoduleBasis (F.positivePolynomialDownsetBasis b J hJ) _ _
    (F.positivePolynomialDownset_multidegree_span b J hJ a)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem positivePolynomialDownsetMultidegreeBasis_height (a : σ → ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialDownsetBasis b J hJ).repr
      (F.positivePolynomialDownsetMultidegreeBasis b J hJ a j).val k) 1 := by
  classical
  unfold positivePolynomialDownsetMultidegreeBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def positivePolynomialDownsetDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ ((F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n))) ℚ
      ((F.positivePolynomialDownsetQuotient J hJ).ordinary.layer n) := by
  classical
  let c := supportedSubmoduleBasis (F.positivePolynomialDownsetBasis b J hJ) _ _
    (F.positivePolynomialDownset_degree_span b J hJ n)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

theorem positivePolynomialDownsetDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialDownsetBasis b J hJ).repr
      (F.positivePolynomialDownsetDegreeBasis b J hJ n j).val k) 1 := by
  classical
  unfold positivePolynomialDownsetDegreeBasis
  rw [Basis.reindex_apply, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one _ _ _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  {κ : BoxedDegreeIndex bound → Type*} [∀ a, Fintype (κ a)]
  (b : ∀ a, Basis (κ a) ℚ (F.positiveCoefficientLayer a))

noncomputable def positivePolynomialSupportedFinBasis (S : Set (σ →₀ ℕ)) :
    Basis (Fin (finrank ℚ (F.positivePolynomialSupport S))) ℚ (F.positivePolynomialSupport S) := by
  classical
  exact (F.positivePolynomialSupportedBasis b S).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (F.positivePolynomialSupportedBasis b S)).symm)

theorem positivePolynomialSupportedFinBasis_height (S : Set (σ →₀ ℕ)) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialSupportedFinBasis b S j).val k) 1 := by
  classical
  unfold positivePolynomialSupportedFinBasis
  rw [Basis.reindex_apply, F.positivePolynomialSupportedBasis_coe]
  exact basis_repr_height_one _ _ _

noncomputable def positivePolynomialMultidegreeBasis (a : σ → ℕ) :
    Basis (Fin (finrank ℚ (F.positivePolynomialMultidegreeLayer a))) ℚ
      (F.positivePolynomialMultidegreeLayer a) :=
  F.positivePolynomialSupportedFinBasis b {c : σ →₀ ℕ | a ≤ fun i => c i}

theorem positivePolynomialMultidegreeBasis_height (a : σ → ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialMultidegreeBasis b a j).val k) 1 :=
  F.positivePolynomialSupportedFinBasis_height b _ j k

noncomputable def positivePolynomialDegreeBasis (n : ℕ) :
    Basis (Fin (finrank ℚ (F.positivePolynomialDegreeLayer n))) ℚ
      (F.positivePolynomialDegreeLayer n) :=
  F.positivePolynomialSupportedFinBasis b {c : σ →₀ ℕ | n ≤ ∑ i, c i}

theorem positivePolynomialDegreeBasis_height (n : ℕ) (j k) :
    RationalHeightLE ((F.positivePolynomialBasis b).repr
      (F.positivePolynomialDegreeBasis b n j).val k) 1 :=
  F.positivePolynomialSupportedFinBasis_height b _ j k

end Erdos3.MultidegreeLieFiltration

end

end OAI
