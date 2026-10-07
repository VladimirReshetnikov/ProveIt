/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use prod_le_prod' for generic product comparisons; mathematical statements are unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.CoordinateConstantDecomposition
import OAI.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual
import OAI.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem boundedSiteMatrix_natAbs_le {K S : Type*} (h : ℕ) (site : S → K → ℤ)
    {L : ℕ} (hL : 1 ≤ L) (hsite : ∀ s k, (site s k).natAbs ≤ L)
    (s : S) (d : BoundedCoefficientExponent K h) :
    (boundedSiteMatrix h site s d).natAbs ≤ L ^ h := by
  classical
  change (∏ k ∈ d.val.support, site s k ^ d.val k).natAbs ≤ L ^ h
  rw [show (∏ k ∈ d.val.support, site s k ^ d.val k).natAbs =
      ∏ k ∈ d.val.support, (site s k ^ d.val k).natAbs from
    map_prod Int.natAbsHom _ _]
  simp only [Int.natAbs_pow]
  calc
    _ ≤ ∏ k ∈ d.val.support, L ^ d.val k :=
      Finset.prod_le_prod' (fun k _ => Nat.pow_le_pow_left (hsite s k) _)
    _ = L ^ d.val.degree := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ L ^ h := Nat.pow_le_pow_right hL d.property

theorem boundedSiteMatrix_height {K S : Type*} (h : ℕ) (site : S → K → ℤ)
    {L : ℕ} (hL : 1 ≤ L) (hsite : ∀ s k, (site s k).natAbs ≤ L)
    (s : S) (d : BoundedCoefficientExponent K h) :
    RationalHeightLE (boundedSiteMatrix h site s d : ℚ) (L ^ h) := by
  constructor
  · simpa using boundedSiteMatrix_natAbs_le h site hL hsite s d
  · simpa using Nat.one_le_pow h L hL

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem emptyCoefficientExponent_eq (h : ℕ) (d : BoundedCoefficientExponent Empty h) :
    d = zeroCoefficientExponent Empty h := by
  apply Subtype.ext
  ext i
  exact isEmptyElim i

noncomputable def constantCoefficientArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : CoefficientArray (K := Empty) U →ₗ[ℝ] CoefficientArray (K := K) U where
  toFun x s := if s.2.val = 0 then x ⟨s.1, zeroCoefficientExponent Empty (s.1.val + 1)⟩ else 0
  map_add' x y := by
    funext s
    by_cases hs : s.2.val = 0 <;> simp [hs]
  map_smul' c x := by
    funext s
    by_cases hs : s.2.val = 0 <;> simp [hs]

theorem constantCoefficientArray_preserves_lattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := Empty) U)
    (hx : x ∈ coefficientIntegerLattice U) :
    constantCoefficientArray (K := K) U x ∈ coefficientIntegerLattice U := by
  intro s a
  by_cases hs : s.2.val = 0
  · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hs] using
      hx ⟨s.1, zeroCoefficientExponent Empty (s.1.val + 1)⟩ a
  · exact ⟨0, by simp [constantCoefficientArray, hs]⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientEvaluationArray {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := Empty) U where
  toFun x s := ∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    (boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d : ℝ) • x ⟨s.1, d⟩
  map_add' x y := by
    funext s
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext s
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro d _
    rw [mul_comm]

theorem coefficientEvaluationArray_preserves_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientEvaluationArray U t x ∈ coefficientIntegerLattice U := by
  choose z hz using hx
  intro s a
  refine ⟨∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d * z ⟨s.1, d⟩ a, ?_⟩
  change ((∑ d : BoundedCoefficientExponent K (s.1.val + 1),
    (boundedSiteMatrix (s.1.val + 1) (fun _ : Unit => t) () d : ℝ) •
      (x ⟨s.1, d⟩ : U s.1)) : U s.1).val a = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, hz, Int.cast_sum, Int.cast_mul]

theorem coefficientEvaluationArray_constant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientArray (K := Empty) U) :
    coefficientEvaluationArray U t (constantCoefficientArray U x) = x := by
  funext s
  rcases s with ⟨j, d⟩
  have hd := emptyCoefficientExponent_eq (j.val + 1) d
  subst d
  change (∑ d : BoundedCoefficientExponent K (j.val + 1),
    (boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d : ℝ) •
      (if d.val = 0 then x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩ else 0)) =
    x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp only [zeroCoefficientExponent, boundedSiteMatrix, Finsupp.prod_zero_index,
      Int.cast_one, ite_true, one_smul]
  · intro d _ hd
    have hd0 : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hd0]
  · simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientLayerInsertion {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ] CoefficientArray (K := K) U where
  toFun v s := (LinearMap.single ℝ (fun k : Fin m => BoundedCoefficientExponent K (k.val + 1) → U k) j v) s.1 s.2
  map_add' v w := by
    funext s
    simp only [map_add, Pi.add_apply]
  map_smul' c v := by
    funext s
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply]

theorem coefficientLayerInsertion_same {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j)
    (d : BoundedCoefficientExponent K (j.val + 1)) :
    coefficientLayerInsertion U j v ⟨j, d⟩ = v d := by
  simp [coefficientLayerInsertion]

theorem coefficientLayerInsertion_ne {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j k : Fin m) (h : k ≠ j)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j)
    (d : BoundedCoefficientExponent K (k.val + 1)) :
    coefficientLayerInsertion U j v ⟨k, d⟩ = 0 := by
  simp [coefficientLayerInsertion, h]

theorem coefficientArrayFunctional_layerInsertion {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientArrayFunctional U frequency (coefficientLayerInsertion U j v) =
      subspaceArrayFunctional (U j) (fun d a => (frequency j d.val a : ℝ)) v := by
  change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) *
    (coefficientLayerInsertion U j v s).val a) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp only [coefficientLayerInsertion_same]
    rfl
  · intro k _ hkj
    simp only [coefficientLayerInsertion_ne U j k hkj, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · simp

theorem coefficientEvaluationArray_layerInsertion {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientEvaluationArray U t (coefficientLayerInsertion U j v) =
      coefficientLayerInsertion (K := Empty) U j
        (fun _ => ∑ d, (boundedSiteMatrix (j.val + 1) (fun _ : Unit => t) () d : ℝ) • v d) := by
  funext s
  rcases s with ⟨k, d⟩
  by_cases hk : k = j
  · subst k
    simp only [coefficientEvaluationArray, LinearMap.coe_mk, AddHom.coe_mk,
      coefficientLayerInsertion_same]
  · simp only [coefficientEvaluationArray, LinearMap.coe_mk, AddHom.coe_mk,
      coefficientLayerInsertion_ne U j k hk, smul_zero, Finset.sum_const_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
  (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientLayerEndomorphism
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j)) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  LinearMap.pi (fun s => (LinearMap.proj s.2).comp ((R s.1).comp (coefficientLayerArray U s.1)))

theorem coefficientLayerEndomorphism_insertion
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j)) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientLayerEndomorphism U R (coefficientLayerInsertion U j v) =
      coefficientLayerInsertion U j (R j v) := by
  funext s
  rcases s with ⟨k, d⟩
  by_cases hk : k = j
  · subst k
    change R j (fun e => coefficientLayerInsertion U j v ⟨j, e⟩) d = _
    simp only [coefficientLayerInsertion_same]
  · change R k (fun e => coefficientLayerInsertion U j v ⟨k, e⟩) d = _
    simp only [coefficientLayerInsertion_ne U j k hk]
    change R k 0 d = 0
    rw [map_zero, Pi.zero_apply]

theorem coefficientLayerEndomorphism_preserves_lattice
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j))
    (hR : ∀ j x, x ∈ subspaceArrayIntegerLattice _ (U j) →
      R j x ∈ subspaceArrayIntegerLattice _ (U j))
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientLayerEndomorphism U R x ∈ coefficientIntegerLattice U := by
  intro s a
  exact hR s.1 (coefficientLayerArray U s.1 x)
    (coefficientLayerArray_preserves_lattice U s.1 x hx) s.2 a

theorem coefficientArrayFunctional_endomorphism_zero_iff [Fintype K] [∀ j, Fintype (J j)]
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    (coefficientArrayFunctional U frequency).comp (coefficientLayerEndomorphism U R) = 0 ↔
      ∀ j, (subspaceArrayFunctional (U j) (fun d => fun a => (frequency j d.val a : ℝ))).comp
        (R j) = 0 := by
  constructor
  · intro h j
    apply LinearMap.ext
    intro v
    have hv := DFunLike.congr_fun h (coefficientLayerInsertion U j v)
    simpa only [LinearMap.comp_apply, coefficientLayerEndomorphism_insertion,
      coefficientArrayFunctional_layerInsertion, LinearMap.zero_apply] using hv
  · intro h
    apply LinearMap.ext
    intro x
    change (∑ s : CoefficientSlot K m, ∑ a,
      (frequency s.1 s.2.val a : ℝ) * ((coefficientLayerEndomorphism U R x) s).val a) = 0
    rw [Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro j _
    exact DFunLike.congr_fun (h j) (coefficientLayerArray U j x)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
  {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientSiteResidual (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  coefficientLayerEndomorphism U (fun j =>
    scaledLinearResidual (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
      (matrixModuleAction (fun d s => (T j d s : ℝ))) (q j : ℝ))

theorem coefficientSiteResidual_preserves_lattice (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientSiteResidual U site q T x ∈ coefficientIntegerLattice U :=
  coefficientLayerEndomorphism_preserves_lattice U _
    (fun j x hx => scaledSiteResidual_preserves_lattice (U j) _ (T j) (q j) x hx) x hx

theorem coefficientSiteResidual_zero_iff [∀ j, Fintype (J j)]
    (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (hq : ∀ j, 0 < q j)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q j : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    (coefficientArrayFunctional U frequency).comp (coefficientSiteResidual U site q T) = 0 ↔
      ∀ j, ∃ M : (S → U j) →ₗ[ℝ] ℝ,
        ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
          coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
            M (siteEvaluation (fun s k => (site s k : ℝ)) p) := by
  rw [coefficientSiteResidual, coefficientArrayFunctional_endomorphism_zero_iff]
  constructor
  · intro h j
    obtain ⟨M, hM⟩ := (scaledLinearResidual_factor_iff _ _
      (show (q j : ℝ) ≠ 0 by exact_mod_cast (hq j).ne') (hT j) _).mp (h j)
    refine ⟨M, ?_⟩
    intro p hp
    have he := DFunLike.congr_fun hM (fun d => coefficients p d.val)
    have hr := boundedArrayPolynomial_reconstruct p hp
    rw [← hr, coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial]
    exact he
  · intro h j
    obtain ⟨M, hM⟩ := h j
    apply (scaledLinearResidual_factor_iff _ _
      (show (q j : ℝ) ≠ 0 by exact_mod_cast (hq j).ne') (hT j) _).mpr
    refine ⟨M, ?_⟩
    apply LinearMap.ext
    intro x
    exact bounded_site_factorization_to_array (U j) (j.val + 1) site _ M hM x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ} {J : Fin m → Type*}
  (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
  (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

theorem coefficientSiteResidual_cover_on_kernel (x : CoefficientTorus (K := K) U)
    (hx : coefficientSiteTorusMap U site x = 0) :
    linearQuotientEndomorphism (coefficientIntegerLattice U)
      (coefficientSiteResidual U site (fun _ => q) T)
      (coefficientSiteResidual_preserves_lattice U site (fun _ => q) T) x =
        quotientIntegerCover (coefficientIntegerLattice U) q x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk]
  change QuotientAddGroup.mk' (coefficientIntegerLattice U)
    (coefficientSiteResidual U site (fun _ => q) T v) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ) • v)
  apply QuotientAddGroup.eq.mpr
  intro s a
  have hsite := congrFun hx s.1
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U s.1))
    (matrixModuleAction (fun t d => (boundedSiteMatrix (s.1.val + 1) site t d : ℝ))
      (coefficientLayerArray U s.1 v)) = 0 at hsite
  have hi := (QuotientAddGroup.eq_zero_iff _).mp hsite
  have ht := integerMatrix_preserves_array_lattice (U s.1) (T s.1) _ hi
  obtain ⟨z, hz⟩ := ht s.2 a
  refine ⟨z, ?_⟩
  change (-((q : ℝ) * (v s).val a -
      (matrixModuleAction (fun d t => (T s.1 d t : ℝ))
        (matrixModuleAction (fun t d => (boundedSiteMatrix (s.1.val + 1) site t d : ℝ))
          (coefficientLayerArray U s.1 v)) s.2).val a) + (q : ℝ) * (v s).val a) = z
  linarith

theorem coefficientSiteResidual_site_zero
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
        (matrixModuleAction (fun d s => (T j d s : ℝ))
          (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)) x)
    (x : CoefficientTorus (K := K) U) :
    coefficientSiteTorusMap U site
      (linearQuotientEndomorphism (coefficientIntegerLattice U)
        (coefficientSiteResidual U site (fun _ => q) T)
        (coefficientSiteResidual_preserves_lattice U site (fun _ => q) T) x) = 0 := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  funext j
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U j))
    (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
      (scaledLinearResidual (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
        (matrixModuleAction (fun d s => (T j d s : ℝ))) (q : ℝ)
        (coefficientLayerArray U j v))) = 0
  rw [scaledLinearResidual_evaluation _ _ _ (hT j), map_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientRowPolynomial_sub (c d : CoefficientArray (K := K) U) (j : Fin m) (i : J j) :
    coefficientRowPolynomial U (c - d) j i =
      coefficientRowPolynomial U c j i - coefficientRowPolynomial U d j i := by
  simp only [coefficientRowPolynomial, monomialArrayPolynomial, Pi.sub_apply,
    Submodule.coe_sub, map_sub, Finset.sum_sub_distrib]

theorem coefficientRowPolynomial_constant (z : ∀ j, U j) (j : Fin m) (i : J j) :
    coefficientRowPolynomial U (constantCoefficientArray (K := K) U (fun s => z s.1)) j i =
      MvPolynomial.C ((z j).val i) := by
  classical
  unfold coefficientRowPolynomial monomialArrayPolynomial
  rw [Finset.sum_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [constantCoefficientArray, zeroCoefficientExponent]
  · intro d _ hd
    have hzero : d.val ≠ 0 := fun h => hd (Subtype.ext h)
    simp [constantCoefficientArray, hzero]
  · simp

theorem coefficientRowPolynomial_eval (c : CoefficientArray (K := K) U)
    (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x (coefficientRowPolynomial U c j i) =
      eval x (boundedArrayPolynomial (W := J j → ℝ) (j.val + 1) (fun d => (c ⟨j, d⟩).val)) i := by
  simp [coefficientRowPolynomial, monomialArrayPolynomial, boundedArrayPolynomial,
    eval_monomial, MvPolynomial.eval_monomial, Finset.sum_apply, mul_comm]

theorem coefficientRowPolynomial_affine_eval {V : Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frame : Option K → V → ℝ) (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x (coefficientRowPolynomial U (affineSampleCoefficientArray U p hm frame) j i) =
      eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i := by
  rw [coefficientRowPolynomial_eval]
  simp_rw [affineSampleCoefficientArray_val]
  rw [boundedArrayPolynomial_reconstruct _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree frame) (p j) (hp j)),
    eval_substitute]
  simp only [affineParameterSubstitution_eval]

end Erdos3.VectorPolynomial

end

end OAI
