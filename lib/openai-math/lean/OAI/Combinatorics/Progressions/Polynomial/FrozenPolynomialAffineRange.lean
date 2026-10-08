/-
Modified for ProveIt: import Lean 4.32 compatibility declarations and use
zero_mul for the zero coefficient on the left in polynomialFamily_eval_mem.
All theorem statements are unchanged from the pinned upstream source.
-/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.IntegerFrozenChart
import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_monomial_eq_C_of_no_keep (keep : I → Prop)
    (fixed : {i // ¬keep i} → R) (d : I →₀ ℕ)
    (hd : ¬∃ i, keep i ∧ d i ≠ 0) (c : R) :
    freezePolynomial keep fixed (monomial d c) =
      C (eval (finiteSplitPoint keep (0 : {i // keep i} → R) fixed) (monomial d c)) := by
  classical
  simp only [freezePolynomial, aeval_monomial, eval_monomial,
    map_mul, map_finsuppProd, map_pow]
  congr 1
  apply Finsupp.prod_congr
  intro i hi
  have hkeep : ¬keep i := fun h => hd ⟨i, h, Finsupp.mem_support_iff.mp hi⟩
  simp [frozenCoordinate, finiteSplitPoint, hkeep]

theorem freezePolynomial_monomial_coeff_eq_zero_of_no_keep (keep : I → Prop)
    (fixed : {i // ¬keep i} → R) (d : I →₀ ℕ)
    (hd : ¬∃ i, keep i ∧ d i ≠ 0) (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (freezePolynomial keep fixed (monomial d (1 : R))).coeff α = 0 := by
  rw [freezePolynomial_monomial_eq_C_of_no_keep keep fixed d hd]
  exact coeff_C_of_ne_zero hα _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

theorem polynomialFamily_eval_mem {J τ R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial τ R) (K : Submodule R (J → R))
    (hP : ∀ α, (fun j => (P j).coeff α) ∈ K) (x : τ → R) :
    (fun j => MvPolynomial.eval x (P j)) ∈ K := by
  classical
  let S : Finset (τ →₀ ℕ) := Finset.univ.biUnion (fun j => (P j).support)
  have he (j : J) : MvPolynomial.eval x (P j) =
      ∑ α ∈ S, (α.prod fun i n => x i ^ n) * (P j).coeff α := by
    conv_lhs => rw [← (P j).support_sum_monomial_coeff, map_sum]
    simp only [eval_monomial, mul_comm]
    apply Finset.sum_subset
    · intro α hα
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hα⟩
    · intro α _ hα
      have hz : (P j).coeff α = 0 := by
        simpa only [mem_support_iff, not_not] using hα
      rw [hz, zero_mul]
  have he' : (fun j => MvPolynomial.eval x (P j)) =
      ∑ α ∈ S, (α.prod fun i n => x i ^ n) • (fun j => (P j).coeff α) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he j
  rw [he']
  exact K.sum_mem (fun α _ => K.smul_mem _ (hP α))

theorem longChart_top_eval_mem {J Full Long : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (f : Long ↪ Full) (r : ℕ)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : Long →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain f) : ℤ) : ℝ)) ∈ K)
    (x : Long → ℝ) :
    (fun j => MvPolynomial.eval x
      (killCompl f.injective (homogeneousComponent r
        (MvPolynomial.map (Int.castRingHom ℝ) (β j))))) ∈ K := by
  apply polynomialFamily_eval_mem
  intro α
  simp only [coeff_killCompl, coeff_homogeneousComponent, Finsupp.degree_mapDomain,
    coeff_map, Int.coe_castRingHom]
  by_cases hα : α.degree = r
  · simp only [ite_eq_left hα]
    exact hcoeff α hα
  · simp only [ite_eq_right hα]
    exact K.zero_mem

theorem longChart_conditioned_top_eval_mem {J Full Long : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (f : Long ↪ Full) (r : ℕ)
    (hdegree : ∀ j, (β j).totalDegree ≤ r)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : Long →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain f) : ℤ) : ℝ)) ∈ K)
    (frozen : Full → ℝ) (x : Long → ℝ) :
    (fun j => MvPolynomial.eval x (homogeneousComponent r
      (conditionPolynomial f f.injective frozen
        (MvPolynomial.map (Int.castRingHom ℝ) (β j))))) ∈ K := by
  have htop (j : J) := homogeneousComponent_conditionPolynomial_top f f.injective
    (MvPolynomial.map (Int.castRingHom ℝ) (β j)) frozen r
    ((totalDegree_map_le _ _).trans (hdegree j))
  simp only [htop]
  exact longChart_top_eval_mem β f r K hcoeff x

theorem longChart_freezePolynomial_zero_eq_killCompl {I R : Type*} [CommRing R]
    (keep : I → Prop) :
    freezePolynomial keep (0 : {i // ¬ keep i} → R) =
      killCompl (Subtype.val_injective (p := keep)) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : keep i
  · let a : {i // keep i} := ⟨i, hi⟩
    have hk := killCompl_rename_app (R := R) (Subtype.val_injective (p := keep))
      (MvPolynomial.X a)
    simp only [rename_X] at hk
    simpa only [freezePolynomial, aeval_X, frozenCoordinate, dite_eq_left hi] using hk.symm
  · have hrange : i ∉ Set.range (Subtype.val : {i // keep i} → I) := by
      rintro ⟨a, rfl⟩
      exact hi a.property
    simp only [freezePolynomial, aeval_X, frozenCoordinate, dite_eq_right hi,
      Pi.zero_apply, map_zero, killCompl, aeval_X, dite_eq_right hrange]

theorem longChart_frozen_top_eval_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (r : ℕ)
    (hdegree : ∀ j, (β j).totalDegree ≤ r)
    (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ α : {i // keep i} →₀ ℕ, α.degree = r →
      (fun j => (((β j).coeff (α.mapDomain Subtype.val) : ℤ) : ℝ)) ∈ K)
    (x : {i // keep i} → ℝ) :
    (fun j => MvPolynomial.eval x (homogeneousComponent r
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))))) ∈ K := by
  have htop (j : J) : homogeneousComponent r
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))) =
      killCompl (Subtype.val_injective (p := keep))
        (homogeneousComponent r (MvPolynomial.map (Int.castRingHom ℝ) (β j))) := by
    rw [freezePolynomial_map, freezePolynomial_top keep _
      ((totalDegree_map_le _ _).trans (hdegree j)), longChart_freezePolynomial_zero_eq_killCompl]
  simp only [htop]
  exact longChart_top_eval_mem β (Function.Embedding.subtype keep) r K hcoeff x

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

theorem polynomialFamily_freeze_coeff_mem {I J R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (keep : I → Prop)
    (fixed : {i // ¬ keep i} → R) (K : Submodule R (J → R))
    (hP : ∀ d, (∃ i, keep i ∧ d i ≠ 0) → (fun j => (P j).coeff d) ∈ K)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (fun j => (freezePolynomial keep fixed (P j)).coeff α) ∈ K := by
  classical
  let S : Finset (I →₀ ℕ) := Finset.univ.biUnion (fun j => (P j).support)
  let c (d : I →₀ ℕ) : R := (freezePolynomial keep fixed (monomial d 1)).coeff α
  have hm (d : I →₀ ℕ) (r : R) :
      (freezePolynomial keep fixed (monomial d r)).coeff α = c d * r := by
    have hr : monomial d r = r • monomial d (1 : R) := by
      simp only [smul_monomial, smul_eq_mul, mul_one]
    rw [hr, map_smul, coeff_smul]
    exact mul_comm r (c d)
  have he (j : J) : (freezePolynomial keep fixed (P j)).coeff α =
      ∑ d ∈ S, c d * (P j).coeff d := by
    conv_lhs => rw [← (P j).support_sum_monomial_coeff, map_sum, coeff_sum]
    simp only [hm]
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hd⟩
    · intro d _ hd
      have hz : (P j).coeff d = 0 := by
        simpa only [mem_support_iff, not_not] using hd
      rw [hz, mul_zero]
  have he' : (fun j => (freezePolynomial keep fixed (P j)).coeff α) =
      ∑ d ∈ S, c d • (fun j => (P j).coeff d) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he j
  rw [he']
  apply K.sum_mem
  intro d _
  by_cases hd : ∃ i, keep i ∧ d i ≠ 0
  · exact K.smul_mem _ (hP d hd)
  · have hc : c d = 0 :=
      freezePolynomial_monomial_coeff_eq_zero_of_no_keep keep fixed d hd α hα
    rw [hc, zero_smul]
    exact K.zero_mem

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem sub_projected_anchor_mem {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (K : Submodule R V) (L : V →ₗ[R] V) (hL : ∀ v, L v ∈ K)
    {v a : V} (h : v - a ∈ K) : v - (a - L a) ∈ K := by
  have he : v - (a - L a) = (v - a) + L a := by abel
  rw [he]
  exact K.add_mem h (hL a)

theorem polynomialFamily_eval_sub_zero_mem {J I R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (K : Submodule R (J → R))
    (hP : ∀ d, d ≠ 0 → (fun j => (P j).coeff d) ∈ K) (x : I → R) :
    (fun j => eval x (P j) - eval (0 : I → R) (P j)) ∈ K := by
  classical
  have h := polynomialFamily_eval_mem
    (fun j => P j - C (constantCoeff (P j))) K (fun d => ?_) x
  · simpa only [map_sub, eval_C, eval_zero] using h
  · by_cases hd : d = 0
    · subst d
      simp only [coeff_sub, coeff_C, ↓reduceIte, constantCoeff_eq, sub_self]
      exact K.zero_mem
    · simpa [coeff_C, Ne.symm hd] using hP d hd

theorem polynomialFamily_linearMap_eval_eq_zero {J I R V : Type*} [Fintype J]
    [CommRing R] [AddCommGroup V] [Module R V]
    (P : J → MvPolynomial I R) (K : Submodule R (J → R))
    (hP : ∀ d, d ≠ 0 → (fun j => (P j).coeff d) ∈ K)
    (Q : (J → R) →ₗ[R] V) (hQ : K ≤ LinearMap.ker Q) (x : I → R) :
    Q (fun j => eval x (P j)) = Q (fun j => eval (0 : I → R) (P j)) := by
  have h := hQ (polynomialFamily_eval_sub_zero_mem P K hP x)
  change Q ((fun j => eval x (P j)) - (fun j => eval (0 : I → R) (P j))) = 0 at h
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

theorem polynomialFamily_quotient_eval_eq_zero {J I R : Type*} [Fintype J] [CommRing R]
    (P : J → MvPolynomial I R) (K : Submodule R (J → R))
    (hP : ∀ d, d ≠ 0 → (fun j => (P j).coeff d) ∈ K) (x : I → R) :
    K.mkQ (fun j => eval x (P j)) = K.mkQ (fun j => eval (0 : I → R) (P j)) := by
  apply polynomialFamily_linearMap_eval_eq_zero P K hP K.mkQ
  simp only [Submodule.ker_mkQ, le_refl]

theorem frozenPolynomialFamily_coeff_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (((β j).coeff d : ℤ) : ℝ)) ∈ K)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    (fun j =>
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))).coeff α) ∈ K := by
  have hreal : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (MvPolynomial.map (Int.castRingHom ℝ) (β j)).coeff d) ∈ K := by
    intro d hd
    simpa only [coeff_map, Int.coe_castRingHom] using hcoeff d hd
  have h := polynomialFamily_freeze_coeff_mem
    (fun j => MvPolynomial.map (Int.castRingHom ℝ) (β j)) keep
    (fun i => (fixed i : ℝ)) K hreal α hα
  simpa only [freezePolynomial_map, Int.coe_castRingHom] using h

theorem frozenPolynomialFamily_eval_sub_zero_mem {J Full : Type*} [Fintype J]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (((β j).coeff d : ℤ) : ℝ)) ∈ K)
    (x : {i // keep i} → ℝ) :
    (fun j => eval x
        (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j))) -
      eval (0 : {i // keep i} → ℝ)
        (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j)))) ∈ K := by
  exact polynomialFamily_eval_sub_zero_mem _ K
    (frozenPolynomialFamily_coeff_mem β keep fixed K hcoeff) x

theorem frozenPolynomialFamily_linearMap_eval_eq_zero {J Full V : Type*} [Fintype J]
    [AddCommGroup V] [Module ℝ V]
    (β : J → MvPolynomial Full ℤ) (keep : Full → Prop)
    (fixed : {i // ¬ keep i} → ℤ) (K : Submodule ℝ (J → ℝ))
    (hcoeff : ∀ d, (∃ i, keep i ∧ d i ≠ 0) →
      (fun j => (((β j).coeff d : ℤ) : ℝ)) ∈ K)
    (Q : (J → ℝ) →ₗ[ℝ] V) (hQ : K ≤ LinearMap.ker Q)
    (x : {i // keep i} → ℝ) :
    Q (fun j => eval x
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j)))) =
    Q (fun j => eval (0 : {i // keep i} → ℝ)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed (β j)))) := by
  exact polynomialFamily_linearMap_eval_eq_zero _ K
    (frozenPolynomialFamily_coeff_mem β keep fixed K hcoeff) Q hQ x

end Erdos3

end

end OAI
