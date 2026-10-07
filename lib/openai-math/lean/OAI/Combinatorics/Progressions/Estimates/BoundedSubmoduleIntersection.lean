/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (b : Basis ι ℚ L)

noncomputable def coordinateArraySpan (m : ℕ) (c : Fin m × ι → ℚ) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range fun a : Fin m => b.equivFun.symm (fun i => c (a, i)))

noncomputable def heightBoundedSubspaces (m H : ℕ) : Set (Submodule ℚ L) :=
  coordinateArraySpan b m '' {c : Fin m × ι → ℚ | ∀ z, RationalHeightLE (c z) H}

theorem mem_heightBoundedSubspaces (m H : ℕ) (U : Submodule ℚ L) :
    U ∈ heightBoundedSubspaces b m H ↔
      ∃ v : Fin m → L, Submodule.span ℚ (Set.range v) = U ∧
        ∀ a i, RationalHeightLE (b.repr (v a) i) H := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun a => b.equivFun.symm (fun i => c (a, i)), rfl, ?_⟩
    intro a i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hc (a, i)
  · rintro ⟨v, hv, hh⟩
    refine ⟨fun z => b.repr (v z.1) z.2, (fun z => hh z.1 z.2), ?_⟩
    have he : (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i)) = v := by
      funext a
      apply b.equivFun.injective
      simp only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply]
    change Submodule.span ℚ (Set.range (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i))) = U
    rw [he, hv]

theorem finite_card_heightBoundedSubspaces (m H : ℕ) :
    (heightBoundedSubspaces b m H).Finite ∧
      (heightBoundedSubspaces b m H).ncard ≤ ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  let S : Set (Fin m × ι → ℚ) := {c | ∀ z, RationalHeightLE (c z) H}
  obtain ⟨hfin, hcard⟩ := finite_card_bounded_height_arrays S H (fun _ hc => hc)
  refine ⟨hfin.image (coordinateArraySpan b m), ?_⟩
  have hh := (Set.ncard_image_le (f := coordinateArraySpan b m) hfin).trans hcard
  rw [Fintype.card_prod, Fintype.card_fin] at hh
  exact hh

section Lie

variable {A : Type*} [LieRing A] [LieAlgebra ℚ A] (e : Basis ι ℚ A)

noncomputable def heightBoundedLieSubalgebras (m H : ℕ) : Set (LieSubalgebra ℚ A) :=
  {K | K.toSubmodule ∈ heightBoundedSubspaces e m H}

theorem finite_card_heightBoundedLieSubalgebras (m H : ℕ) :
    (heightBoundedLieSubalgebras e m H).Finite ∧
      (heightBoundedLieSubalgebras e m H).ncard ≤
        ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  classical
  obtain ⟨hfin, hcard⟩ := finite_card_heightBoundedSubspaces e m H
  let f : heightBoundedLieSubalgebras e m H → heightBoundedSubspaces e m H :=
    fun K => ⟨K.val.toSubmodule, K.property⟩
  have hf : Function.Injective f := by
    intro K J h
    exact Subtype.ext (LieSubalgebra.toSubmodule_injective (congrArg Subtype.val h))
  let : Fintype (heightBoundedSubspaces e m H) := hfin.fintype
  let : Finite (heightBoundedLieSubalgebras e m H) := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  refine ⟨Set.toFinite _, ?_⟩
  exact (show (heightBoundedLieSubalgebras e m H).ncard ≤ (heightBoundedSubspaces e m H).ncard by
    simpa only [Nat.card_coe_set_eq] using hc).trans hcard

end Lie
end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (e : Basis ι ℚ L) (K : Submodule ℚ L)

theorem exists_bounded_submodule_ambient_spanning (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e K v hspan hv
  have hr : finrank ℚ K ≤ Fintype.card ι := by
    simpa only [finrank_eq_card_basis e] using K.finrank_le
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (finrank ℚ K)) :
      w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ = (b i : L) := by
    simp only [w, dite_eq_left i.isLt]
  refine ⟨w, ?_, ?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      dsimp only [w]
      split_ifs with ha
      · exact (b ⟨a.val, ha⟩).property
      · exact K.zero_mem
    · have htop : (⊤ : Submodule ℚ K) ≤
          (Submodule.span ℚ (Set.range w)).comap K.subtype := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        change (b i : L) ∈ Submodule.span ℚ (Set.range w)
        rw [← hw i]
        exact Submodule.subset_span ⟨_, rfl⟩
      intro x hx
      exact htop (show (⟨x, hx⟩ : K) ∈ (⊤ : Submodule ℚ K) by trivial)
  · intro a i
    dsimp only [w]
    split_ifs with ha
    · exact hb ⟨a.val, ha⟩ i
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH

theorem bounded_submodule_spanning_mem_candidates (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    K ∈ heightBoundedSubspaces e (Fintype.card ι) H := by
  obtain ⟨w, hw, hh⟩ := exists_bounded_submodule_ambient_spanning e K v hspan hH hv
  exact (mem_heightBoundedSubspaces e (Fintype.card ι) H K).mpr ⟨w, hw, hh⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_submodule_intersection_basis_logHeight
    {ι κ J V : Type*} [Fintype ι] [Fintype κ] [Fintype J]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : J → Submodule ℚ V) (v : J → κ → V)
    (hv : ∀ j, Submodule.span ℚ (Set.range (v j)) = U j)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hheight : ∀ j a i, rationalLogHeight (b.repr (v j a) i) ≤ p) :
    ∃ n : ℕ, n ≤ Fintype.card ι ∧ ∃ bw : Basis (Fin n) ℚ ↥(⨅ j, U j : Submodule ℚ V),
      ∀ a i, rationalLogHeight (b.repr (bw a : V) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 := by
  classical
  let A : J → Matrix ι κ ℚ := fun j i k => b.equivFun (v j k) i
  let W := ⨅ j, U j
  let Wc : Submodule ℚ (ι → ℚ) := ⨅ j, LinearMap.range (A j).mulVecLin
  have hA (j : J) : LinearMap.range (A j).mulVecLin = (U j).map b.equivFun.toLinearMap := by
    rw [← hv j, Submodule.map_span, ← Set.range_comp]
    exact Matrix.range_mulVecLin _
  have hmem (x : V) : b.equivFun x ∈ Wc ↔ x ∈ W := by
    simp only [Wc, W, Submodule.mem_iInf]
    constructor
    · intro hx j
      obtain ⟨y, hy, he⟩ := hA j ▸ hx j
      exact b.equivFun.injective he ▸ hy
    · intro hx j
      rw [hA j]
      exact ⟨x, hx j, rfl⟩
  let e : W ≃ₗ[ℚ] Wc :=
    { toFun := fun x => ⟨b.equivFun x, (hmem x).mpr x.property⟩
      invFun := fun x => ⟨b.equivFun.symm x, (hmem _).mp (by
        simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
      map_add' := fun x y => Subtype.ext (b.equivFun.map_add x y)
      map_smul' := fun c x => Subtype.ext (b.equivFun.map_smul c x)
      left_inv := fun x => Subtype.ext (b.equivFun.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (b.equivFun.apply_symm_apply x) }
  let q := (p + 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hp1q : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcols : ((∑ _j : J, Fintype.card κ : ℕ) : ℝ) ≤ q := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    have hprod := mul_le_mul hJ hκ (Nat.cast_nonneg _) hp
    dsimp [q]
    nlinarith
  obtain ⟨bc, hbc⟩ := exists_image_intersection_basis_exp_height A (one_le_ceil_exp p)
    (fun j i k => rationalHeightLE_ceil_exp (hheight j k i)) hq
    (hJ.trans hpq) (hι.trans hpq) hcols
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1q))
  refine ⟨finrank ℚ Wc, ?_, bc.map e.symm, ?_⟩
  · simpa using Submodule.finrank_le Wc
  · intro a i
    change rationalLogHeight (b.repr (b.equivFun.symm (bc a : ι → ℚ)) i) ≤ _
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact (rationalLogHeight_le_iff _ _).mpr (hbc a i)

end Erdos3

end

end OAI
