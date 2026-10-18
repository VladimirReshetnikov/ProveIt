import GowersSzemeredi.Proofs05Downstream
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.MeanInequalities

/-!
# Global polynomial phase removal (Lemma 5.14)

This module assembles the local refinements constructed in
`Proofs05Downstream` over every cell of an input partition.  The dependent
families of local cells are flattened through a sigma type, and Jensen's
inequality supplies the sharp global cell-count exponent.

The final result remains conditional on `corollary_5_6`: that is precisely
the outstanding analytic input used by the local refinement theorem.

`lemma_5_14_holds_of_corollary_5_6` is in `Proofs05Lemma14Side`, outside the
final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Flattening dependent families of refinements -/

/-- The canonical finite reindexing of a dependent family of finite types. -/
noncomputable def section5FlattenEquiv {M : Nat} (L : Fin M → Nat) :
    (Σ i : Fin M, Fin (L i)) ≃ Fin (∑ i, L i) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Flatten a dependent family of modular progressions to one `Fin`-indexed
family, without adding any padding cells. -/
noncomputable def section5Flatten {N M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → ModAP N) :
    Fin (∑ i, L i) → ModAP N := fun j =>
  let z := (section5FlattenEquiv L).symm j
  R z.1 z.2

/-- Flattening local partitions gives a partition of the original union. -/
theorem section5Flatten_partition {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N)
    (L : Fin M → Nat) (R : (i : Fin M) → Fin (L i) → ModAP N)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hR : ∀ i, IsPartition (fun j ↦ (R i j).carrier) (Q i).carrier) :
    IsPartition (fun j ↦ (section5Flatten L R j).carrier) Finset.univ := by
  let e := section5FlattenEquiv L
  have hsigma := IsPartition.sigma L (fun i ↦ (Q i).carrier)
    Finset.univ (fun i j ↦ (R i j).carrier) hQ hR
  constructor
  · intro x
    rw [hsigma.1 x]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨e z, ?_⟩
      change x ∈
        (R ((section5FlattenEquiv L).symm (section5FlattenEquiv L z)).1
          ((section5FlattenEquiv L).symm (section5FlattenEquiv L z)).2).carrier
      rw [(section5FlattenEquiv L).symm_apply_apply z]
      exact hz
    · rintro ⟨j, hj⟩
      refine ⟨e.symm j, ?_⟩
      simpa only [section5Flatten, e] using hj
  · intro i j hij
    have hij' : i ≠ j := bne_iff_ne.mp hij
    have hpre : e.symm i ≠ e.symm j := fun h => hij' (e.symm.injective h)
    simpa only [section5Flatten, e] using
      hsigma.2 (e.symm i) (e.symm j) (bne_iff_ne.mpr hpre)

/-- The flattened partition refines the original family cell by cell. -/
theorem section5Flatten_refinement {N M : Nat} [NeZero N]
    (Q : Fin M → ModAP N)
    (L : Fin M → Nat) (R : (i : Fin M) → Fin (L i) → ModAP N)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hR : ∀ i, IsPartition (fun j ↦ (R i j).carrier) (Q i).carrier) :
    IsRefinement (fun j ↦ (section5Flatten L R j).carrier)
      (fun i ↦ (Q i).carrier) := by
  have hflat := section5Flatten_partition Q L R hQ hR
  refine ⟨fun x ↦ (hflat.1 x).symm.trans (hQ.1 x), ?_, hflat.2⟩
  intro j
  let z := (section5FlattenEquiv L).symm j
  refine ⟨z.1, ?_⟩
  simpa only [section5Flatten, z] using
    (IsPartition.cell_subset (hR z.1) z.2)

/-- Properness is preserved by dependent-family flattening. -/
theorem section5Flatten_isProper {N M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → ModAP N)
    (hR : ∀ i j, (R i j).IsProper) :
    ∀ j, (section5Flatten L R j).IsProper := by
  intro j
  let z := (section5FlattenEquiv L).symm j
  simpa only [section5Flatten, z] using hR z.1 z.2

/-- Sums over a flattened family are the corresponding iterated sums. -/
theorem section5Flatten_sum {N M : Nat} (L : Fin M → Nat)
    (R : (i : Fin M) → Fin (L i) → ModAP N)
    {A : Type*} [AddCommMonoid A] (F : ModAP N → A) :
    ∑ j, F (section5Flatten L R j) = ∑ i, ∑ j, F (R i j) := by
  let e := section5FlattenEquiv L
  calc
    ∑ j, F (section5Flatten L R j) =
        ∑ z : Σ i : Fin M, Fin (L i), F (section5Flatten L R (e z)) :=
      (e.sum_comp _).symm
    _ = ∑ z : Σ i : Fin M, Fin (L i), F (R z.1 z.2) := by
      apply Finset.sum_congr rfl
      intro z _hz
      change F (R ((section5FlattenEquiv L).symm
        (section5FlattenEquiv L z)).1
        ((section5FlattenEquiv L).symm (section5FlattenEquiv L z)).2) =
          F (R z.1 z.2)
      exact congrArg (fun w : Σ i : Fin M, Fin (L i) ↦ F (R w.1 w.2))
        ((section5FlattenEquiv L).symm_apply_apply z)
    _ = ∑ i, ∑ j, F (R i j) := Fintype.sum_sigma _

/-! ### The global cell-count estimate -/

/-- Hölder's inequality (weights `1`, exponents `K` and `K / (K - 1)`) in exactly the form needed
to aggregate local cell counts. -/
theorem section5_sum_rpow_le {M N K : Nat} (hK : 0 < K)
    (m : Fin M → Nat) (hsum : ∑ i, m i = N) :
    ∑ i, (m i : Real) ^ (1 - (K : Real)⁻¹) ≤
      (M : Real) ^ (K : Real)⁻¹ *
        (N : Real) ^ (1 - (K : Real)⁻¹) := by
  rcases Nat.lt_or_ge 1 K with hK1 | hK1
  · have hKr : (1 : Real) < K := by exact_mod_cast hK1
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := univ) (Real.HolderConjugate.conjExponent hKr)
      (f := fun _ => (1 : Real)) (g := fun i => (m i : Real) ^ (1 - (K : Real)⁻¹))
      (fun _ _ => zero_le_one) (fun i _ => by positivity)
    have hK1r : (K : Real) - 1 ≠ 0 := by linarith
    have he : (1 - (K : Real)⁻¹) * Real.conjExponent K = 1 := by
      unfold Real.conjExponent; field_simp
    have hq : 1 / Real.conjExponent K = 1 - (K : Real)⁻¹ := by
      unfold Real.conjExponent; field_simp
    simp only [one_mul, Real.one_rpow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ← Real.rpow_mul (Nat.cast_nonneg _), he, Real.rpow_one] at h
    calc _ ≤ _ := h
      _ = _ := by
        rw [hq, one_div]
        exact_mod_cast congrArg (fun x : Nat => (M : Real) ^ (K : Real)⁻¹ *
          (x : Real) ^ (1 - (K : Real)⁻¹)) hsum
  · obtain rfl : K = 1 := by omega
    simp

end LeanProofs.GowersSzemeredi
