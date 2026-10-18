import GowersSzemeredi.Proofs05Downstream
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Fintype.EquivFin

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

/-- Jensen's inequality in exactly the form needed to aggregate local cell
counts. -/
theorem section5_sum_rpow_le {M N K : Nat} (hM : 0 < M) (hK : 0 < K)
    (m : Fin M → Nat) (hsum : ∑ i, m i = N) :
    ∑ i, (m i : Real) ^ (1 - (K : Real)⁻¹) ≤
      (M : Real) ^ (K : Real)⁻¹ *
        (N : Real) ^ (1 - (K : Real)⁻¹) := by
  let q : Real := (K : Real)⁻¹
  let p : Real := 1 - q
  have hKreal : (0 : Real) < K := by exact_mod_cast hK
  have hKone : (1 : Real) ≤ K := by exact_mod_cast hK
  have hq0 : 0 ≤ q := (inv_pos.mpr hKreal).le
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ hKone
  have hp0 : 0 ≤ p := by dsimp only [p]; linarith
  have hp1 : p ≤ 1 := by dsimp only [p]; linarith
  have hMreal : (0 : Real) < M := by exact_mod_cast hM
  have hweights : ∑ _i : Fin M, (M : Real)⁻¹ = 1 := by
    simp [ne_of_gt hMreal]
  have hsumReal : ∑ i, (m i : Real) = (N : Real) := by
    exact_mod_cast hsum
  have hjensen := (Real.concaveOn_rpow hp0 hp1).le_map_sum
    (t := (Finset.univ : Finset (Fin M)))
    (w := fun _i : Fin M ↦ (M : Real)⁻¹)
    (p := fun i : Fin M ↦ (m i : Real))
    (fun _i _hi ↦ (inv_pos.mpr hMreal).le) hweights
    (fun i _hi ↦ (show (0 : Real) ≤ m i by positivity))
  have hjensen' :
      (M : Real)⁻¹ * ∑ i, (m i : Real) ^ p ≤
        ((M : Real)⁻¹ * (N : Real)) ^ p := by
    simpa only [smul_eq_mul, Function.comp_apply, ← Finset.mul_sum, hsumReal]
      using hjensen
  have hscaled :
      ∑ i, (m i : Real) ^ p ≤
        (M : Real) * ((M : Real)⁻¹ * (N : Real)) ^ p := by
    calc
      ∑ i, (m i : Real) ^ p =
          (M : Real) * ((M : Real)⁻¹ * ∑ i, (m i : Real) ^ p) := by
        field_simp
      _ ≤ (M : Real) * ((M : Real)⁻¹ * (N : Real)) ^ p :=
        mul_le_mul_of_nonneg_left hjensen' hMreal.le
  calc
    ∑ i, (m i : Real) ^ (1 - (K : Real)⁻¹) =
        ∑ i, (m i : Real) ^ p := by rfl
    _ ≤ (M : Real) * ((M : Real)⁻¹ * (N : Real)) ^ p := hscaled
    _ = (M : Real) ^ q * (N : Real) ^ p := by
      rw [Real.mul_rpow (inv_nonneg.mpr hMreal.le)
        (show (0 : Real) ≤ N by positivity), Real.inv_rpow hMreal.le]
      have hMpow :
          (M : Real) * ((M : Real) ^ p)⁻¹ = (M : Real) ^ q := by
        calc
          (M : Real) * ((M : Real) ^ p)⁻¹ =
              (M : Real) ^ (1 : Real) * (M : Real) ^ (-p) := by
            rw [Real.rpow_one, Real.rpow_neg hMreal.le]
          _ = (M : Real) ^ ((1 : Real) + (-p)) :=
            (Real.rpow_add hMreal 1 (-p)).symm
          _ = (M : Real) ^ q := by
            congr 1
            dsimp only [p, q]
            ring
      calc
        (M : Real) * (((M : Real) ^ p)⁻¹ * (N : Real) ^ p) =
            ((M : Real) * ((M : Real) ^ p)⁻¹) * (N : Real) ^ p := by
          ring
        _ = (M : Real) ^ q * (N : Real) ^ p := by rw [hMpow]
    _ = (M : Real) ^ (K : Real)⁻¹ *
        (N : Real) ^ (1 - (K : Real)⁻¹) := by rfl

end LeanProofs.GowersSzemeredi
