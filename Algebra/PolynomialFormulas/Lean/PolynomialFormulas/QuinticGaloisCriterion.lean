import PolynomialFormulas.SolvableGaloisRadicals
import PolynomialFormulas.AbelRuffini
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The Galois criterion for irreducible rational quintics

Mathlib's Abel--Ruffini development supplies the direction from a radical
root of an irreducible polynomial to solvability of its Galois group.  The
converse follows from `solvable_galois_over_rat_le_solvableByRad`: realize the
splitting field inside `ℂ`, transfer solvability across the canonical
splitting-field equivalence, and include every root in that field.
-/

open Polynomial IntermediateField

namespace LeanProofs.PolynomialFormulas

theorem completelySolvableByRadicals_iff_gal_isSolvable_of_irreducible
    {p : ℚ[X]} (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    CompletelySolvableByRadicals p ↔ IsSolvable p.Gal := by
  constructor
  · intro hrad
    have hp0 : p ≠ 0 := hp.ne_zero
    have hmap0 : p.map (algebraMap ℚ ℂ) ≠ 0 := map_ne_zero hp0
    have hmapNatDegree : (p.map (algebraMap ℚ ℂ)).natDegree = 5 := by
      rw [Polynomial.natDegree_map_eq_of_injective
        (algebraMap ℚ ℂ).injective p, hdeg]
    have hmapDegree : (p.map (algebraMap ℚ ℂ)).degree ≠ 0 := by
      rw [degree_eq_natDegree hmap0, hmapNatDegree]
      norm_num
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_root (p.map (algebraMap ℚ ℂ)) hmapDegree
    have hxaeval : aeval x p = 0 := by
      simpa [Polynomial.IsRoot, aeval_def] using hx
    have hxset : x ∈ p.rootSet ℂ := (mem_rootSet_of_ne hp0).2 hxaeval
    exact isSolvable_gal_of_irreducible (hrad ⟨x, hxset⟩) hp
      (aeval_eq_zero_of_mem_rootSet hxset)
  · intro hsolv
    let L : IntermediateField ℚ ℂ :=
      IntermediateField.adjoin ℚ (p.rootSet ℂ)
    letI : Fact ((p.map (algebraMap ℚ ℂ)).Splits) :=
      ⟨IsAlgClosed.splits _⟩
    letI : p.IsSplittingField ℚ L :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    letI : FiniteDimensional ℚ L := IsSplittingField.finiteDimensional L p
    letI : IsGalois ℚ L :=
      IsGalois.of_separable_splitting_field hp.separable
    let e : Gal(L/ℚ) ≃* p.Gal :=
      (IsSplittingField.algEquiv L p).autCongr
    letI : IsSolvable Gal(L/ℚ) :=
      solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    have hL : L ≤ solvableByRad ℚ ℂ :=
      solvable_galois_over_rat_le_solvableByRad L
    intro x
    exact hL (IntermediateField.subset_adjoin ℚ (p.rootSet ℂ) x.property)

end LeanProofs.PolynomialFormulas
