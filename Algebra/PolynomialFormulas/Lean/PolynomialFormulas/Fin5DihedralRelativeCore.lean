import PolynomialFormulas.Fin5DihedralCore

/-!
# Relative-index interface for the standard `C₅`/`D₅`/`F₂₀` chain

This small module extends `Fin5DihedralCore` with exactly the inclusion and
relative-index facts needed by the Section 5 two-coset resolvents.  It does
not import or use the classification of transitive subgroups of `S₅`.
-/

namespace LeanProofs.PolynomialFormulas.Fin5DihedralRelativeCore

open Subgroup

export LeanProofs.PolynomialFormulas.Fin5DihedralCore
  (S5 mem_standardD5_iff reflection reflection_mem_standardD5 standardC5
    standardC5_le_standardD5 standardD5)
export LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral.Classification
  (standardF20_inf_standardA5_eq_standardD5)

abbrev standardF20 : Subgroup S5 := Fin5Solvable.standardF20
abbrev standardA5 : Subgroup S5 :=
  alternatingGroup (Fin 5)

theorem standardD5_le_standardF20 : standardD5 ≤ standardF20 := by
  intro g hg
  have hg' : g ∈ standardF20 ⊓ standardA5 := by
    rw [standardF20_inf_standardA5_eq_standardD5]
    exact hg
  exact hg'.1

theorem relIndex_standardC5_standardD5 :
    standardC5.relIndex standardD5 = 2 := by
  have hcardSub :
      Nat.card (standardC5.subgroupOf standardD5) = 5 := by
    calc
      Nat.card (standardC5.subgroupOf standardD5) = Nat.card standardC5 :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe standardC5_le_standardD5).toEquiv
      _ = 5 := Fin5Solvable.natCard_standardC5
  have h := (standardC5.subgroupOf standardD5).index_mul_card
  change standardC5.relIndex standardD5 *
      Nat.card (standardC5.subgroupOf standardD5) = Nat.card standardD5 at h
  rw [hcardSub, Fin5DihedralCore.natCard_standardD5] at h
  omega

theorem relIndex_standardD5_standardF20 :
    standardD5.relIndex standardF20 = 2 := by
  have hcardSub :
      Nat.card (standardD5.subgroupOf standardF20) = 10 := by
    calc
      Nat.card (standardD5.subgroupOf standardF20) = Nat.card standardD5 :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe standardD5_le_standardF20).toEquiv
      _ = 10 := Fin5DihedralCore.natCard_standardD5
  have h := (standardD5.subgroupOf standardF20).index_mul_card
  change standardD5.relIndex standardF20 *
      Nat.card (standardD5.subgroupOf standardF20) = Nat.card standardF20 at h
  rw [hcardSub, Fin5TransitiveC5.natCard_standardF20] at h
  omega

end LeanProofs.PolynomialFormulas.Fin5DihedralRelativeCore
