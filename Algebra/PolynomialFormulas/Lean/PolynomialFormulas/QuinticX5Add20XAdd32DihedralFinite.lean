import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic
import PolynomialFormulas.FrobeniusDummitResolvent

/-!
# The explicit dihedral subgroup used by `X^5 + 20 X + 32`

This small module isolates the comparatively expensive ordinary-kernel
finite computations on `S₅`.  Its executable table has exactly the affine
maps `x ↦ ±x+a`; closure and the intersection with `A₅` are checked by
`decide`, with no native-code oracle.
-/

namespace LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral
namespace Classification

open Equiv Subgroup

abbrev S5 := Fin5Solvable.S5
abbrev fiveCycle : S5 := Fin5Solvable.fiveCycle
abbrev standardF20 : Subgroup S5 := Fin5Solvable.standardF20
abbrev standardA5 : Subgroup S5 := alternatingGroup (Fin 5)
abbrev multiplierTwo : S5 := FrobeniusDummitResolvent.multiplierTwo
abbrev f20Elements : Finset S5 := Fin5TransitiveC5.f20Elements

theorem mem_f20Elements_iff (g : S5) :
    g ∈ f20Elements ↔ g ∈ standardF20 :=
  Fin5TransitiveC5.mem_f20Elements_iff g

/-- The reflection `x ↦ -x` in the affine realization of `F₂₀`. -/
def reflection : S5 := multiplierTwo ^ 2

/-- The ten affine permutations `x ↦ ±x+a`. -/
def d5Element (ab : Fin 5 × Fin 2) : S5 :=
  fiveCycle ^ (ab.1 : ℕ) * reflection ^ (ab.2 : ℕ)

def d5Elements : Finset S5 :=
  Finset.univ.image d5Element

set_option maxRecDepth 100000 in
theorem card_d5Elements : d5Elements.card = 10 := by
  decide

set_option maxRecDepth 100000 in
theorem one_mem_d5Elements : (1 : S5) ∈ d5Elements := by
  decide

set_option maxRecDepth 100000 in
theorem d5Elements_mul_closed :
    ∀ a b : S5, a ∈ d5Elements → b ∈ d5Elements → a * b ∈ d5Elements := by
  decide

set_option maxRecDepth 100000 in
theorem d5Elements_inv_closed :
    ∀ a : S5, a ∈ d5Elements → a⁻¹ ∈ d5Elements := by
  decide

/-- The standard dihedral subgroup, with an executable ten-element carrier. -/
def standardD5 : Subgroup S5 where
  carrier := {g | g ∈ d5Elements}
  one_mem' := one_mem_d5Elements
  mul_mem' := by
    intro a b ha hb
    exact d5Elements_mul_closed a b ha hb
  inv_mem' := by
    intro a ha
    exact d5Elements_inv_closed a ha

@[simp] theorem mem_standardD5_iff (g : S5) :
    g ∈ standardD5 ↔ g ∈ d5Elements :=
  Iff.rfl

noncomputable def standardD5EquivElements :
    standardD5 ≃ {g : S5 // g ∈ d5Elements} where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_standardD5 : Nat.card standardD5 = 10 := by
  rw [Nat.card_congr standardD5EquivElements]
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using
    card_d5Elements

/-- Inside the standard Frobenius group, the even permutations are exactly
the standard dihedral subgroup. -/
theorem standardF20_inf_standardA5_eq_standardD5 :
    standardF20 ⊓ standardA5 = standardD5 := by
  set_option maxRecDepth 100000 in
    ext g
    simp only [Subgroup.mem_inf, ← mem_f20Elements_iff,
      Equiv.Perm.mem_alternatingGroup, mem_standardD5_iff]
    revert g
    decide

/-- `H` is an inner conjugate of `K`. -/
def IsConjugateTo (H K : Subgroup S5) : Prop :=
  ∃ g : S5, K.map (MulAut.conj g).toMonoidHom = H

theorem natCard_eq_of_isConjugateTo {H K : Subgroup S5}
    (h : IsConjugateTo H K) : Nat.card H = Nat.card K := by
  obtain ⟨g, hg⟩ := h
  calc
    Nat.card H = Nat.card (K.map (MulAut.conj g).toMonoidHom) := by
      rw [hg]
    _ = Nat.card K :=
      Subgroup.card_map_of_injective (K := K) (MulAut.conj g).injective

end Classification
end LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral
