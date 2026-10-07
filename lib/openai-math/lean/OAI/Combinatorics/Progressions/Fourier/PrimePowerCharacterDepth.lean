import OAI.Combinatorics.Progressions.Estimates.FiniteProductImageDecay

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem primePower_character_tag_depth_max
    {Tag : Type*} [Fintype Tag] [DecidableEq Tag] [Nonempty Tag]
    {H : Tag → Type*} [∀ j, AddCommGroup (H j)]
    {p a : ℕ} (hp : p.Prime) (χ : AddChar (∀ j, H j) ℂ)
    (depth : Tag → ℕ)
    (hcoord : ∀ j, orderOf (finiteProductCharacterCoordinate χ j) = p ^ depth j)
    (horder : orderOf χ = p ^ a) :
    (∀ j, depth j ≤ a) ∧ ∃ j, depth j = a := by
  classical
  have hpow : χ ^ (p ^ a) = 1 := by rw [← horder]; exact pow_orderOf_eq_one χ
  have hcoordPow (j : Tag) : (finiteProductCharacterCoordinate χ j) ^ (p ^ a) = 1 := by
    ext x
    exact congrArg (fun ψ : AddChar (∀ j, H j) ℂ => ψ (Pi.single j x)) hpow
  have hdepth (j : Tag) : depth j ≤ a := by
    have hdvd := orderOf_dvd_of_pow_eq_one (hcoordPow j)
    rw [hcoord j] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  refine ⟨hdepth, ?_⟩
  by_cases ha : a = 0
  · obtain ⟨j⟩ := ‹Nonempty Tag›
    exact ⟨j, by have := hdepth j; omega⟩
  by_contra! hmax
  have hsmall (j : Tag) : depth j ≤ a - 1 := by have := hdepth j; have := hmax j; omega
  have hkilled (j : Tag) : (finiteProductCharacterCoordinate χ j) ^ (p ^ (a - 1)) = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hcoord j]
    exact pow_dvd_pow p (hsmall j)
  have hkill : χ ^ (p ^ (a - 1)) = 1 := by
    rw [← finiteProductCharacter_decomposition χ, ← map_pow]
    have hpi : (finiteProductCharacterCoordinate χ) ^ (p ^ (a - 1)) = 1 := by
      funext j
      exact hkilled j
    rw [hpi, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hkill
  rw [horder] at hdvd
  have hle := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  omega

end Erdos3

end

end OAI
