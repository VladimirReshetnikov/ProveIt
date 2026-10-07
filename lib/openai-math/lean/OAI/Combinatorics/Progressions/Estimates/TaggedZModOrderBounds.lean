import OAI.Combinatorics.Progressions.Fourier.FiniteCharacterOrderTail

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def taggedIntegerResidue {Tag : Type*} (J : Tag → Type*) (N : ℕ) :
    ((Sigma J) → ℤ) →+ (∀ h : Tag, J h → ZMod N) where
  toFun x h j := (x ⟨h, j⟩ : ZMod N)
  map_zero' := by ext h j; simp
  map_add' := by intro x y; ext h j; simp

theorem taggedIntegerResidue_surjective {Tag : Type*} (J : Tag → Type*) (N : ℕ) :
    Function.Surjective (taggedIntegerResidue J N) := by
  intro y
  choose x hx using fun s : Sigma J => ZMod.intCast_surjective (y s.1 s.2)
  exact ⟨x, funext fun h => funext fun j => hx ⟨h, j⟩⟩

variable {Tag X : Type*} [Fintype Tag] [Fintype X]
  (J : Tag → Type*) [∀ h, Fintype (J h)] (N : ℕ) [NeZero N]

theorem taggedZMod_boundedOrder_card_le (T : ℕ) :
    (Finset.univ.filter
      (fun χ : AddChar (∀ h : Tag, J h → ZMod N) ℂ => orderOf χ ≤ T)).card ≤
        T ^ (Fintype.card (Sigma J) + 1) :=
  finiteCharacter_boundedOrder_card_le (taggedIntegerResidue J N)
    (taggedIntegerResidue_surjective J N) T

theorem taggedZModImage_boundedOrder_coefficient_mass (p : FiniteProbabilityWeights X)
    (Y : X → ∀ h : Tag, J h → ZMod N) (T : ℕ) :
    (∑ χ ∈ Finset.univ.filter
      (fun χ : AddChar (∀ h : Tag, J h → ZMod N) ℂ => orderOf χ ≤ T),
      ‖finiteImageCharacteristic p Y χ‖) ≤ (T : ℝ) ^ (Fintype.card (Sigma J) + 1) :=
  finiteImage_boundedOrder_coefficient_mass (taggedIntegerResidue J N)
    (taggedIntegerResidue_surjective J N) p Y T

theorem taggedZModImage_order_bounds (p : FiniteProbabilityWeights X)
    (Y : X → ∀ h : Tag, J h → ZMod N)
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (∀ h : Tag, J h → ZMod N) ℂ,
      ‖finiteImageCharacteristic p Y χ‖ ≤ C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) :
    let S := Finset.univ.filter
      (fun χ : AddChar (∀ h : Tag, J h → ZMod N) ℂ => orderOf χ ≤ T)
    (∀ z, (Fintype.card (∀ h : Tag, J h → ZMod N) : ℝ) * finiteImageMass p Y z ≤ 1 + C) ∧
    S.card ≤ T ^ (Fintype.card (Sigma J) + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic p Y χ‖) ≤
      (T : ℝ) ^ (Fintype.card (Sigma J) + 1) ∧
    ∀ z, ‖(Fintype.card (∀ h : Tag, J h → ZMod N) : ℂ) * finiteImageMass p Y z -
      ∑ χ ∈ S, finiteImageCharacteristic p Y χ * star (χ z)‖ ≤ C / T := by
  have hd := finiteCharacter_integer_decay_of_rpow (I := Sigma J) hC hP _ hdecay
  let π := taggedIntegerResidue J N
  have hπ : Function.Surjective π := taggedIntegerResidue_surjective J N
  exact ⟨fun z => finiteImage_density_bound_of_order_decay π hπ p Y hC hd z,
    finiteCharacter_boundedOrder_card_le π hπ T,
    finiteImage_boundedOrder_coefficient_mass π hπ p Y T,
    fun z => finiteImage_density_order_truncation π hπ p Y hC hd T hT z⟩

end Erdos3

end

end OAI
