import OAI.Combinatorics.Progressions.Lattices.FiniteUnchargedPrimeDensity
import OAI.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_character_order_reduction {J : Type*} [Fintype J]
    (N : ℕ) [NeZero N] (χ : AddChar (J → ZMod N) ℂ) :
    ∃ (hq : orderOf χ ∣ N) (ψ : AddChar (J → ZMod (orderOf χ)) ℂ),
      characterPullback (zmodPiReduction hq) ψ = χ := by
  have hann (x : J → ZMod N) : N • x = 0 := by
    ext j
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hq := finiteCharacter_order_dvd_of_annihilation N hann χ
  obtain ⟨ψ, hψ, _⟩ := exists_zmodPiReduction_character hq χ (pow_orderOf_eq_one χ)
  exact ⟨hq, ψ, hψ⟩

theorem character_integerTuple_congr_order {J : Type*} [Fintype J]
    (N : ℕ) [NeZero N] (χ : AddChar (J → ZMod N) ℂ) (x y : J → ℤ)
    (hxy : ∀ j, (x j : ZMod (orderOf χ)) = (y j : ZMod (orderOf χ))) :
    χ (fun j => (x j : ZMod N)) = χ (fun j => (y j : ZMod N)) := by
  obtain ⟨hq, ψ, hψ⟩ := exists_character_order_reduction N χ
  rw [← hψ]
  change ψ (fun j => ZMod.castHom hq (ZMod (orderOf χ)) (x j : ZMod N)) =
    ψ (fun j => ZMod.castHom hq (ZMod (orderOf χ)) (y j : ZMod N))
  simp only [map_intCast]
  congr 1
  exact funext hxy

theorem integerLongPolynomial_characteristic_inactive_congr
    {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (v w : I → ℤ)
    (hvw : ∀ i, (v i : ZMod (orderOf χ)) = (w i : ZMod (orderOf χ))) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly v N t j : ZMod N)) χ =
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly w N t j : ZMod N)) χ := by
  unfold finiteImageCharacteristic
  congr 1
  funext t
  apply character_integerTuple_congr_order
  intro j
  apply integerPolynomial_eval_congr
  funext a
  cases a with
  | inl a => rfl
  | inr i => exact hvw i

end Erdos3

end

end OAI
