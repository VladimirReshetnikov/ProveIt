import OAI.Combinatorics.Progressions.Lattices.FiniteUnchargedPrimeDensity
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem primePower_integer_polynomial_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (z : ∀ j, J j → ZMod (p ^ A)) :
    let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
    let Y := fun (x : V → ZMod (p ^ A)) j i => eval₂ (Int.castRingHom (ZMod (p ^ A))) x (F j i)
    |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 ∧
    (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z ≤
      1 + 2 / (p : ℝ) ^ 2 := by
  dsimp only
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) j i => eval₂ (Int.castRingHom (ZMod (p ^ A))) x (F j i)
  have hdecay (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (_hχ : χ ≠ 1) :
      ‖finiteImageCharacteristic law Y χ‖ ≤ (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
    have hlocal := primePower_polynomial_image_characteristic_decay hs p A 0 0 hp C hC
      (fun j i => map (Int.castRingHom (ZMod (p ^ A))) (F j i))
      (fun j i => (totalDegree_map_le _ _).trans (hF j i))
      (by
        intro B hB hBA j row hunit
        rw [primePowerHomogeneousRankProbability_integerPolynomial]
        exact hrank B hB hBA j row hunit)
      (fun _ => 0) χ
    simpa only [law, Y, eval_map, Nat.zero_add, pow_zero, Nat.cast_one, Real.one_rpow,
      one_mul, zero_add] using hlocal
  have hann (x : ∀ j, J j → ZMod (p ^ A)) : (p ^ A) • x = 0 := by
    ext j i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have h := finiteImage_uncharged_prime_density_rpow (taggedIntegerResidue J (p ^ A))
    (taggedIntegerResidue_surjective J (p ^ A)) hp hann law Y hP hdecay z
  have hd : |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 := by
    simpa only [← Nat.card_eq_fintype_card] using h
  exact ⟨hd, by linarith [(abs_le.mp hd).2]⟩

end Erdos3

end

end OAI
