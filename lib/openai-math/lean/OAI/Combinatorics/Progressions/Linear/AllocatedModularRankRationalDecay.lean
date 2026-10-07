import OAI.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

theorem allocatedCongruence_crt_rational_decay_of_bad_product
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C) (R : ℕ)
    (hbad : (∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p.val) ≤ R)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ)
    (origin : ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X E inactive) →
      ZMod (∏ p : P, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq P := Classical.decEq _
    ‖finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := LayerSamplerLongVariables inactive G B)
        (fun p : P => p.val) (fun p : P => A p.val))
      (fun x j => (crtPrimePowerIntegerPolynomialOutput (fun p : P => p.val) (fun p : P => A p.val)
        (fun p : P => e p.val)
        (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective)
        (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v)
        origin x j : ZMod (∏ p : P, p.val ^ A p.val))) χ‖ ≤
      ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  let : DecidableEq P := Classical.decEq _
  let b := allocatedCongruenceBadDepth inactive noise r projection spatial kernel block P A C
  have h := crt_integer_polynomial_rational_characteristic_decay hm
    (fun p : P => p.val) (fun p : P => A p.val) (fun p : P => b p.val) (fun p : P => e p.val)
    (fun p => hp p.val p.property) Subtype.val_injective C hC
    (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v)
    (fun j o => allocatedCongruenceIntegerPolynomial_degree inactive j base noise r (projection j) v o)
    (fun p a ha hA j w hw =>
      allocatedCongruenceIntegerPolynomial_rank_of_good inactive noise r projection spatial kernel block
        P C p a (allocatedCongruence_largest_bad_depth_good inactive noise r projection spatial kernel block
          P A C p a ha hA) base v j w hw) origin χ
  exact h.trans (mul_le_mul_of_nonneg_right
    (crtPolynomialCharge_le_of_bad_product (fun p : P => p.val) (fun p : P => b p.val)
      (fun p : P => e p.val) m hC hbad) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end Erdos3.VectorPolynomial

end

end OAI
