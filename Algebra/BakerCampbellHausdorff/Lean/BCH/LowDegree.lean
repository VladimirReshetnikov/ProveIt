/-
# The homogeneous BCH components of degrees one to six

This file computes the first six homogeneous components `Zₙ(X, Y)` of the
BCH series, as defined in `BCH.Series` (`bchHom`), and shows that they are the
expressions displayed in the accompanying article (`docs/combined`,
Proposition 4.3, equations (4.9)–(4.14) and the associative expansions
(4.15)–(4.17)):

* `Z₁ = X + Y`;
* `Z₂ = ½ (XY - YX) = ½ [X, Y]`;
* `Z₃ = 1/12 (X²Y + XY² - 2XYX + Y²X + YX² - 2YXY) = 1/12 [X,[X,Y]] + 1/12 [Y,[Y,X]]`;
* `Z₄ = 1/24 (X²Y² - 2XYXY - Y²X² + 2YXYX) = -1/24 [Y,[X,[X,Y]]]`;
* `Z₅` and `Z₆` in nested-commutator form (`bchHom_five_lie`, `bchHom_six_lie`).

The identities hold for `X, Y` in any algebra over `ℝ` or `ℂ` (no norm or
completeness is used); the bracket is the ring commutator `⁅X, Y⁆ = XY - YX`.
The proofs expand the degree recursion of `bchHom` and normalize the resulting
linear combinations of words with the `module` tactic.
-/
import BCH.Series

open NormedSpace Finset Finset.Nat

namespace BCH

variable {𝕂 : Type*} {𝔸 : Type*} [RCLike 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸]

lemma expBlock_one (X Y : 𝔸) : expBlock 𝕂 X Y 1 = X + Y := by
  simp [expBlock, Finset.Nat.sum_antidiagonal_succ, add_comm]

lemma expBlock_two (X Y : 𝔸) :
    expBlock 𝕂 X Y 2 = (2 : 𝕂)⁻¹ • (X * X) + X * Y + (2 : 𝕂)⁻¹ • (Y * Y) := by
  simp [expBlock, Finset.Nat.sum_antidiagonal_succ, Nat.factorial, pow_succ]
  module

lemma expBlock_three (X Y : 𝔸) :
    expBlock 𝕂 X Y 3 = (6 : 𝕂)⁻¹ • (X * X * X) + (2 : 𝕂)⁻¹ • (X * X * Y)
      + (2 : 𝕂)⁻¹ • (X * (Y * Y)) + (6 : 𝕂)⁻¹ • (Y * Y * Y) := by
  simp [expBlock, Finset.Nat.sum_antidiagonal_succ, Nat.factorial, pow_succ]
  module

lemma expBlock_four (X Y : 𝔸) :
    expBlock 𝕂 X Y 4 = (24 : 𝕂)⁻¹ • (X * X * X * X) + (6 : 𝕂)⁻¹ • (X * X * X * Y)
      + (4 : 𝕂)⁻¹ • (X * X * (Y * Y)) + (6 : 𝕂)⁻¹ • (X * (Y * Y * Y))
      + (24 : 𝕂)⁻¹ • (Y * Y * Y * Y) := by
  simp [expBlock, Finset.Nat.sum_antidiagonal_succ, Nat.factorial, pow_succ]
  module

lemma uBlock_one (X Y : 𝔸) : uBlock 𝕂 X Y 1 = X + Y := by simp [uBlock, expBlock_one]

lemma uBlock_two (X Y : 𝔸) :
    uBlock 𝕂 X Y 2 = (2 : 𝕂)⁻¹ • (X * X) + X * Y + (2 : 𝕂)⁻¹ • (Y * Y) := by
  simp [uBlock, expBlock_two]

lemma uBlock_three (X Y : 𝔸) :
    uBlock 𝕂 X Y 3 = (6 : 𝕂)⁻¹ • (X * X * X) + (2 : 𝕂)⁻¹ • (X * X * Y)
      + (2 : 𝕂)⁻¹ • (X * (Y * Y)) + (6 : 𝕂)⁻¹ • (Y * Y * Y) := by
  simp [uBlock, expBlock_three]

lemma uBlock_four (X Y : 𝔸) :
    uBlock 𝕂 X Y 4 = (24 : 𝕂)⁻¹ • (X * X * X * X) + (6 : 𝕂)⁻¹ • (X * X * X * Y)
      + (4 : 𝕂)⁻¹ • (X * X * (Y * Y)) + (6 : 𝕂)⁻¹ • (X * (Y * Y * Y))
      + (24 : 𝕂)⁻¹ • (Y * Y * Y * Y) := by
  simp [uBlock, expBlock_four]

theorem bchHom_one (X Y : 𝔸) : bchHom 𝕂 X Y 1 = X + Y := by
  simp [bchHom, powBlock_one, uBlock_one]

theorem bchHom_two (X Y : 𝔸) : bchHom 𝕂 X Y 2 = (2 : 𝕂)⁻¹ • (X * Y - Y * X) := by
  simp [bchHom, Finset.sum_range_succ, powBlock_succ,
    powBlock_zero, Finset.Nat.sum_antidiagonal_succ, uBlock_zero, uBlock_one, uBlock_two,
    mul_add, add_mul, mul_assoc,
    smul_smul, smul_add, smul_sub]
  module

theorem bchHom_two_lie (X Y : 𝔸) : bchHom 𝕂 X Y 2 = (2 : 𝕂)⁻¹ • ⁅X, Y⁆ := by
  rw [bchHom_two, Ring.lie_def]

theorem bchHom_three (X Y : 𝔸) :
    bchHom 𝕂 X Y 3 = (12 : 𝕂)⁻¹ • (X * X * Y + X * Y * Y - (2 : 𝕂) • (X * Y * X)
      + Y * Y * X + Y * X * X - (2 : 𝕂) • (Y * X * Y)) := by
  simp [bchHom, Finset.sum_range_succ, powBlock_succ,
    powBlock_zero, Finset.Nat.sum_antidiagonal_succ, uBlock_zero, uBlock_one, uBlock_two,
    uBlock_three, mul_add, add_mul, mul_assoc,
    smul_smul, smul_add, smul_sub]
  module

theorem bchHom_three_lie (X Y : 𝔸) :
    bchHom 𝕂 X Y 3 = (12 : 𝕂)⁻¹ • ⁅X, ⁅X, Y⁆⁆ + (12 : 𝕂)⁻¹ • ⁅Y, ⁅Y, X⁆⁆ := by
  rw [bchHom_three]
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc, smul_sub, smul_add, smul_smul]
  module

theorem bchHom_four (X Y : 𝔸) :
    bchHom 𝕂 X Y 4 = (24 : 𝕂)⁻¹ • (X * X * (Y * Y) - (2 : 𝕂) • (X * Y * (X * Y))
      - Y * Y * (X * X) + (2 : 𝕂) • (Y * X * (Y * X))) := by
  simp [bchHom, Finset.sum_range_succ, powBlock_succ,
    powBlock_zero, Finset.Nat.sum_antidiagonal_succ, uBlock_zero, uBlock_one, uBlock_two,
    uBlock_three, uBlock_four, mul_add, add_mul, mul_assoc, smul_smul, smul_add, smul_sub]
  module

theorem bchHom_four_lie (X Y : 𝔸) :
    bchHom 𝕂 X Y 4 = -(24 : 𝕂)⁻¹ • ⁅Y, ⁅X, ⁅X, Y⁆⁆⁆ := by
  rw [bchHom_four]
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc, smul_sub, smul_add, smul_smul]
  module

lemma expBlock_five (X Y : 𝔸) :
    expBlock 𝕂 X Y 5 = (120 : 𝕂)⁻¹ • (X * X * X * X * X) + (24 : 𝕂)⁻¹ • (X * X * X * X * Y)
      + (12 : 𝕂)⁻¹ • (X * X * X * (Y * Y)) + (12 : 𝕂)⁻¹ • (X * X * (Y * Y * Y))
      + (24 : 𝕂)⁻¹ • (X * (Y * Y * Y * Y)) + (120 : 𝕂)⁻¹ • (Y * Y * Y * Y * Y) := by
  simp [expBlock, Finset.Nat.sum_antidiagonal_succ, Nat.factorial, pow_succ]
  module

lemma uBlock_five (X Y : 𝔸) :
    uBlock 𝕂 X Y 5 = (120 : 𝕂)⁻¹ • (X * X * X * X * X) + (24 : 𝕂)⁻¹ • (X * X * X * X * Y)
      + (12 : 𝕂)⁻¹ • (X * X * X * (Y * Y)) + (12 : 𝕂)⁻¹ • (X * X * (Y * Y * Y))
      + (24 : 𝕂)⁻¹ • (X * (Y * Y * Y * Y)) + (120 : 𝕂)⁻¹ • (Y * Y * Y * Y * Y) := by
  simp [uBlock, expBlock_five]

lemma expBlock_six (X Y : 𝔸) :
    expBlock 𝕂 X Y 6 = (720 : 𝕂)⁻¹ • (X * X * X * X * X * X)
      + (120 : 𝕂)⁻¹ • (X * X * X * X * X * Y)
      + (48 : 𝕂)⁻¹ • (X * X * X * X * (Y * Y)) + (36 : 𝕂)⁻¹ • (X * X * X * (Y * Y * Y))
      + (48 : 𝕂)⁻¹ • (X * X * (Y * Y * Y * Y)) + (120 : 𝕂)⁻¹ • (X * (Y * Y * Y * Y * Y))
      + (720 : 𝕂)⁻¹ • (Y * Y * Y * Y * Y * Y) := by
  simp [expBlock, Finset.Nat.sum_antidiagonal_succ, Nat.factorial, pow_succ]
  module

lemma uBlock_six (X Y : 𝔸) :
    uBlock 𝕂 X Y 6 = (720 : 𝕂)⁻¹ • (X * X * X * X * X * X)
      + (120 : 𝕂)⁻¹ • (X * X * X * X * X * Y)
      + (48 : 𝕂)⁻¹ • (X * X * X * X * (Y * Y)) + (36 : 𝕂)⁻¹ • (X * X * X * (Y * Y * Y))
      + (48 : 𝕂)⁻¹ • (X * X * (Y * Y * Y * Y)) + (120 : 𝕂)⁻¹ • (X * (Y * Y * Y * Y * Y))
      + (720 : 𝕂)⁻¹ • (Y * Y * Y * Y * Y * Y) := by
  simp [uBlock, expBlock_six]

set_option maxHeartbeats 4000000 in
/-- **Proposition 4.3, equation (4.z5)**: the degree-five component
`Z₅ = -1/720 ([Y,[Y,[Y,[Y,X]]]] + [X,[X,[X,[X,Y]]]]) + 1/360 ([X,[Y,[Y,[Y,X]]]] + [Y,[X,[X,[X,Y]]]])
+ 1/120 ([Y,[X,[Y,[X,Y]]]] + [X,[Y,[X,[Y,X]]]])`. -/
theorem bchHom_five_lie (X Y : 𝔸) :
    bchHom 𝕂 X Y 5 = -(720 : 𝕂)⁻¹ • (⁅Y, ⁅Y, ⁅Y, ⁅Y, X⁆⁆⁆⁆ + ⁅X, ⁅X, ⁅X, ⁅X, Y⁆⁆⁆⁆)
      + (360 : 𝕂)⁻¹ • (⁅X, ⁅Y, ⁅Y, ⁅Y, X⁆⁆⁆⁆ + ⁅Y, ⁅X, ⁅X, ⁅X, Y⁆⁆⁆⁆)
      + (120 : 𝕂)⁻¹ • (⁅Y, ⁅X, ⁅Y, ⁅X, Y⁆⁆⁆⁆ + ⁅X, ⁅Y, ⁅X, ⁅Y, X⁆⁆⁆⁆) := by
  simp only [Ring.lie_def]
  simp [bchHom, Finset.sum_range_succ, powBlock_succ,
    powBlock_zero, Finset.Nat.sum_antidiagonal_succ, uBlock_zero, uBlock_one, uBlock_two,
    uBlock_three, uBlock_four, uBlock_five, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    smul_smul, smul_add, smul_sub]
  module

set_option maxHeartbeats 16000000 in
/-- **Proposition 4.3, equation (4.z6)**: the degree-six component
`Z₆ = 1/240 [X,[Y,[X,[Y,[X,Y]]]]] + 1/720 ([X,[Y,[X,[X,[X,Y]]]]] - [X,[X,[Y,[Y,[X,Y]]]]])
+ 1/1440 ([X,[Y,[Y,[Y,[X,Y]]]]] - [X,[X,[Y,[X,[X,Y]]]]])`. -/
theorem bchHom_six_lie (X Y : 𝔸) :
    bchHom 𝕂 X Y 6 = (240 : 𝕂)⁻¹ • ⁅X, ⁅Y, ⁅X, ⁅Y, ⁅X, Y⁆⁆⁆⁆⁆
      + (720 : 𝕂)⁻¹ • (⁅X, ⁅Y, ⁅X, ⁅X, ⁅X, Y⁆⁆⁆⁆⁆ - ⁅X, ⁅X, ⁅Y, ⁅Y, ⁅X, Y⁆⁆⁆⁆⁆)
      + (1440 : 𝕂)⁻¹ • (⁅X, ⁅Y, ⁅Y, ⁅Y, ⁅X, Y⁆⁆⁆⁆⁆ - ⁅X, ⁅X, ⁅Y, ⁅X, ⁅X, Y⁆⁆⁆⁆⁆) := by
  simp only [Ring.lie_def]
  simp [bchHom, Finset.sum_range_succ, powBlock_succ,
    powBlock_zero, Finset.Nat.sum_antidiagonal_succ, uBlock_zero, uBlock_one, uBlock_two,
    uBlock_three, uBlock_four, uBlock_five, uBlock_six, mul_add, add_mul, mul_sub, sub_mul,
    mul_assoc, smul_smul, smul_add, smul_sub]
  module

end BCH
