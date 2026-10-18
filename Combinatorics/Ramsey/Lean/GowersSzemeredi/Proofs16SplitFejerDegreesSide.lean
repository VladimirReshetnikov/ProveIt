import GowersSzemeredi.Proofs16SplitFejerDegrees
import GowersSzemeredi.Proofs16SplitStepBoundsSide

/-! Declarations of `Proofs16SplitFejerDegrees` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem five_k_le_eight_pow : ∀ k, 2 ≤ k → 5 * k + 22 ≤ 8 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

/-- Doubling the exponent `c·2^k`; stated separately because `congr 1` would
try to close it by evaluating the powers. -/
theorem double_exponent (c k : Nat) : c * 2 ^ k + c * 2 ^ k = c * 2 ^ (k + 1) := by
  rw [pow_succ]; ring

/-- **The invariants propagate** when `P ≤ 2^(5k+20)` and `T ≤ 2^(5k+19)`:
`2^(k+6)·a ≤ 2^(c·2^k)` and `D ≤ 2^((c+8)·2^k)`, for any `c`. -/
theorem fejer_split_step (c : Nat) {k a D a' D' P T : Nat} (hk : 2 ≤ k)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ (c * 2 ^ k)) (hDb : D ≤ 2 ^ ((c + 8) * 2 ^ k))
    (ha' : a' ≤ 2 ^ (k + 5) * (a * a)) (hD' : D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T)
    (hP : P ≤ 2 ^ (5 * k + 20)) (hT : T ≤ 2 ^ (5 * k + 19)) :
    2 ^ (k + 1 + 6) * a' ≤ 2 ^ (c * 2 ^ (k + 1)) ∧ D' ≤ 2 ^ ((c + 8) * 2 ^ (k + 1)) := by
  constructor
  · calc 2 ^ (k + 1 + 6) * a' ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ ha'
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ (c * 2 ^ k) * 2 ^ (c * 2 ^ k) := Nat.mul_le_mul hA hA
      _ = 2 ^ (c * 2 ^ (k + 1)) := by rw [← pow_add, double_exponent c k]
  · have haX : a ≤ 2 ^ (c * 2 ^ k) :=
      le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have hXY : 2 ^ (c * 2 ^ k) ≤ 2 ^ ((c + 8) * 2 ^ k) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hsum : a + D ≤ 2 * 2 ^ ((c + 8) * 2 ^ k) := by omega
    have hkey : 2 ^ (5 * k + 22) * 2 ^ (c * 2 ^ k) ≤ 2 ^ ((c + 8) * 2 ^ k) := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      have := five_k_le_eight_pow k hk
      rw [add_mul]
      omega
    have e20 : 2 ^ (5 * k + 20) = 2 * 2 ^ (5 * k + 19) := by rw [show 5 * k + 20 = (5 * k + 19) + 1 by ring, pow_succ]; ring
    have e22 : 2 ^ (5 * k + 22) = 8 * 2 ^ (5 * k + 19) := by
      rw [show 5 * k + 22 = (5 * k + 19) + 3 by ring, pow_add]; ring
    have hX1 : 1 ≤ 2 ^ (c * 2 ^ k) := Nat.one_le_two_pow
    have hY1 : 1 ≤ 2 ^ ((c + 8) * 2 ^ k) := Nat.one_le_two_pow
    calc D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T := hD'
      _ = (2 ^ (k + 6) * a) * (a + D) * P + T := by ring
      _ ≤ 2 ^ (c * 2 ^ k) * (2 * 2 ^ ((c + 8) * 2 ^ k)) * 2 ^ (5 * k + 20) + 2 ^ (5 * k + 19) :=
          Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) hP) hT
      _ ≤ (2 ^ (5 * k + 22) * 2 ^ (c * 2 ^ k)) * 2 ^ ((c + 8) * 2 ^ k) := by
          rw [e20, e22]
          exact split_step_arith _ _ _ hX1 hY1
      _ ≤ 2 ^ ((c + 8) * 2 ^ k) * 2 ^ ((c + 8) * 2 ^ k) := Nat.mul_le_mul_right _ hkey
      _ = 2 ^ ((c + 8) * 2 ^ (k + 1)) := by rw [← pow_add, double_exponent (c + 8) k]

/-- The split recursion with the Fejér inputs, from a seed at dimension `2`. -/
def splitPairWith (seedA seedD : Nat) : Nat → Nat × Nat
  | 0 => (seedA, seedD)
  | k + 1 => if k < 2 then (seedA, seedD)
      else (splitStepA k (splitPairWith seedA seedD k).1,
        splitStepDWith (fejerStepP k) (fejerStepT k) k
          (splitPairWith seedA seedD k).1 (splitPairWith seedA seedD k).2)

theorem splitPairWith_two (seedA seedD : Nat) : splitPairWith seedA seedD 2 = (seedA, seedD) := by
  simp [splitPairWith]

theorem splitPairWith_succ (seedA seedD : Nat) {k : Nat} (hk : 2 ≤ k) :
    splitPairWith seedA seedD (k + 1) =
      (splitStepA k (splitPairWith seedA seedD k).1,
        splitStepDWith (fejerStepP k) (fejerStepT k) k
          (splitPairWith seedA seedD k).1 (splitPairWith seedA seedD k).2) := by
  rw [splitPairWith, if_neg (by omega)]

/-- **The split degrees with the Fejér inputs**, for any invariant constant
`c`: from a seed with `2^8·a₂ ≤ 2^(4c)` and `D₂ ≤ 2^(4(c+8))`,
`log₂ D_k ≤ (c+8)·2^k` in every dimension `k ≥ 2`. -/
theorem split_pair_with_bounds (c : Nat) {seedA seedD : Nat} (hA1 : 1 ≤ seedA) (hD1 : 1 ≤ seedD)
    (hA : 2 ^ 8 * seedA ≤ 2 ^ (c * 4)) (hD : seedD ≤ 2 ^ ((c + 8) * 4)) : ∀ k, 2 ≤ k →
    1 ≤ (splitPairWith seedA seedD k).1 ∧ 1 ≤ (splitPairWith seedA seedD k).2 ∧
      2 ^ (k + 6) * (splitPairWith seedA seedD k).1 ≤ 2 ^ (c * 2 ^ k) ∧
      (splitPairWith seedA seedD k).2 ≤ 2 ^ ((c + 8) * 2 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [splitPairWith_two]
    refine ⟨hA1, hD1, ?_, ?_⟩
    · simpa using hA
    · simpa using hD
  | succ k hk ih =>
    obtain ⟨ha, hDp, hAb, hDb⟩ := ih
    rw [splitPairWith_succ _ _ hk]
    set a := (splitPairWith seedA seedD k).1
    set D := (splitPairWith seedA seedD k).2
    obtain ⟨h1, h2⟩ := fejer_split_step c hk hAb hDb (splitStepA_le ha)
      (splitStepDWith_le ha hDp (fejerStepP_ge k)) (fejerStepP_le k) (fejerStepT_le k)
    refine ⟨?_, ?_, h1, h2⟩
    · unfold splitStepA sCountN; omega
    · unfold splitStepDWith wCountW; omega

/-- **At `c = 14`**: any seed `a₂ ≤ 2^48`, `D₂ ≤ 2^88` gives
`log₂ D_k ≤ 22·2^k`. Dimension-two counts under the Fejér θ₁ are about
`2^34` (Notes L.16c), well inside. -/
theorem split_pair_with_bounds_fourteen {seedA seedD : Nat} (hA1 : 1 ≤ seedA) (hD1 : 1 ≤ seedD)
    (hA : seedA ≤ 2 ^ 48) (hD : seedD ≤ 2 ^ 88) : ∀ k, 2 ≤ k →
    (splitPairWith seedA seedD k).2 ≤ 2 ^ (22 * 2 ^ k) := by
  intro k hk
  have h := split_pair_with_bounds 14 hA1 hD1
    (by calc 2 ^ 8 * seedA ≤ 2 ^ 8 * 2 ^ 48 := Nat.mul_le_mul_left _ hA
          _ = 2 ^ (14 * 4) := by norm_num)
    (by simpa using hD) k hk
  simpa using h.2.2.2

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

theorem splitStepDWith_stepP (k a D : Nat) :
    splitStepDWith (stepP k) (stepT k) k a D = splitStepD k a D := by
  unfold splitStepDWith wCountW wExpW wThrDeg wZW wLW wBqW wErW wEbW wPbW wSW wStepY
    splitStepD sCountW sExpW stepThrDeg sZW sLW sBqW sErW sEbW sPbW sSW sQrW sStepY
  rfl

end LeanProofs.GowersSzemeredi
