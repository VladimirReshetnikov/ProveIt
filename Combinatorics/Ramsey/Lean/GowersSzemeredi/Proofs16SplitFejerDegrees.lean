import GowersSzemeredi.Proofs16SplitAllDimensions
import GowersSzemeredi.Proofs16TightRadius

/-! **The split-class degrees with the Fejér inputs** (Notes L.16c).

The split recursion `splitPair` (Notes L.7) takes three inputs from
Section 16: the parameter exponent `stepP k = 2^(2^(k+5)+6)` (θ₁), the
Bohr exponent `stepT k = 2^(2^(k+6))` (the printed `s`) and the
dimension-two seed `2^132`. They give `log₂ D_k ≈ 68·2^k`
(`split_pair_tight`). Here the parameter-side step is parameterized by
`(P, T)` (`splitStepDWith`, a copy of `splitStepD` with `stepP k`, `stepT k`
replaced). Its bound `splitStepDWith_le` is the corpus's generic
`split_degree_poly`.
* `fejer_split_step c`: if `P ≤ 2^(5k+20)` and `T ≤ 2^(5k+19)`, the
  invariants `2^(k+6)·a_k ≤ 2^(c·2^k)` and `D_k ≤ 2^((c+8)·2^k)` propagate,
  for `k ≥ 2` and any `c`.
* `fejerStepP k = 64·fejerProductExponent k` and
  `fejerStepT k = 22·fejerProductExponent k + 105` (the tight radius of
  `Proofs16TightRadius`) satisfy these bounds (`fejerStepP_le`,
  `fejerStepT_le`).
* `splitPairWith`: the recursion with these inputs from a seed `(a₂, D₂)`.
  `split_pair_with_bounds c` gives `log₂ D_k ≤ (c+8)·2^k` when
  `2^8·a₂ ≤ 2^(4c)` and `D₂ ≤ 2^(4(c+8))`.
  `split_pair_with_bounds_fourteen` covers any seed `a₂ ≤ 2^48`,
  `D₂ ≤ 2^88` with `log₂ D_k ≤ 22·2^k`, against `68·2^k` today.

The seed is the dimension-two base. Under the Fejér θ₁ its counts are about
`2^34` (`section16BaseFamilyBound`, whose Lemma 16.3 density
`2^(−2000)(γθ)^10000` multiplies the budget degree by `10^4`), so the seed
is about `2^35` to `2^40`: inside the `2^48` of the `c = 14` instance. By
the envelope model (`models/model_tight_s.py`) a class constant up to 25
gives Theorem 18.1 at `d + 6` and Theorem 18.2 at `L + 4`. Proving the seed
bound is the dimension-two part of the propagation (Notes L.16c).

`splitStepDWith_stepP` is in `Proofs16SplitFejerDegreesSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The parameter-side step with inputs `(P, T)` -/

def wStepY (P k a D : Nat) : Nat := a * (P + 1) + D * (P + k + 6)
def wSW (P k a D : Nat) : Nat := wStepY P k a D * 2 ^ k + P + 8
def wPbW (P k a D : Nat) : Nat := a * (P + wSW P k a D + 1) + D * (P + 5)
def wCountW (P k a D : Nat) : Nat := P + 1 + 2 * wSW P k a D + 2 * wPbW P k a D
def wEbW (P a D : Nat) : Nat := a * (P + 1) + D * (P + 6)
def wErW (P k a D : Nat) : Nat := (wStepY P k a D + 4) * 2 ^ k
def wBqW (P k a D : Nat) : Nat := 4 + (wEbW P a D + 1) * 2 ^ (k + 2)
def wLW (P k a D : Nat) : Nat := wBqW P k a D + (wErW P k a D + wEbW P a D)
def wZW (P T a D : Nat) : Nat := T + a + wEbW P a D + 7
def wExpW (P T k a D : Nat) : Nat := wZW P T a D + wLW P k a D + wPbW P k a D + 6
def wThrDeg (P D : Nat) : Nat := D * (P + 2) + P + 2

/-- The parameter degree of the next split class, with inputs `(P, T)`. At
`P = stepP k`, `T = stepT k` it is `splitStepD k a D`
(`splitStepDWith_stepP`). -/
def splitStepDWith (P T k a D : Nat) : Nat :=
  wCountW P k a D + wExpW P T k a D + wThrDeg P D

theorem splitStepDWith_le {P T k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) (hP : k + 9 ≤ P) :
    splitStepDWith P T k a D ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T := by
  have h4 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have h6 : 2 ^ (k + 6) = 2 ^ k * 64 := by rw [pow_add]; norm_num
  have h := split_degree_poly (a := a) (D := D) (P := P) (A := 2 ^ k) (T := T)
    (k := k) (Y := wStepY P k a D) (SW := wSW P k a D) (PbW := wPbW P k a D)
    (CW := wCountW P k a D) (EbW := wEbW P a D) (ErW := wErW P k a D) (BqW := wBqW P k a D)
    (LW := wLW P k a D) (ZW := wZW P T a D) (EW := wExpW P T k a D) (Th := wThrDeg P D)
    ha hD Nat.one_le_two_pow hP h4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [h6]
  exact h

/-! ### The invariants -/

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

/-- The arithmetic of the step, over plain variables (abstracting powers of
two with `generalize` would make `kabstract` unfold them). -/
theorem split_step_arith (X Y Z : Nat) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    X * (2 * Y) * (2 * Z) + Z ≤ 8 * Z * X * Y := by
  have h : 1 * 1 ≤ X * Y := Nat.mul_le_mul hX hY
  nlinarith [Nat.mul_le_mul_left Z h]

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

/-! ### The Fejér inputs -/

/-- The parameter exponent with the Fejér θ₁: `64·fejerProductExponent k`. -/
def fejerStepP (k : Nat) : Nat := 64 * fejerProductExponent k

/-- The tight Bohr exponent with the Fejér θ₁: `22·fejerProductExponent k + 105`. -/
def fejerStepT (k : Nat) : Nat := 22 * fejerProductExponent k + 105

theorem fejerStepP_le (k : Nat) : fejerStepP k ≤ 2 ^ (5 * k + 20) := by
  unfold fejerStepP
  have h := fejerProductExponent_le k
  have e : 2 ^ (5 * k + 20) = 64 * 2 ^ (5 * k + 14) := by
    rw [show 5 * k + 20 = (5 * k + 14) + 6 by ring, pow_add]; ring
  rw [e]
  exact Nat.mul_le_mul_left 64 h

theorem fejerStepT_le (k : Nat) : fejerStepT k ≤ 2 ^ (5 * k + 19) := by
  unfold fejerStepT
  have h := fejerProductExponent_le k
  have e : 2 ^ (5 * k + 19) = 32 * 2 ^ (5 * k + 14) := by
    rw [show 5 * k + 19 = (5 * k + 14) + 5 by ring, pow_add]; ring
  have h14 : 2 ^ 14 ≤ 2 ^ (5 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [e]
  omega

theorem fejerStepP_ge (k : Nat) : k + 9 ≤ fejerStepP k := by
  unfold fejerStepP fejerProductExponent fejerSelectionExponent
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ 2 ^ (3 * k + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 1 ≤ 2 ^ (k + 4) * (k + 6) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h4 : 2 ^ (3 * k + 7) ≤ 2 ^ (3 * k + 7) * (2 ^ (k + 4) * (k + 6)) :=
    Nat.le_mul_of_pos_right _ h3
  omega

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
