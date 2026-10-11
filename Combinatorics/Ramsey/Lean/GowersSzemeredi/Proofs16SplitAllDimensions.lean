import GowersSzemeredi.Proofs16SplitStepBounds
import GowersSzemeredi.Proofs16AllDimensions

/-! Split uniform classes in every dimension, with `O(2^k)` logarithms
(Notes L.7, F3a).

* `splitStepA_le`: `splitStepA k a ≤ 2^(k+5)·a²`.
* `splitStepD_le`: `splitStepD k a D ≤ 2^(k+6)·a(a+D)·P + T`, with
  `P = stepP k` and `T = stepT k`. There is no `D²` term: the parameter degree
  enters the next class linearly, multiplied by `a` and `P`.
* `split_invariant_succ`: the step preserves the invariants
  `2^(k+6)·a_k ≤ 2^(35·2^k)` and `D_k ≤ 2^(75·2^k)`. At `k = 2` they hold for
  `a = D = 2^132`.
* `splitPair k = (a_k, D_k)`: the degrees, with `split_pair_bounds`.
* `splitUniformClass_all`: a split class in every dimension `k ≥ 2`.

So `log a_k ≤ 35·2^k` and `log D_k ≤ 75·2^k`, against `k·2^(k+6)` for the
power classes of Notes L.6. This is the budget Theorem 18.2 at every length
needs (Notes L.7). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The step degrees -/

theorem splitStepA_le {k a : Nat} (ha : 1 ≤ a) : splitStepA k a ≤ 2 ^ (k + 5) * (a * a) := by
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have h5 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
  unfold splitStepA sCountN sExpN sLN sBqN sErN sPbN sSN sQrN
  rw [h2, h5]
  set A := 2 ^ k
  have haa : a ≤ a * a := Nat.le_mul_of_pos_left _ ha
  nlinarith [Nat.mul_le_mul hA haa, Nat.mul_le_mul hA ha, Nat.zero_le (A * a), Nat.zero_le (A * (a * a))]

/-- The polynomial behind `splitStepD_le`, over plain variables. -/
theorem split_degree_poly {a D P A A4 T k Y SW PbW CW EbW ErW BqW LW ZW EW Th : Nat}
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hA : 1 ≤ A) (hkP : k + 9 ≤ P) (hA4 : A4 = A * 4)
    (hY : Y = a * (P + 1) + D * (P + k + 6)) (hSW : SW = Y * A + P + 8)
    (hPb : PbW = a * (P + SW + 1) + D * (P + 5)) (hCW : CW = P + 1 + 2 * SW + 2 * PbW)
    (hEb : EbW = a * (P + 1) + D * (P + 6)) (hEr : ErW = (Y + 4) * A)
    (hBq : BqW = 4 + (EbW + 1) * A4) (hL : LW = BqW + (ErW + EbW))
    (hZ : ZW = T + a + EbW + 7) (hE : EW = ZW + LW + PbW + 6)
    (hTh : Th = D * (P + 2) + P + 2) :
    CW + EW + Th ≤ A * 64 * (a * (a + D)) * P + T := by
  subst hA4
  have hs1 : 1 ≤ a + D := by omega
  have hsA : 1 ≤ (a + D) * A := Nat.mul_le_mul hs1 hA
  -- `Q = (a+D)·P·A ≤ R = a(a+D)·P·A`
  have hPQ : P * 1 ≤ P * ((a + D) * A) := Nat.mul_le_mul_left P hsA
  have hQR : 1 * ((a + D) * P * A) ≤ a * ((a + D) * P * A) := Nat.mul_le_mul_right _ ha
  have hsP : (a + D) * P * 1 ≤ (a + D) * P * A := Nat.mul_le_mul_left _ hA
  have hs1P : (a + D) * 1 ≤ (a + D) * P := Nat.mul_le_mul_left _ (by omega)
  have haS : a ≤ a + D := by omega
  have hDS : D ≤ a + D := by omega
  have h1 : Y ≤ 2 * (a + D) * P := by
    have e1 := Nat.mul_le_mul_left a (show P + 1 ≤ 2 * P by omega)
    have e2 := Nat.mul_le_mul_left D (show P + k + 6 ≤ 2 * P by omega)
    rw [hY]; nlinarith only [e1, e2]
  have h1A : Y * A ≤ 2 * (a + D) * P * A := Nat.mul_le_mul_right A h1
  have h2 : SW ≤ 4 * ((a + D) * P * A) := by
    rw [hSW]; nlinarith only [h1A, hPQ, hkP]
  have h3a : P + SW + 1 ≤ 6 * ((a + D) * P * A) := by nlinarith only [h2, hPQ, hkP]
  have h3b : a * (P + SW + 1) ≤ a * (6 * ((a + D) * P * A)) := Nat.mul_le_mul_left a h3a
  have h3c : D * (P + 5) ≤ (a + D) * (2 * P) := Nat.mul_le_mul hDS (by omega)
  have h3 : PbW ≤ 8 * (a * ((a + D) * P * A)) := by
    rw [hPb]; nlinarith only [h3b, h3c, hsP, hQR]
  have hC : CW ≤ 26 * (a * ((a + D) * P * A)) := by
    rw [hCW]; nlinarith only [h2, h3, hPQ, hQR, hkP]
  have hEb' : EbW ≤ 2 * (a + D) * P := by
    have e1 := Nat.mul_le_mul_left a (show P + 1 ≤ 2 * P by omega)
    have e2 := Nat.mul_le_mul_left D (show P + 6 ≤ 2 * P by omega)
    rw [hEb]; nlinarith only [e1, e2]
  have hEbA : EbW * A ≤ 2 * (a + D) * P * A := Nat.mul_le_mul_right A hEb'
  have h4A : 4 * A ≤ P * A := Nat.mul_le_mul_right A (by omega)
  have hPA : 1 * (P * A) ≤ (a + D) * (P * A) := Nat.mul_le_mul_right _ hs1
  have hEr' : ErW ≤ 3 * ((a + D) * P * A) := by
    rw [hEr]; nlinarith only [h1A, h4A, hPA]
  have hBq' : BqW ≤ 13 * ((a + D) * P * A) := by
    rw [hBq]; nlinarith only [hEbA, h4A, hPA, hA]
  have hL' : LW ≤ 18 * ((a + D) * P * A) := by
    rw [hL]; nlinarith only [hBq', hEr', hEb', hsP]
  have hZ' : ZW ≤ T + 4 * ((a + D) * P * A) := by
    rw [hZ]; nlinarith only [hEb', hsP, hs1P, haS, hkP, hPQ]
  have hE' : EW ≤ T + 31 * (a * ((a + D) * P * A)) := by
    rw [hE]; nlinarith only [hZ', hL', h3, hQR, hPQ, hkP]
  have hTh' : Th ≤ 4 * ((a + D) * P * A) := by
    have e1 := Nat.mul_le_mul_left D (show P + 2 ≤ 2 * P by omega)
    rw [hTh]; nlinarith only [e1, hDS, hsP, hPQ, hkP, Nat.mul_le_mul_right P hDS]
  nlinarith only [hC, hE', hTh', hQR]

theorem splitStepD_le {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D) :
    splitStepD k a D ≤ 2 ^ (k + 6) * (a * (a + D)) * stepP k + stepT k := by
  have h4 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [pow_add]; norm_num
  have h6 : 2 ^ (k + 6) = 2 ^ k * 64 := by rw [pow_add]; norm_num
  have h := split_degree_poly (a := a) (D := D) (P := stepP k) (A := 2 ^ k) (T := stepT k)
    (k := k) (Y := sStepY k a D) (SW := sSW k a D) (PbW := sPbW k a D) (CW := sCountW k a D)
    (EbW := sEbW k a D) (ErW := sErW k a D) (BqW := sBqW k a D) (LW := sLW k a D)
    (ZW := sZW k a D) (EW := sExpW k a D) (Th := stepThrDeg k D)
    ha hD Nat.one_le_two_pow (stepP_ge9 k) h4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [h6]
  exact h

/-! ### The invariants -/

theorem split_invariant_succ {k a D : Nat} (ha : 1 ≤ a) (hD : 1 ≤ D)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ (35 * 2 ^ k)) (hDb : D ≤ 2 ^ (75 * 2 ^ k)) :
    2 ^ (k + 1 + 6) * splitStepA k a ≤ 2 ^ (35 * 2 ^ (k + 1)) ∧
      splitStepD k a D ≤ 2 ^ (75 * 2 ^ (k + 1)) := by
  have hE : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  constructor
  · calc 2 ^ (k + 1 + 6) * splitStepA k a ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ (splitStepA_le ha)
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ (35 * 2 ^ k) * 2 ^ (35 * 2 ^ k) := Nat.mul_le_mul hA hA
      _ = 2 ^ (35 * 2 ^ (k + 1)) := by
          rw [← pow_add, pow_succ]; congr 1; ring
  · have haE : a ≤ 2 ^ (35 * 2 ^ k) :=
      le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have h3575 : 2 ^ (35 * 2 ^ k) ≤ 2 ^ (75 * 2 ^ k) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsum : a + D ≤ 2 ^ (75 * 2 ^ k + 1) := by rw [pow_succ]; omega
    have hP : stepP k = 2 ^ (32 * 2 ^ k + 6) := by
      unfold stepP; congr 1; rw [pow_add]; ring
    have hT : stepT k = 2 ^ (64 * 2 ^ k) := by
      unfold stepT; congr 1; rw [pow_add]; ring
    have he : 35 * 2 ^ k + (75 * 2 ^ k + 1) + (32 * 2 ^ k + 6) = 142 * 2 ^ k + 7 := by ring
    calc splitStepD k a D ≤ 2 ^ (k + 6) * (a * (a + D)) * stepP k + stepT k := splitStepD_le ha hD
      _ = (2 ^ (k + 6) * a) * (a + D) * 2 ^ (32 * 2 ^ k + 6) + 2 ^ (64 * 2 ^ k) := by
          rw [hP, hT]; ring
      _ ≤ 2 ^ (35 * 2 ^ k) * 2 ^ (75 * 2 ^ k + 1) * 2 ^ (32 * 2 ^ k + 6) + 2 ^ (142 * 2 ^ k + 7) :=
          add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) le_rfl)
            (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 2 ^ (142 * 2 ^ k + 7) + 2 ^ (142 * 2 ^ k + 7) := by rw [← pow_add, ← pow_add, he]
      _ = 2 ^ (142 * 2 ^ k + 8) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (75 * 2 ^ (k + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ]; omega)

/-! ### Every dimension -/

/-- The seed degree at dimension `2`. -/
def splitSeed : Nat := 2 ^ 132

/-- The degrees `(a_k, D_k)` of the split class in dimension `k`; constant
below dimension `2`. -/
def splitPair : Nat → Nat × Nat
  | 0 => (splitSeed, splitSeed)
  | k + 1 => if k < 2 then (splitSeed, splitSeed)
      else (splitStepA k (splitPair k).1, splitStepD k (splitPair k).1 (splitPair k).2)

theorem splitPair_two : splitPair 2 = (splitSeed, splitSeed) := by
  rw [splitPair, if_pos (by norm_num)]

theorem splitPair_succ {k : Nat} (hk : 2 ≤ k) :
    splitPair (k + 1) = (splitStepA k (splitPair k).1, splitStepD k (splitPair k).1 (splitPair k).2) := by
  rw [splitPair, if_neg (by omega)]

theorem split_pair_bounds : ∀ k, 2 ≤ k →
    1 ≤ (splitPair k).1 ∧ 1 ≤ (splitPair k).2 ∧
      2 ^ (k + 6) * (splitPair k).1 ≤ 2 ^ (35 * 2 ^ k) ∧ (splitPair k).2 ≤ 2 ^ (75 * 2 ^ k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [splitPair_two]
    unfold splitSeed
    refine ⟨Nat.one_le_two_pow, Nat.one_le_two_pow, ?_, Nat.pow_le_pow_right (by norm_num) (by norm_num)⟩
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ k hk ih =>
    obtain ⟨ha, hD, hA, hDb⟩ := ih
    rw [splitPair_succ hk]
    obtain ⟨h1, h2⟩ := split_invariant_succ ha hD hA hDb
    refine ⟨?_, ?_, h1, h2⟩
    · unfold splitStepA sCountN; omega
    · unfold splitStepD sCountW; omega

/-- **A split uniform class in every dimension `k ≥ 2`**, with degrees
`splitPair k`, so `log a_k ≤ 35·2^k` and `log D_k ≤ 75·2^k`
(`split_pair_bounds`). -/
theorem splitUniformClass_all (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass k (classV Kc pc k) (splitPair k).1 (splitPair k).2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitPair_two]
    exact splitUniformClass_two (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl) (by unfold splitSeed; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨ha, hD, -, -⟩ := split_pair_bounds k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitPair_succ hk]
    exact splitUniformClass_succ (by omega) hV1 ha hD C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

end LeanProofs.GowersSzemeredi
