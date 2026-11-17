import IPRADerivations.Probability.MedianCounts

/-!
# A skewed sample whose median exceeds its mean

Packet: `probability/median_ipra_constructive_proofs`, Proposition `prop:skew-counterexample`: for the
equally weighted sample `0, 0, 1, 1, 2` the mean is `4/5`, the median is `1`, and the third central
moment is `18/125 > 0`. The sample is the body `x(i) = [i ∈ {2, 3}] + 2 [i = 4]` on `i < 5`.

* `skew_sum`: `∑_{i<5} x_i = 4`, so the mean is `4/5`;
* `skew_median`: at `t = 1` the counts below and above are `B = 2`, `A = 1`, so `2B ≤ 5` and
  `2A ≤ 5` (`1` is a balance median); at `t = 0` there are `A = 3` entries above and at `t = 2` there
  are `B = 4` below, so neither neighbour is a median;
* `skew_moment`: with `d_i = 5 x_i − 4 ∈ {−4, −4, 1, 1, 6}` split into positive and negative parts
  (`posB`, `negB`), `∑ (d_i⁺)³ = 218`, `∑ (d_i⁻)³ = 128`, so the cleared third central moment is
  `∑ d_i³ = 90 > 0`, i.e. `(1/5) ∑ (x_i − 4/5)³ = 90/625 = 18/125`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianSkew

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.MedianCounts (belowB aboveB Bc Ac isMed below_pt above_pt congrSg)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The sample `x(i) = [i = 2] + [i = 3] + 2 [i = 4]`. -/
abbrev xB : PTm 2 := eqb (var 0) (num 2) + eqb (var 0) (num 3) + two * eqb (var 0) (num 4)

/-- `∑_{i<5} f(i) = f(0) + f(1) + f(2) + f(3) + f(4)`. -/
theorem sum_five (f : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF f) (num 5) x ≐
      inst2 f (num 0) x + inst2 f (num 1) x + inst2 f (num 2) x + inst2 f (num 3) x + inst2 f (num 4) x := by
  have s : ∀ k : ℕ, Γ ⊢[PRAAx] ap2 (sumF f) (num (k + 1)) x ≐ ap2 (sumF f) (num k) x + inst2 f (num k) x :=
    fun k => sum_succ' f (num k) x
  refine (s 4).eqTrans (congrAdd ((s 3).eqTrans (congrAdd ((s 2).eqTrans (congrAdd ((s 1).eqTrans
    (congrAdd ((s 0).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _))) (.eqRefl _)))
    (.eqRefl _))) (.eqRefl _))) (.eqRefl _))

theorem eqb_num (i j : ℕ) : Γ ⊢[PRAAx] eqb (num i : PTm n) (num j) ≐ num (if i = j then 1 else 0) := by
  split_ifs with h
  · subst h; exact eqb_of_eq (.eqRefl _)
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - i - 1, by omega⟩
      exact eqb_zero_of_lt (le_of_eq_add (d := num k) (by apply deriveNat; ipra_simps; push_cast; ring))
    · obtain ⟨k, rfl⟩ : ∃ k, i = j + 1 + k := ⟨i - j - 1, by omega⟩
      exact eqb_zero_of_gt (le_of_eq_add (d := num k) (by apply deriveNat; ipra_simps; push_cast; ring))

theorem x_at (i : ℕ) (x : PTm n) :
    Γ ⊢[PRAAx] inst2 xB (num i) x ≐ num ((if i = 2 then 1 else 0) + (if i = 3 then 1 else 0) + 2 * (if i = 4 then 1 else 0)) := by
  have e : inst2 xB (num i) x = eqb (num i) (num 2) + eqb (num i) (num 3) + two * eqb (num i) (num 4) := by
    simp [inst2]
  rw [e]
  refine (congrAdd (congrAdd (eqb_num i 2) (eqb_num i 3)) (congrMul (.eqRefl _) (eqb_num i 4))).eqTrans ?_
  apply deriveNat; ipra_simps; split_ifs <;> simp_all <;> norm_num

/-- `∑_{i<5} x_i = 4`. -/
theorem skew_sum (x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF xB) (num 5) x ≐ num 4 := by
  refine (sum_five xB x).eqTrans ?_
  refine (congrAdd (congrAdd (congrAdd (congrAdd (x_at 0 x) (x_at 1 x)) (x_at 2 x)) (x_at 3 x)) (x_at 4 x)).eqTrans ?_
  apply deriveNat; ipra_simps; norm_num

/-- The sample values `0, 0, 1, 1, 2`. -/
def xv (i : ℕ) : ℕ := (if i = 2 then 1 else 0) + (if i = 3 then 1 else 0) + 2 * (if i = 4 then 1 else 0)

theorem monus_num (t v : ℕ) : Γ ⊢[PRAAx] monus (num t : PTm n) (num v) ≐ num (t - v) := by
  rcases le_or_gt t v with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, v = t + k := ⟨v - t, by omega⟩
    have e : t - (t + k) = 0 := by omega
    rw [e]
    exact le_of_eq_add (d := num k) (by apply deriveNat; ipra_simps; push_cast; ring)
  · obtain ⟨k, rfl⟩ : ∃ k, t = v + k := ⟨t - v, by omega⟩
    have e : v + k - v = k := by omega
    rw [e]
    have c : Γ ⊢[PRAAx] (num (v + k) : PTm n) ≐ num k + num v := by apply deriveNat; ipra_simps; push_cast; ring
    exact (congrMonus c (.eqRefl _)).eqTrans (add_monus _ _)

theorem sg_num (k : ℕ) : Γ ⊢[PRAAx] sg (num k : PTm n) ≐ num (if k = 0 then 0 else 1) := by
  cases k with
  | zero => exact sg_zero
  | succ k => exact sg_succ _

theorem below_at (t i : ℕ) (p : PTm n) :
    Γ ⊢[PRAAx] inst2 (belowB xB) (num i) (pairT (num t) p) ≐ num (if t - xv i = 0 then 0 else 1) :=
  (below_pt xB _ _ _).eqTrans ((congrSg (congrMonus (.eqRefl _) (x_at i p))).eqTrans
    ((congrSg (monus_num t (xv i))).eqTrans (sg_num _)))

theorem above_at (t i : ℕ) (p : PTm n) :
    Γ ⊢[PRAAx] inst2 (aboveB xB) (num i) (pairT (num t) p) ≐ num (if xv i - t = 0 then 0 else 1) :=
  (above_pt xB _ _ _).eqTrans ((congrSg (congrMonus (x_at i p) (.eqRefl _))).eqTrans
    ((congrSg (monus_num (xv i) t)).eqTrans (sg_num _)))

theorem B_count (t : ℕ) (p : PTm n) :
    Γ ⊢[PRAAx] Bc xB (num 5) (num t) p ≐ num ((if t - xv 0 = 0 then 0 else 1) + (if t - xv 1 = 0 then 0 else 1) +
      (if t - xv 2 = 0 then 0 else 1) + (if t - xv 3 = 0 then 0 else 1) + (if t - xv 4 = 0 then 0 else 1)) := by
  refine (sum_five _ _).eqTrans ((congrAdd (congrAdd (congrAdd (congrAdd (below_at t 0 p) (below_at t 1 p))
    (below_at t 2 p)) (below_at t 3 p)) (below_at t 4 p)).eqTrans ?_)
  apply deriveNat; ipra_simps; push_cast; ring

theorem A_count (t : ℕ) (p : PTm n) :
    Γ ⊢[PRAAx] Ac xB (num 5) (num t) p ≐ num ((if xv 0 - t = 0 then 0 else 1) + (if xv 1 - t = 0 then 0 else 1) +
      (if xv 2 - t = 0 then 0 else 1) + (if xv 3 - t = 0 then 0 else 1) + (if xv 4 - t = 0 then 0 else 1)) := by
  refine (sum_five _ _).eqTrans ((congrAdd (congrAdd (congrAdd (congrAdd (above_at t 0 p) (above_at t 1 p))
    (above_at t 2 p)) (above_at t 3 p)) (above_at t 4 p)).eqTrans ?_)
  apply deriveNat; ipra_simps; push_cast; ring

/-- `1` is a balance median of the sample (`B(1) = 2`, `A(1) = 1`), while `0` (`A(0) = 3`) and `2`
(`B(2) = 4`) are not. -/
theorem skew_median (p : PTm n) :
    Γ ⊢[PRAAx] isMed xB (num 5) (num 1) p ⋏
      (lt (num 5) (two * Ac xB (num 5) (num 0) p) ⋏ lt (num 5) (two * Bc xB (num 5) (num 2) p)) := by
  have b1 := B_count (Γ := Γ) 1 p; have a1 := A_count (Γ := Γ) 1 p
  have a0 := A_count (Γ := Γ) 0 p; have b2 := B_count (Γ := Γ) 2 p
  simp only [xv] at b1 a1 a0 b2; norm_num at b1 a1 a0 b2
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · exact le_congr (congrMul (.eqRefl _) b1).eqSymm (.eqRefl _) (le_of_eq_add (d := num 1) (by apply deriveNat; ipra_simps; norm_num))
  · exact le_congr (congrMul (.eqRefl _) a1).eqSymm (.eqRefl _) (le_of_eq_add (d := num 3) (by apply deriveNat; ipra_simps; norm_num))
  · exact le_congr (.eqRefl _) (congrMul (.eqRefl _) a0).eqSymm (le_of_eq_add (d := num 0) (by apply deriveNat; ipra_simps; norm_num))
  · exact le_congr (.eqRefl _) (congrMul (.eqRefl _) b2).eqSymm (le_of_eq_add (d := num 2) (by apply deriveNat; ipra_simps; norm_num))

/-- The positive and negative parts of the centred, scaled values `d_i = 5 x_i − 4`, cubed. -/
abbrev posB : PTm 2 := monus (num 5 * xB) (num 4) * monus (num 5 * xB) (num 4) * monus (num 5 * xB) (num 4)
abbrev negB : PTm 2 := monus (num 4) (num 5 * xB) * monus (num 4) (num 5 * xB) * monus (num 4) (num 5 * xB)

theorem scaled_at (i : ℕ) (x : PTm n) : Γ ⊢[PRAAx] num 5 * inst2 xB (num i) x ≐ num (5 * xv i) :=
  (congrMul (.eqRefl _) (x_at i x)).eqTrans (by apply deriveNat; ipra_simps; unfold xv; push_cast; ring)

theorem pos_at (i : ℕ) (x : PTm n) : Γ ⊢[PRAAx] inst2 posB (num i) x ≐ num ((5 * xv i - 4) ^ 3) := by
  have e : inst2 posB (num i) x = monus (num 5 * inst2 xB (num i) x) (num 4) *
      monus (num 5 * inst2 xB (num i) x) (num 4) * monus (num 5 * inst2 xB (num i) x) (num 4) := by simp [inst2]
  rw [e]
  have m := (congrMonus (scaled_at (Γ := Γ) i x) (.eqRefl _)).eqTrans (monus_num (5 * xv i) 4)
  exact (congrMul (congrMul m m) m).eqTrans (by apply deriveNat; ipra_simps; push_cast; ring)

theorem neg_at (i : ℕ) (x : PTm n) : Γ ⊢[PRAAx] inst2 negB (num i) x ≐ num ((4 - 5 * xv i) ^ 3) := by
  have e : inst2 negB (num i) x = monus (num 4) (num 5 * inst2 xB (num i) x) *
      monus (num 4) (num 5 * inst2 xB (num i) x) * monus (num 4) (num 5 * inst2 xB (num i) x) := by simp [inst2]
  rw [e]
  have m := (congrMonus (.eqRefl _) (scaled_at (Γ := Γ) i x)).eqTrans (monus_num 4 (5 * xv i))
  exact (congrMul (congrMul m m) m).eqTrans (by apply deriveNat; ipra_simps; push_cast; ring)

/-- The cleared third central moment: `∑ (5 x_i − 4)³ = 218 − 128 = 90 > 0`, i.e. `18/125`. -/
theorem skew_moment (x : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF posB) (num 5) x ≐ num 218) ⋏ ((ap2 (sumF negB) (num 5) x ≐ num 128) ⋏
      (ap2 (sumF posB) (num 5) x ≐ ap2 (sumF negB) (num 5) x + num 90)) := by
  have P : Γ ⊢[PRAAx] ap2 (sumF posB) (num 5) x ≐ num 218 := by
    refine (sum_five _ _).eqTrans ((congrAdd (congrAdd (congrAdd (congrAdd (pos_at 0 x) (pos_at 1 x))
      (pos_at 2 x)) (pos_at 3 x)) (pos_at 4 x)).eqTrans ?_)
    simp only [xv]; norm_num
    apply deriveNat; ipra_simps; norm_num
  have N : Γ ⊢[PRAAx] ap2 (sumF negB) (num 5) x ≐ num 128 := by
    refine (sum_five _ _).eqTrans ((congrAdd (congrAdd (congrAdd (congrAdd (neg_at 0 x) (neg_at 1 x))
      (neg_at 2 x)) (neg_at 3 x)) (neg_at 4 x)).eqTrans ?_)
    simp only [xv]; norm_num
    apply deriveNat; ipra_simps; norm_num
  refine .andI P (.andI N (P.eqTrans (.eqTrans ?_ (congrAdd N (.eqRefl _)).eqSymm)))
  apply deriveNat; ipra_simps; norm_num

end LeanProofs.IPRA.Probability.MedianSkew
