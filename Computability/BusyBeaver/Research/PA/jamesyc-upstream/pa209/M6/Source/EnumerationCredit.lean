module
public import M6.Source.CantorPullback
@[expose] public section

namespace M6.Source.Enumeration
open Cantor

def balance (n : Nat) : Int := prefixSum (fun k => weight (word k)) n
def q (n : Nat) : Int := weight (residual n) + 1

theorem q_sum (n : Nat) : prefixSum q (n+1) = 1 + balance n + (n : Int) := by
  induction n with
  | zero => simp [prefixSum,q,residual,balance,weight]
  | succ n ih =>
    change prefixSum q (n+1) + q (n+1) = 1 + balance (n+1) + ((n+1 : Nat) : Int)
    rw [ih]
    simp only [q,residual_succ,balance,prefixSum,Int.natCast_add,Int.natCast_one]
    omega

theorem q_prefix_nonnegative (bound : Nat)
    (hb : ∀ j, j < bound → 0 ≤ balance j + (j : Int)) :
    ∀ k, k ≤ bound → 0 ≤ prefixSum q k := by
  intro k hk
  cases k with
  | zero => simp [prefixSum]
  | succ k =>
    rw [q_sum]
    have h := hb k (by omega)
    omega

private theorem parse_ax_diagonal (s y : Nat) (hy : y+2 ≤ s) :
    parse (triangle s+y) =
      ⟨.ax (s-y-2) (decode (decode y).2).1 (decode y).1,(decode (decode y).2).2⟩ := by
  have hys : y ≤ s := by omega
  have he : s-y = (s-y-2)+2 := by omega
  simp only [parse,decode_diagonal s y hys]
  rw [he]
  rfl

theorem ax_word_weight (s y : Nat) (hy : y+2 ≤ s) :
    weight (word (triangle s+y)) = 9 + pullback (pullback q) y := by
  simp only [word,parse_ax_diagonal s y hy,weight,commandWeight,pullback,q]
  omega

/-- Complete weights of the first k AX words in a diagonal; both field
consumptions appear explicitly as two Cantor-right-projection pullbacks. -/
theorem ax_prefix_weight (s k : Nat) (hk : k+1 ≤ s) :
    prefixSum (fun y => weight (word (triangle s+y))) k =
      9*(k : Int) + prefixSum (pullback (pullback q)) k := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    change prefixSum (fun y => weight (word (triangle s+y))) k +
      weight (word (triangle s+k)) =
      9*((k+1 : Nat) : Int) + (prefixSum (pullback (pullback q)) k + pullback (pullback q) k)
    rw [ih (by omega),ax_word_weight s k (by omega)]
    simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_one]
    omega

/-- This bound uses only earlier indices j<s-1, not a global safety claim.
It is the quantitative supplier for the subsequent diagonal induction. -/
theorem ax_prefix_lower (s k : Nat) (hk : k+1 ≤ s)
    (hb : ∀ j, j < s-1 → 0 ≤ balance j + (j : Int)) :
    9*(k : Int) ≤ prefixSum (fun y => weight (word (triangle s+y))) k := by
  have hq := q_prefix_nonnegative (s-1) hb
  have once := pullback_prefix_nonnegative q (s-1) hq
  have twice := pullback_prefix_nonnegative (pullback q) (s-1) once
  have h := twice k (by omega)
  rw [ax_prefix_weight s k hk]
  omega

private theorem mp_word_weight (s : Nat) (hs : 1 ≤ s) :
    weight (word (triangle s+(s-1))) = weight (residual (decode (s-1)).2) := by
  have he : s-(s-1) = 1 := by omega
  simp only [word,parse,decode_diagonal s (s-1) (by omega)]
  rw [he]
  simp only [weight,commandWeight,Int.zero_add]

private theorem shift_word_weight (s : Nat) :
    weight (word (triangle s+s)) = -1 + weight (residual s) := by
  simp only [word,parse,decode_diagonal s s (Nat.le_refl _),Nat.sub_self,weight,commandWeight]

private theorem mp_word_lower (s : Nat) (hs : 1 ≤ s) :
    -((s-1 : Nat) : Int) ≤ weight (word (triangle s+(s-1))) := by
  rw [mp_word_weight s hs]
  have h1 := residual_weight_lower (decode (s-1)).2
  have h2 := (decode_bounds (s-1)).2
  omega

private theorem before_shift_lower (s : Nat) (hs : 2 ≤ s)
    (hb : ∀ j, j < s-1 → 0 ≤ balance j + (j : Int)) :
    8*((s-1 : Nat) : Int) ≤ prefixSum (fun y => weight (word (triangle s+y))) s := by
  have hax := ax_prefix_lower s (s-1) (by omega) hb
  have hmp := mp_word_lower s (by omega)
  have he : s = (s-1)+1 := by omega
  have hstep := congrArg (prefixSum (fun y => weight (word (triangle s+y)))) he
  rw [prefixSum] at hstep
  rw [hstep]
  omega

/-- Every complete-word prefix of a later diagonal has nonnegative relative
weight. Only previously established small-index balance bounds are used. -/
theorem diagonal_prefix_nonnegative (s : Nat) (hs : 2 ≤ s)
    (hb : ∀ j, j < s-1 → 0 ≤ balance j + (j : Int))
    (k : Nat) (hk : k ≤ s+1) :
    0 ≤ prefixSum (fun y => weight (word (triangle s+y))) k := by
  by_cases hax : k ≤ s-1
  · have h := ax_prefix_lower s k (by omega) hb
    omega
  · have hbshift := before_shift_lower s hs hb
    by_cases he : k = s
    · subst k; omega
    · have he : k = s+1 := by omega
      subst k
      rw [prefixSum,shift_word_weight]
      have hlast := residual_weight_lower s
      omega

def GoodDiagonal (s : Nat) : Prop :=
  (∀ n, n < triangle s → -3 ≤ balance n ∧ 0 ≤ balance n + (n : Int)) ∧
  -3 ≤ balance (triangle s)

private theorem word_zero : word 0 = [.shift] := by
  simp [word,parse,decode,advance,residual]
private theorem word_one : word 1 = [.mp 0] := by
  simp [word,parse,decode,advance,residual]
private theorem word_two : word 2 = [.shift,.shift] := by
  simp [word,parse,decode,advance,residual]

private theorem good_two : GoodDiagonal 2 := by
  have h0 : balance 0 = 0 := rfl
  have h1 : balance 1 = -1 := by simp [balance,prefixSum,word_zero,weight,commandWeight]
  have h2 : balance 2 = -1 := by simp [balance,prefixSum,word_zero,word_one,weight,commandWeight]
  have h3 : balance 3 = -3 := by simp [balance,prefixSum,word_zero,word_one,word_two,weight,commandWeight]
  constructor
  · intro n hn
    change n < 3 at hn
    have he : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases he with rfl | rfl | rfl <;> simp [h0,h1,h2]
  · change -3 ≤ balance 3
    rw [h3]
    omega

private theorem good_next (s : Nat) (hs : 2 ≤ s) (hg : GoodDiagonal s) : GoodDiagonal (s+1) := by
  have hb : ∀ j, j < s-1 → 0 ≤ balance j + (j : Int) := by
    intro j hj
    exact (hg.1 j (by have := triangle_ge s; omega)).2
  have hdiag := diagonal_prefix_nonnegative s hs hb
  have ht : triangle (s+1) = triangle s+(s+1) := by simp [triangle,Nat.add_assoc]
  have hthree : 3 ≤ triangle s := by
    by_cases he : s = 2
    · subst s; decide
    · have := triangle_ge s; omega
  constructor
  · intro n hn
    by_cases hold : n < triangle s
    · exact hg.1 n hold
    · have hy : n-triangle s ≤ s := by rw [ht] at hn; omega
      have he : n = triangle s+(n-triangle s) := by omega
      have h := hdiag (n-triangle s) (by omega)
      have hb0 := hg.2
      have hbn : balance n = balance (triangle s) +
          prefixSum (fun y => weight (word (triangle s+y))) (n-triangle s) := by
        change prefixSum (fun k => weight (word k)) n = _
        rw [he,prefixSum_add]
        simp only [Nat.add_sub_cancel_left,balance]
      rw [hbn]
      constructor <;> omega
  · have h := hdiag (s+1) (Nat.le_refl _)
    have hb0 := hg.2
    change -3 ≤ prefixSum (fun k => weight (word k)) (triangle (s+1))
    rw [ht,prefixSum_add]
    change -3 ≤ balance (triangle s) + _
    omega

private theorem good_all (s : Nat) : GoodDiagonal (s+2) := by
  induction s with
  | zero => exact good_two
  | succ s ih => exact good_next (s+2) (by omega) ih

/-- Every complete candidate-word boundary has credit at least minus three.
Within-word prefixes and source safety remain separate from this theorem. -/
theorem balance_lower (n : Nat) : -3 ≤ balance n ∧ 0 ≤ balance n + (n : Int) := by
  exact (good_all n).1 n (by have := triangle_ge (n+2); omega)

private theorem prefix_weight_lower (cs p rest : List Command) (h : cs = p ++ rest) :
    -(cs.length : Int) ≤ weight p := by
  have hl := congrArg List.length h
  simp only [List.length_append] at hl
  have hw := weight_lower p
  omega

private theorem prefix_cons_lower (c : Command) (r : Nat) (p rest : List Command)
    (h : c :: residual r = p ++ rest) (hne : p ≠ []) :
    commandWeight c - (r : Int) ≤ weight p := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons d ds =>
    simp only [List.cons_append,List.cons.injEq] at h
    rcases h with ⟨hcd,ht⟩
    subst d
    have hl := congrArg List.length ht
    simp only [List.length_append] at hl
    have hr := residual_length_le r
    have hw := weight_lower ds
    simp only [weight]
    omega

/-- EVERY within-word enumeration prefix has credit at least minus three,
including all fields consumed on unsuccessful MP and AX paths. -/
theorem every_prefix_credit (n : Nat) (p rest : List Command) (hp : word n = p ++ rest) :
    -3 ≤ balance n + weight p := by
  by_cases hempty : p = []
  · subst p
    simpa only [weight,Int.add_zero] using (balance_lower n).1
  · by_cases hsmall : n < 3
    · have hw := prefix_weight_lower (word n) p rest hp
      have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hn with rfl | rfl | rfl
      all_goals simp only [word_zero,word_one,word_two,List.length_cons,List.length_nil] at hw
      all_goals simp [balance,prefixSum,word_zero,word_one,word_two,weight,commandWeight]
      all_goals omega
    · let y := (decode n).2
      let s := (decode n).1+y
      have hy : y ≤ s := by dsimp [s]; omega
      have he : n = triangle s+y := (pair_decode n).symm
      have hs : 2 ≤ s := by
        by_cases hz : s = 0
        · have hy0 : y = 0 := by omega
          rw [hz,hy0] at he
          simp only [triangle,Nat.zero_add] at he
          omega
        · by_cases h1 : s = 1
          · rw [h1] at he
            simp only [triangle,Nat.zero_add] at he
            omega
          · omega
      have hb0 := (balance_lower (triangle s)).1
      have hbn : balance n = balance (triangle s) +
          prefixSum (fun i => weight (word (triangle s+i))) y := by
        calc
          balance n = balance (triangle s+y) := congrArg balance he
          _ = _ := prefixSum_add _ _ _
      rw [he] at hp
      by_cases hax : y+2 ≤ s
      · have hw : word (triangle s+y) =
            .ax (s-y-2) (decode (decode y).2).1 (decode y).1 :: residual (decode (decode y).2).2 := by
          simp only [word,parse_ax_diagonal s y hax]
        rw [hw] at hp
        have hpre := prefix_cons_lower _ _ p rest hp hempty
        simp only [commandWeight] at hpre
        have ht1 := (decode_bounds y).2
        have ht2 := (decode_bounds (decode y).2).2
        have hd := ax_prefix_lower s y (by omega) (fun j _ => (balance_lower j).2)
        rw [hbn]
        omega
      · by_cases hlast : y = s
        · rw [hlast] at hp hbn
          have hw : word (triangle s+s) = .shift :: residual s := by
            simp only [word,parse,decode_diagonal s s (Nat.le_refl _),Nat.sub_self]
          rw [hw] at hp
          have hpre := prefix_cons_lower _ _ p rest hp hempty
          simp only [commandWeight] at hpre
          have hd := before_shift_lower s hs (fun j _ => (balance_lower j).2)
          rw [hbn]
          omega
        · have htag : s-y = 1 := by omega
          have hw : word (triangle s+y) = .mp (decode y).1 :: residual (decode y).2 := by
            simp only [word,parse,decode_diagonal s y hy]
            rw [htag]
          rw [hw] at hp
          have hpre := prefix_cons_lower _ _ p rest hp hempty
          simp only [commandWeight] at hpre
          have ht := (decode_bounds y).2
          have hd := ax_prefix_lower s y (by omega) (fun j _ => (balance_lower j).2)
          rw [hbn]
          omega

/-- Nine initial wrappers minus the exact global enumeration debt leave at
least six. Connecting wrappers to source arithmetic is a separate invariant. -/
theorem initial_wrapper_credit (n : Nat) (p rest : List Command) (hp : word n = p ++ rest) :
    6 ≤ 9 + balance n + weight p := by
  have h := every_prefix_credit n p rest hp
  omega

#print axioms every_prefix_credit
#print axioms initial_wrapper_credit
#print axioms balance_lower
#print axioms q_prefix_nonnegative
#print axioms ax_prefix_lower
end M6.Source.Enumeration

