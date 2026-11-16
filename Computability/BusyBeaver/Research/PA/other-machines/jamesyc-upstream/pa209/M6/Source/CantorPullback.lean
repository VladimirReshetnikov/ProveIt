module
public import M6.Source.Enumeration
@[expose] public section

/-! Bounded nonnegative-prefix sums are preserved by the Cantor right
projection. This is the twice-used diagonal lemma in the global credit proof. -/
namespace M6.Source.Enumeration
open Cantor

def prefixSum (q : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => prefixSum q n + q n

theorem prefixSum_congr (n : Nat) (h : ∀ i, i < n → q i = r i) :
    prefixSum q n = prefixSum r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixSum]
    rw [ih (fun i hi => h i (by omega)),h n (by omega)]

theorem prefixSum_add (q : Nat → Int) (a b : Nat) :
    prefixSum q (a+b) = prefixSum q a + prefixSum (fun i => q (a+i)) b := by
  induction b with
  | zero => simp [prefixSum]
  | succ b ih =>
    change prefixSum q (a+b) + q (a+b) =
      prefixSum q a + (prefixSum (fun i => q (a+i)) b + q (a+b))
    rw [ih]
    omega

theorem decode_diagonal (s y : Nat) (hy : y ≤ s) : decode (triangle s+y) = (s-y,y) := by
  have he : pair (s-y) y = triangle s+y := by simp only [pair,Nat.sub_add_cancel hy]
  rw [← he,decode_pair]

def pullback (q : Nat → Int) (n : Nat) : Int := q (decode n).2

theorem pullback_diagonal (q : Nat → Int) (s k : Nat) (hk : k ≤ s+1) :
    prefixSum (fun i => pullback q (triangle s+i)) k = prefixSum q k := by
  apply prefixSum_congr
  intro i hi
  simp only [pullback,decode_diagonal s i (by omega)]

private theorem complete_diagonals_nonnegative (q : Nat → Int) (s : Nat)
    (hq : ∀ k, k ≤ s → 0 ≤ prefixSum q k) :
    0 ≤ prefixSum (pullback q) (triangle s) := by
  induction s with
  | zero => simp [triangle,prefixSum]
  | succ s ih =>
    have old := ih (fun k hk => hq k (by omega))
    have now := hq (s+1) (by omega)
    have ht : triangle (s+1) = triangle s+(s+1) := by simp [triangle,Nat.add_assoc]
    rw [ht,prefixSum_add,pullback_diagonal q s (s+1) (by omega)]
    omega

theorem decode_diagonal_le (n : Nat) : (decode n).1+(decode n).2 ≤ n := by
  have h := triangle_ge ((decode n).1+(decode n).2)
  have he := pair_decode n
  simp only [pair] at he
  omega

/-- Only prefix sums up to the current diagonal are needed; no circular
hypothesis about uncomputed later enumeration words is introduced. -/
theorem pullback_nonnegative_bounded (q : Nat → Int) (n : Nat)
    (hq : ∀ k, k ≤ (decode n).1+(decode n).2 → 0 ≤ prefixSum q k) :
    0 ≤ prefixSum (pullback q) n := by
  let s := (decode n).1+(decode n).2
  have old := complete_diagonals_nonnegative q s hq
  have hy : (decode n).2 ≤ s := by dsimp [s]; omega
  have now := hq (decode n).2 hy
  have he : n = triangle s+(decode n).2 := (pair_decode n).symm
  rw [he,prefixSum_add,pullback_diagonal q s (decode n).2 (by omega)]
  omega

/-- The property remains true under one pullback on every bounded prefix, so
it can be reused a second time for AX's two additionally consumed fields. -/
theorem pullback_prefix_nonnegative (q : Nat → Int) (bound : Nat)
    (hq : ∀ k, k ≤ bound → 0 ≤ prefixSum q k) :
    ∀ k, k ≤ bound → 0 ≤ prefixSum (pullback q) k := by
  intro k hk
  apply pullback_nonnegative_bounded
  intro j hj
  exact hq j (Nat.le_trans hj (Nat.le_trans (decode_diagonal_le k) hk))

#print axioms pullback_nonnegative_bounded
#print axioms pullback_prefix_nonnegative
end M6.Source.Enumeration

