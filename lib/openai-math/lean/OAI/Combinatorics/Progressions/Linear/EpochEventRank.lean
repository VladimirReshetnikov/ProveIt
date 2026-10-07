import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def epochStackRank (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r * (d + 1) ^ rs.length + epochStackRank d rs

inductive EpochStackEvent (d : ℕ) : List ℕ → List ℕ → Prop
  | head {r r' : ℕ} {xs ys : List ℕ} (drop : r' < r) (length : ys.length = xs.length)
      (bounded : ∀ q ∈ ys, q ≤ d) : EpochStackEvent d (r :: xs) (r' :: ys)
  | tail {r : ℕ} {xs ys : List ℕ} (event : EpochStackEvent d xs ys) :
      EpochStackEvent d (r :: xs) (r :: ys)

theorem EpochStackEvent.length_eq {d : ℕ} {xs ys : List ℕ} (h : EpochStackEvent d xs ys) :
    ys.length = xs.length := by
  induction h with
  | head _ hlen _ => simpa only [List.length_cons] using congrArg Nat.succ hlen
  | tail _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem epochStackRank_lt (d : ℕ) (xs : List ℕ) (hbounded : ∀ q ∈ xs, q ≤ d) :
    epochStackRank d xs < (d + 1) ^ xs.length := by
  revert hbounded
  induction xs with
  | nil => simp [epochStackRank]
  | cons r xs ih =>
    intro hbounded
    have hr : r ≤ d := hbounded r (by simp)
    have ht := ih (fun q hq => hbounded q (by simp [hq]))
    change r * (d + 1) ^ xs.length + epochStackRank d xs < (d + 1) ^ (xs.length + 1)
    calc
      r * (d + 1) ^ xs.length + epochStackRank d xs <
          r * (d + 1) ^ xs.length + (d + 1) ^ xs.length := Nat.add_lt_add_left ht _
      _ = (r + 1) * (d + 1) ^ xs.length := by ring
      _ ≤ (d + 1) * (d + 1) ^ xs.length := Nat.mul_le_mul_right _ (Nat.add_le_add_right hr 1)
      _ = (d + 1) ^ (xs.length + 1) := by rw [pow_succ]; ring

theorem EpochStackEvent.rank_lt {d : ℕ} {xs ys : List ℕ} (h : EpochStackEvent d xs ys) :
    epochStackRank d ys < epochStackRank d xs := by
  induction h with
  | @head r r' xs ys hdrop hlen hbounded =>
    have htail := epochStackRank_lt d ys hbounded
    change r' * (d + 1) ^ ys.length + epochStackRank d ys <
      r * (d + 1) ^ xs.length + epochStackRank d xs
    rw [hlen] at htail ⊢
    calc
      r' * (d + 1) ^ xs.length + epochStackRank d ys <
          r' * (d + 1) ^ xs.length + (d + 1) ^ xs.length := Nat.add_lt_add_left htail _
      _ = (r' + 1) * (d + 1) ^ xs.length := by ring
      _ ≤ r * (d + 1) ^ xs.length := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hdrop)
      _ ≤ r * (d + 1) ^ xs.length + epochStackRank d xs := Nat.le_add_right _ _
  | @tail r xs ys hevent ih =>
    change r * (d + 1) ^ ys.length + epochStackRank d ys <
      r * (d + 1) ^ xs.length + epochStackRank d xs
    rw [hevent.length_eq]
    exact Nat.add_lt_add_left ih _

theorem epochEventChain_length_le_rank (d n : ℕ) (states : ℕ → List ℕ)
    (hsteps : ∀ i, i < n → EpochStackEvent d (states i) (states (i + 1))) :
    n ≤ epochStackRank d (states 0) := by
  induction n generalizing states with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hfirst := (hsteps 0 (by omega)).rank_lt
    have hrest := ih (fun i => states (i + 1)) (fun i hi => hsteps (i + 1) (by omega))
    simp only [Nat.zero_add] at hfirst hrest
    omega

theorem epochEventChain_bound (d n : ℕ) (states : ℕ → List ℕ)
    (hbounded : ∀ q ∈ states 0, q ≤ d)
    (hsteps : ∀ i, i < n → EpochStackEvent d (states i) (states (i + 1))) :
    n ≤ (d + 1) ^ (states 0).length - 1 := by
  have hlength := epochEventChain_length_le_rank d n states hsteps
  have hrank := epochStackRank_lt d (states 0) hbounded
  omega

end Erdos3

end

end OAI
