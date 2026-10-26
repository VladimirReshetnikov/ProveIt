import Mathlib.Data.Nat.Pairing

namespace PostBaseline.FormulaMinimum
private theorem pair_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' :=
  ((show StrictMono (fun a => Nat.pair a b) from fun _ _ h =>
    Nat.pair_lt_pair_left b h).monotone ha).trans
      ((show StrictMono (Nat.pair a') from fun _ _ h =>
        Nat.pair_lt_pair_right a' h).monotone hb)

def atomCode (n : ℕ) := Nat.pair 0 n + 1
def forkCode (a b : ℕ) := Nat.pair (a+1) b + 1

private theorem fork_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    forkCode a b ≤ forkCode a' b' :=
  Nat.add_le_add_right (pair_mono (Nat.add_le_add_right ha 1) hb) 1

private theorem atom_pos (n : ℕ) : 1 ≤ atomCode n := by
  unfold atomCode
  omega

theorem variable_min (tag i j : ℕ) :
    44 ≤ forkCode (atomCode tag) (forkCode (atomCode i) (atomCode j)) :=
  (by decide : 44 ≤ forkCode 1 (forkCode 1 1)).trans
    (fork_mono (atom_pos tag) (fork_mono (atom_pos i) (atom_pos j)))

theorem connective_min (tag payload : ℕ) (htag : 3 ≤ tag) :
    44 ≤ forkCode (atomCode tag) payload :=
  (by decide : 44 ≤ forkCode (atomCode 3) 0).trans
    (fork_mono (Nat.add_le_add_right (pair_mono le_rfl htag) 1) (Nat.zero_le _))

#print axioms PostBaseline.FormulaMinimum.variable_min
#print axioms PostBaseline.FormulaMinimum.connective_min
end PostBaseline.FormulaMinimum
