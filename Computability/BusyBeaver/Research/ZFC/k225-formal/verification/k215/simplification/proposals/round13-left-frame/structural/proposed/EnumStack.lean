import BusyBeaver.ZFC.KCode222

/-! Stack semantics common to the dominated and command-permuted enumerators.
No command decoder, scheduler, state type or new semantic parameter is introduced. -/

namespace SetTheory.BusyBeaver.ZFC.EnumStack

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222

attribute [local irreducible] P

abbrev unP (z : Nat) : Nat × Nat := Cantor.ofNat z

theorem unP_P' (x y : Nat) : unP (P x y) = (x, y) := unP_P x y

/-- The stack after AX: `tw` first, then GEN of the cache at `u`, then rho8 … rho1. -/
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w)))))))))

def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle222 a b c

/-- The stream after dropping `k` entries. -/
def tailN : Nat → Nat → Nat
  | 0, z => z
  | k + 1, z => tailN k (unP z).2

/-- Every entry of a stream is derivable. -/
def Good (z : Nat) : Prop := ∀ k, C222 (unP (tailN k z)).1

theorem tailN_zero : ∀ k, tailN k 0 = 0
  | 0 => rfl
  | k + 1 => by
      have h0 : (unP 0).2 = 0 := rfl
      simp only [tailN, h0, tailN_zero k]

theorem good_zero : Good 0 := fun k => by rw [tailN_zero k]; exact C222.truth

theorem good_cons {x z : Nat} (hx : C222 x) (hz : Good z) : Good (P x z) := by
  intro k
  cases k with
  | zero => simpa [tailN, unP_P'] using hx
  | succ k => simpa [tailN, unP_P'] using hz k

theorem gate_good (a b c : Nat) : C222 (gate a b c) := by
  unfold gate
  split
  · exact C222.truth
  · rename_i h
    exact C222.bundle a b c (fun e => h (Or.inl e)) (fun e => h (Or.inr e))

theorem axStack_good (a h b c u t w : Nat) (hh : C222 h) (ht : C222 t) (hw : Good w) :
    Good (axStack a h b c u t w) :=
  good_cons (C222.r1 a b) <| good_cons (C222.r2 a b c) <| good_cons (C222.r3 a b c) <|
    good_cons (C222.r4 a b c) <| good_cons (C222.r5 a b c) <| good_cons (C222.r6 a c) <|
    good_cons (C222.rG a b c) <| good_cons (C222.r8 a b c u) <| good_cons (C222.gen u hh) <|
    good_cons ht hw

theorem wim_ne_one (a b : Nat) : wim a b ≠ 1 := by simp only [wim]; omega

theorem wal_ne_one (a b : Nat) : wal a b ≠ 1 := by simp only [wal]; omega

theorem gate_ne_one (a b c : Nat) : gate a b c ≠ 1 := by
  unfold gate; split
  · omega
  · exact wim_ne_one _ _

theorem gate_self (a b : Nat) : gate a b a = 0 := by simp [gate]

end SetTheory.BusyBeaver.ZFC.EnumStack
