module
public import PA196.Commands.Store
@[expose] public section

/-!
Symbolic contracts for the nine-item AX stack and the paper's command words.
All large AX codes remain symbolic. In particular, the proof of discard is
specialized to its closed selector only after the symbolic contract is proved.
-/
namespace PA196.Commands
open M6.Source.Cantor Code

def pop : List Command := [.ax 0 0 0] ++ List.replicate 10 .shift
def push : List Command := [.ax 0 0 0] ++ List.replicate 8 .shift ++ [.mp 0]
def discard : List Command := [.mp 1, .ax 1 0 0] ++ List.replicate 9 .shift ++ [.mp 0]
def offset (u : Nat) : List Command := if u = 0 then [] else [.mp u]

/-- Eight Shifts expose the restricted propositional head and generalization.
No halt side condition is required, including when the saved top is `1`. -/
theorem ax_shift8 (c x y t w d h : Nat) :
    run ([.ax c x y] ++ List.replicate 8 .shift) ⟨t, w, d, h⟩ =
      some ⟨rho8 (d + x) c (h + y) d, pair t w, 0, U d h⟩ := by
  simp only [List.replicate_succ, List.replicate_zero, List.cons_append,
    List.nil_append, run, ax_step, Option.bind_some, heads,
    List.foldr_cons, List.foldr_nil]
  simp [step, decode_pair, head1, head2, head3, head4, head5, head6, rho8, ex, N]

/-- The paper's nine-shift identity, for arbitrary incoming caches and top. -/
theorem ax_shift9 (c x y t w d h : Nat) :
    run ([.ax c x y] ++ List.replicate 9 .shift) ⟨t, w, d, h⟩ =
      some ⟨U d h, w, 0, t⟩ := by
  have hl : List.replicate 9 Command.shift = List.replicate 8 .shift ++ [.shift] := rfl
  rw [hl, ← List.append_assoc, run_append, ax_shift8]
  simp [run, step, decode_pair]

/-- Pop preserves the current top and consumes one Cantor stack item. -/
theorem pop_total (t a w d h : Nat) :
    run pop ⟨t, pair a w, d, h⟩ = some ⟨t, w, 0, a⟩ := by
  have hl : List.replicate 10 Command.shift = List.replicate 9 .shift ++ [.shift] := rfl
  rw [pop, hl, ← List.append_assoc, run_append, ax_shift9]
  simp [run, step, decode_pair]

/-- Push saves any top, including falsity, and clears both caches. -/
theorem push_total (t w d h : Nat) :
    run push ⟨t, w, d, h⟩ = some ⟨0, pair t w, 0, 0⟩ := by
  rw [push, run_append, ax_shift8]
  simp [run, step]

def discardWith (c : Nat) : List Command :=
  [.mp c, .ax c 0 0] ++ List.replicate 9 .shift ++ [.mp 0]

theorem discardWith_total (c : Nat) (hc : 0 < c) (t w : Nat) :
    run (discardWith c) ⟨t, w, 0, 0⟩ = some ⟨0, w, 0, 0⟩ := by
  have he : I t c ≠ 0 := by
    intro hz
    have hh := (I_zero_iff t c).mp hz
    omega
  have hfirst : run [.mp c] ⟨t, w, 0, 0⟩ = some ⟨0, w, c, 0⟩ := by
    simp [run, step, he]
  change run ([.mp c] ++ ([.ax c 0 0] ++ List.replicate 9 .shift) ++ [.mp 0])
    ⟨t, w, 0, 0⟩ = _
  rw [run_append, run_append, hfirst]
  simp only [Option.bind_some, ax_shift9]
  simp [run, step]

theorem discard_total (t w : Nat) :
    run discard ⟨t, w, 0, 0⟩ = some ⟨0, w, 0, 0⟩ := by
  simpa only [discardWith, discard] using discardWith_total 1 (by decide) t w

theorem offset_total (u w : Nat) : run (offset u) ⟨0, w, 0, 0⟩ = some ⟨0, w, u, 0⟩ := by
  by_cases hu : u = 0
  · simp [offset, hu, run]
  · have he : I 0 u ≠ 0 := by simpa using hu
    simp [offset, hu, run, step, he]

def generalize (i : Nat) : List Command :=
  push ++ offset i ++ [.shift] ++ [.ax i 0 0] ++ List.replicate 9 .shift

theorem generalize_total (i a w : Nat) :
    run (generalize i) ⟨a, w, 0, 0⟩ = some ⟨U i a, w, 0, 0⟩ := by
  have hs : run [.shift] ⟨0, pair a w, i, 0⟩ = some ⟨0, w, i, a⟩ := by
    simp [run, step, decode_pair]
  have hp := append_total (push_total a w 0 0) (offset_total i (pair a w))
  have hps := append_total hp hs
  have h := append_total hps (ax_shift9 i 0 0 0 w i a)
  simpa only [generalize, List.append_assoc] using h

def mpSuffix (b : Nat) : List Command :=
  [.shift, .shift, .mp b] ++ [.ax b 0 0] ++ List.replicate 10 .shift

/-- The sole possible early halt in this suffix is its second Shift, when
the antecedent is falsity. Otherwise it returns the consequent and old stack. -/
theorem mpSuffix_result (a b w : Nat) :
    run (mpSuffix b) ⟨0, pair a (pair (I a b) w), 0, 0⟩ =
      if a = 1 then none else some ⟨b, w, 0, 0⟩ := by
  by_cases ha : a = 1
  · simp [mpSuffix, run, step, decode_pair, ha]
  · have hs : run [.shift, .shift, .mp b]
        ⟨0, pair a (pair (I a b) w), 0, 0⟩ = some ⟨b, pair 0 w, b, 0⟩ := by
      simp [run, step, decode_pair, ha]
    have hx : run ([.ax b 0 0] ++ List.replicate 10 .shift)
        ⟨b, pair 0 w, b, 0⟩ = some ⟨b, w, 0, 0⟩ := by
      have hl : List.replicate 10 Command.shift = List.replicate 9 .shift ++ [.shift] := rfl
      rw [hl, ← List.append_assoc, run_append, ax_shift9]
      simp [run, step, decode_pair]
    simp only [ha, ite_false]
    simpa only [mpSuffix, List.append_assoc] using append_total hs hx

#print axioms ax_shift9
#print axioms pop_total
#print axioms push_total
#print axioms discard_total
#print axioms generalize_total
#print axioms mpSuffix_result
end PA196.Commands
