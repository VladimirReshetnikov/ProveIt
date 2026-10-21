import BusyBeaver.ZFC.EnumPerm

/-!
Uncompiled research adapter against EnumPerm at
 e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad.
No sealed source is changed. The all-natural proof is in LENGTH_PADDING.md.
This demonstrates the small generic library boundary, not a measured reduction
of the current specialized four-line encL_ge proof.
-/
namespace SetTheory.BusyBeaver.ZFC.EnumPerm.LengthPadding

open SetTheory.BusyBeaver.ZFC.EnumPerm

/-- Derive the packing bound from existing decoder facts, without arity cases. -/
theorem rest_le_pack (c : Cmd) (r : Nat) : r ≤ pack c r := by
  have h := decode_le (pack c r)
  rw [decode_pack] at h
  exact h

/-- The tail length is one less than the nonempty encoded word length. -/
theorem tail_length_le_encL (cs : List Cmd) : ∀ c : Cmd, cs.length ≤ encL c cs := by
  induction cs with
  | nil => intro c; exact Nat.zero_le _
  | cons c' cs ih =>
      intro c
      have h1 := ih c'
      have h2 := rest_le_pack c (encL c' cs + 1)
      simp only [List.length_cons, encL]
      omega

/-- Universal halting, unlike a normalized-state contract, survives every prefix. -/
theorem prefix_universal {u : List Cmd} (hu : ∀ w, cexec u w = none)
    (p : List Cmd) (w : W) : cexec (p ++ u) w = none := by
  rw [cexec_append]
  cases h : cexec p w with
  | none => rfl
  | some w' => exact hu w'

/-- A precise head/tail representation of N prepended padding commands. -/
def padded (q : Cmd) : Nat → Cmd → List Cmd → Cmd × List Cmd
  | 0, c, cs => (c, cs)
  | n + 1, c, cs =>
      let prev := padded q n c cs
      (q, prev.1 :: prev.2)

/-- This bound avoids any claims about neutral padding or fresh opcode fields. -/
theorem padded_tail_length (q : Cmd) : ∀ (n : Nat) (c : Cmd) (cs : List Cmd),
    (padded q n c cs).2.length = n + cs.length
  | 0, c, cs => by simp [padded]
  | n + 1, c, cs => by
      simp only [padded, List.length_cons, padded_tail_length q n c cs]
      omega

theorem padded_code_ge (q : Cmd) (n : Nat) (c : Cmd) (cs : List Cmd) :
    n ≤ encL (padded q n c cs).1 (padded q n c cs).2 := by
  have h := tail_length_le_encL (padded q n c cs).2 (padded q n c cs).1
  rw [padded_tail_length] at h
  omega

end SetTheory.BusyBeaver.ZFC.EnumPerm.LengthPadding
