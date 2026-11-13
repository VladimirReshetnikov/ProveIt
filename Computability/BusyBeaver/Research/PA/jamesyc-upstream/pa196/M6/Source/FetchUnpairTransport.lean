module
public import M6.Source.FetchUnpairBinding
public import M6.Source.Unpair
public import M6.Source.SegmentTransfer
@[expose] public section

namespace M6.Source.FetchUnpair

def rename (r : Fin 9) : Fin 9 :=
  if r = 2 then 8 else if r = 8 then 2 else if r = 3 then 5 else if r = 5 then 3 else r

theorem rename_involution (r : Fin 9) : rename (rename r) = r :=
  (by decide : ∀ r : Fin 9, rename (rename r) = r) r

theorem rename_eq_iff (r s : Fin 9) : rename r = s ↔ r = rename s :=
  (by decide : ∀ r s : Fin 9, rename r = s ↔ r = rename s) r s

def regs (r : Registers) : Registers := fun k => r (rename k)

theorem regs_write (r : Registers) (k : Fin 9) (v : Nat) :
    regs (write r k v) = write (regs r) (rename k) v := by
  funext j
  simp [regs, write, rename_eq_iff]

def next : Option Nat → Option Nat
  | none => some 23
  | some k => some (k-3924)

def control : Control → Control
  | .at k => .at (k-3924)
  | .exited => .at 23
  | .halted => .halted
  | .malformed => .malformed

def embed (c : Configuration) : Configuration := ⟨control c.control, regs c.registers⟩

def instruction : Instruction → Instruction
  | .inc r n => .inc (rename r) (next n)
  | .dec r z n => .dec (rename r) (next z) (next n)
  | .jump n => .jump (next n)
  | .halt => .halt

private theorem destination_next (n : Option Nat) : destination (next n) = control (destination n) := by
  cases n <;> rfl

theorem execute_commutes (i : Instruction) (r : Registers) :
    execute (instruction i) (regs r) = embed (execute i r) := by
  cases i with
  | inc k n => simp [instruction, execute, embed, destination_next, regs_write, regs, rename_involution]
  | dec k z n =>
    by_cases h : r k = 0 <;>
      simp [instruction, execute, embed, destination_next, regs_write, regs, rename_involution, h]
  | jump n => simp [instruction, execute, embed, destination_next]
  | halt => rfl

/-- The two independently source-bound 14-instruction blocks differ only in
register renaming, ordinal shift, and their explicit exit destination. -/
theorem instructions_match (j : Fin 14) :
    fetchUnpairExpected[j.val] = instruction unpairExpected[j.val] :=
  (by decide : ∀ j : Fin 14, fetchUnpairExpected[j.val] = instruction unpairExpected[j.val]) j

def InBlock (c : Configuration) : Prop :=
  c.control = .exited ∨ ∃ j : Fin 14, c.control = .at (3933+j.val)

private theorem outcome_inBlock (j : Fin 14) (r : Registers) :
    InBlock (execute unpairExpected[j.val] r) := by
  have finite : ∀ j : Fin 14, ∀ q ∈
      (match unpairExpected[j.val] with
       | .inc _ n | .jump n => [destination n]
       | .dec _ z n => [destination z,destination n]
       | .halt => [.halted]),
      q = .exited ∨ ∃ k : Fin 14, q = .at (3933+k.val) := by decide
  have h := finite j
  generalize he : unpairExpected[j.val] = i at h ⊢
  cases i <;> simp only [execute, InBlock]
  · exact h _ (by simp)
  · split
    · exact h _ (by simp)
    · exact h _ (by simp)
  · exact h _ (by simp)
  · exact h _ (by simp)

theorem preserve (c : Configuration) (hc : InBlock c) : InBlock (step exactSites c) := by
  rcases c with ⟨q,r⟩
  rcases hc with h | ⟨j,h⟩
  · simp only at h
    subst q
    exact Or.inl rfl
  · simp only at h
    subst q
    rw [step_of_resolved (unpair_resolved_at j)]
    exact outcome_inBlock j r

theorem step_commutes (c : Configuration) (hc : InBlock c) (hne : c.control ≠ .exited) :
    step exactSites (embed c) = embed (step exactSites c) := by
  rcases c with ⟨q,r⟩
  rcases hc with h | ⟨j,h⟩
  · exact False.elim (hne h)
  · simp only at h
    subst q
    have he : 3933+j.val-3924 = 9+j.val := by omega
    change step exactSites ⟨.at (3933+j.val-3924),regs r⟩ = _
    rw [he, step_of_resolved (fetch_unpair_resolved_at j),
      step_of_resolved (unpair_resolved_at j), instructions_match]
    exact execute_commutes _ r

/-- Reuse the already proved Cantor loop by exact register/PC conjugacy.
The decoder exits into selector ordinal 23, not a normal root return. -/
theorem unpair (n : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ Unpair.loopCost n (0,0) +
      (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1) ∧
      Steps exactSites m
        (embed (Unpair.configAt 3933 ⟨n,0,0,0,f⟩))
        (embed (Unpair.exitAt ⟨(Cantor.decode n).2,(Cantor.decode n).1,0,0,f⟩)) := by
  exact transfer_until_exit embed InBlock preserve step_commutes
    (Unpair.unpair n f) (Or.inr ⟨⟨0,by decide⟩,rfl⟩) (by simp [Unpair.configAt]) rfl

def registers (l a x y : Nat) (frame : Registers) : Registers := fun r =>
  if r = 8 then l else if r = 3 then a else if r = 6 then x else if r = 7 then y else frame r

private theorem register_bridge (l a x y : Nat) (f : Registers) :
    regs (Unpair.registers ⟨l,a,x,y,regs f⟩) = registers l a x y f := by
  funext j
  simp only [regs, Unpair.registers, registers, rename_eq_iff, rename_involution]
  rfl

/-- All-natural selector decoding at the actual fetch port, with clean A,X,Y.
N,T,W,D,H and every other untouched source register retain their input values. -/
theorem fetch_decode (n : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ Unpair.loopCost n (0,0) +
      (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1) ∧
      Steps exactSites m ⟨.at 9,registers n 0 0 0 f⟩
        ⟨.at 23,registers (Cantor.decode n).2 (Cantor.decode n).1 0 0 f⟩ := by
  have h := unpair n (regs f)
  simpa only [embed, Unpair.configAt, Unpair.exitAt, control, register_bridge] using h

#print axioms fetch_decode
#print axioms unpair
end M6.Source.FetchUnpair

