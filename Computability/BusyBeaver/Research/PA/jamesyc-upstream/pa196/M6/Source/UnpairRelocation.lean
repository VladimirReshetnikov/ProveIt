module
public import M6.Source.FetchUnpairTransport
public import M6.Source.UnpairAddition
@[expose] public section

namespace M6.Source

/-- A register involution and literal port relocation for the common 14-step
Cantor decoder. Exit is a source ordinal, not an absorbing root-return state. -/
structure UnpairRelocation where
  rename : Fin 9 → Fin 9
  involution : ∀ r, rename (rename r) = r
  base : Nat
  exitPort : Nat

namespace UnpairRelocation

def regs (p : UnpairRelocation) (r : Registers) : Registers := fun j => r (p.rename j)

theorem rename_eq_iff (p : UnpairRelocation) (r s : Fin 9) :
    p.rename r = s ↔ r = p.rename s := by
  constructor
  · intro h
    have hh := congrArg p.rename h
    simpa only [p.involution] using hh
  · intro h
    rw [h,p.involution]

theorem regs_write (p : UnpairRelocation) (r : Registers) (k : Fin 9) (v : Nat) :
    p.regs (write r k v) = write (p.regs r) (p.rename k) v := by
  funext j
  simp [regs,write,p.rename_eq_iff]

def next (p : UnpairRelocation) : Option Nat → Option Nat
  | none => some p.exitPort
  | some k => some (p.base + (k-3933))

def control (p : UnpairRelocation) : Control → Control
  | .at k => .at (p.base + (k-3933))
  | .exited => .at p.exitPort
  | .halted => .halted
  | .malformed => .malformed

def embed (p : UnpairRelocation) (c : Configuration) : Configuration :=
  ⟨p.control c.control,p.regs c.registers⟩

def instruction (p : UnpairRelocation) : Instruction → Instruction
  | .inc r n => .inc (p.rename r) (p.next n)
  | .dec r z n => .dec (p.rename r) (p.next z) (p.next n)
  | .jump n => .jump (p.next n)
  | .halt => .halt

private theorem destination_next (p : UnpairRelocation) (n : Option Nat) :
    destination (p.next n) = p.control (destination n) := by cases n <;> rfl

theorem execute_commutes (p : UnpairRelocation) (i : Instruction) (r : Registers) :
    execute (p.instruction i) (p.regs r) = p.embed (execute i r) := by
  cases i with
  | inc k n => simp [instruction,execute,embed,destination_next,regs_write,regs,p.involution]
  | dec k z n =>
    by_cases h : r k = 0 <;>
      simp [instruction,execute,embed,destination_next,regs_write,regs,p.involution,h]
  | jump n => simp [instruction,execute,embed,destination_next]
  | halt => rfl

def Bound (p : UnpairRelocation) : Prop :=
  ∀ j : Fin 14, resolveAt exactSites (p.base+j.val) = some (p.instruction unpairExpected[j.val])

theorem step_commutes (p : UnpairRelocation) (hbound : p.Bound)
    (c : Configuration) (hc : FetchUnpair.InBlock c) (hne : c.control ≠ .exited) :
    step exactSites (p.embed c) = p.embed (step exactSites c) := by
  rcases c with ⟨q,r⟩
  rcases hc with h | ⟨j,h⟩
  · exact False.elim (hne h)
  · simp only at h
    subst q
    change step exactSites ⟨.at (p.base+(3933+j.val-3933)),p.regs r⟩ = _
    have he : 3933+j.val-3933 = j.val := by omega
    rw [he,step_of_resolved (hbound j),step_of_resolved (unpair_resolved_at j)]
    exact p.execute_commutes _ r

/-- Universal arithmetic reuse for an exactly bound source copy. The caller
must prove the literal 14-row binding; no semantic macro supplier is assumed. -/
theorem unpair_add (p : UnpairRelocation) (hbound : p.Bound) (n h : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ Unpair.loopCost n (0,0) +
      (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1) ∧
      Steps exactSites m
        (p.embed (Unpair.configAt 3933 ⟨n,h,0,0,f⟩))
        (p.embed (Unpair.exitAt ⟨(Cantor.decode n).2,h+(Cantor.decode n).1,0,0,f⟩)) := by
  exact transfer_until_exit p.embed FetchUnpair.InBlock FetchUnpair.preserve
    (p.step_commutes hbound) (Unpair.unpair_add n h f)
    (Or.inr ⟨⟨0,by decide⟩,rfl⟩) (by simp [Unpair.configAt]) rfl

#print axioms unpair_add
end UnpairRelocation
end M6.Source

