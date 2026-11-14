import PA194FetchPrefix
import PA194FetchDecode
/-! Arithmetic proof adapted from M6.Source.Fetch; every literal
source binding is reproved against the PA194 program. -/

namespace PA194FetchSource.Fetch
open M6.Source

def registers (n l a : Nat) (f : Registers) : Registers :=
  FetchUnpair.registers l a 0 0 (write f 0 n)

def start (n l : Nat) (f : Registers) : Configuration := ⟨.at 25,registers n l 0 f⟩
def selected (n seed : Nat) (f : Registers) : Configuration :=
  ⟨.at 48,registers n (Cantor.decode seed).2 (Cantor.decode seed).1 f⟩

def decodeCost (seed : Nat) : Nat :=
  Unpair.loopCost seed (0,0) + (3*(Cantor.decode seed).2+1) + (3*(Cantor.decode seed).1+1)

private theorem bridge (n l : Nat) (f : Registers) :
    FetchPrefix.registers ⟨n,l,0,FetchUnpair.registers 0 0 0 0 f⟩ = registers n l 0 f := by
  funext r
  by_cases h0 : r = 0 <;> by_cases h8 : r = 8 <;> by_cases h3 : r = 3 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [FetchPrefix.registers,FetchUnpair.registers,registers,write]

/-- Positive continuation L consumes L-1, without advancing the fresh counter. -/
theorem positive (n l : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ 2 + decodeCost l ∧
      Steps PA194SourceProgram.sites m (start n (l+1) f) (selected n l f) := by
  have hp := FetchPrefix.positive n l (FetchUnpair.registers 0 0 0 0 f)
  simp only [FetchPrefix.configAt, bridge] at hp
  rcases FetchUnpair.fetch_decode l (write f 0 n) with ⟨m,hm,hbound,hd⟩
  refine ⟨2+m,by omega,by exact Nat.add_le_add_left hbound 2,?_⟩
  exact hp.append hd

/-- A fresh fetch consumes N and increments N, proving the exact exceptional
zero-pointer convention rather than subtracting one from the fresh candidate. -/
theorem fresh (n : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ 7*n+4 + decodeCost n ∧
      Steps PA194SourceProgram.sites m (start n 0 f) (selected (n+1) n f) := by
  have hp := FetchPrefix.fresh n (FetchUnpair.registers 0 0 0 0 f)
  simp only [FetchPrefix.configAt, bridge] at hp
  rcases FetchUnpair.fetch_decode n (write f 0 (n+1)) with ⟨m,hm,hbound,hd⟩
  refine ⟨7*n+4+m,by omega,by exact Nat.add_le_add_left hbound (7*n+4),?_⟩
  exact hp.append hd

/-- All clean source fetch invocations terminate at the literal selector port. -/
theorem total (n l : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ Steps PA194SourceProgram.sites m (start n l f)
      (selected (if l = 0 then n+1 else n) (if l = 0 then n else l-1) f) := by
  cases l with
  | zero =>
    rcases fresh n f with ⟨m,hm,_,hs⟩
    exact ⟨m,hm,hs⟩
  | succ l =>
    rcases positive n l f with ⟨m,hm,_,hs⟩
    exact ⟨m,hm,hs⟩

#print axioms positive
#print axioms fresh
#print axioms total
end PA194FetchSource.Fetch

