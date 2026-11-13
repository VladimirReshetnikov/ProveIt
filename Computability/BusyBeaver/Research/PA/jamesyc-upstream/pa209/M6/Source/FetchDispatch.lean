module
public import M6.Source.Dispatch
@[expose] public section
namespace M6.Source.FetchDispatch

def seed (n l : Nat) : Nat := if l = 0 then n else l-1
def nextN (n l : Nat) : Nat := if l = 0 then n+1 else n

def commandEntry (n l : Nat) (f : Registers) : Configuration :=
  let p := Cantor.decode (seed n l)
  ⟨.at (Dispatch.target p.1),Fetch.registers (nextN n l) p.2 (p.1-2) f⟩

private theorem write_a (n l a b : Nat) (f : Registers) :
    write (Fetch.registers n l a f) 3 b = Fetch.registers n l b f := by
  funext r
  by_cases h8 : r = 8 <;> by_cases h3 : r = 3 <;> by_cases h6 : r = 6 <;>
    by_cases h7 : r = 7 <;>
    simp_all [write, Fetch.registers, FetchUnpair.registers]

/-- Every clean invocation reaches precisely the S, MP or AX entry selected by
its decoded field. Both fresh and positive continuation conventions are exact. -/
theorem total (n l : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ Steps exactSites m (Fetch.start n l f) (commandEntry n l f) := by
  rcases Fetch.total n l f with ⟨m,hm,hfetch⟩
  have hd := Dispatch.total (Cantor.decode (seed n l)).1
    (Fetch.registers (nextN n l) (Cantor.decode (seed n l)).2 (Cantor.decode (seed n l)).1 f)
    (by simp [Fetch.registers,FetchUnpair.registers])
  simp only [write_a] at hd
  refine ⟨m+Dispatch.cost (Cantor.decode (seed n l)).1,by omega,?_⟩
  exact hfetch.append hd

#print axioms total
end M6.Source.FetchDispatch

