module
public import M6.Source.Fetch
@[expose] public section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace M6.Source.Dispatch

theorem resolve_23 : resolveAt exactSites 23 = some (.dec 3 (some 3911) (some 24)) := by decide
theorem resolve_24 : resolveAt exactSites 24 = some (.dec 3 (some 3804) (some 25)) := by decide

private theorem write_same (r : Registers) (k : Fin 9) : write r k (r k) = r := by
  funext j
  simp only [write]
  split <;> simp_all

private theorem write_twice (r : Registers) (k : Fin 9) (a b : Nat) :
    write (write r k a) k b = write r k b := by
  funext j
  by_cases h : j = k <;> simp [write,h]

theorem zero (r : Registers) (ha : r 3 = 0) :
    Steps exactSites 1 ⟨.at 23,r⟩ ⟨.at 3911,r⟩ := by
  apply Steps.cons
  rw [step_of_resolved resolve_23]
  simp only [execute, ha, ↓reduceIte, destination]
  exact Steps.refl _

theorem one (r : Registers) (ha : r 3 = 1) :
    Steps exactSites 2 ⟨.at 23,r⟩ ⟨.at 3804,write r 3 0⟩ := by
  apply Steps.cons
  rw [step_of_resolved resolve_23]
  simp only [execute, ha, Nat.reduceEqDiff, ↓reduceIte, destination, Nat.reduceSub]
  apply Steps.cons
  rw [step_of_resolved resolve_24]
  simp only [execute, write, ↓reduceIte, destination]
  exact Steps.refl _

theorem many (a : Nat) (r : Registers) (ha : r 3 = a+2) :
    Steps exactSites 2 ⟨.at 23,r⟩ ⟨.at 25,write r 3 a⟩ := by
  apply Steps.cons
  rw [step_of_resolved resolve_23]
  have hn : a+2 ≠ 0 := by omega
  simp only [execute, ha, hn, ↓reduceIte, destination]
  apply Steps.cons
  rw [step_of_resolved resolve_24]
  have hread : write r 3 (a+2-1) 3 = a+1 := by simp [write]
  have hn' : a+1 ≠ 0 := by omega
  simp only [execute, hread, hn', ↓reduceIte, destination, Nat.add_sub_cancel, write_twice]
  exact Steps.refl _

def target (a : Nat) : Nat := if a = 0 then 3911 else if a = 1 then 3804 else 25
def cost (a : Nat) : Nat := if a = 0 then 1 else 2

/-- Exact three-way dispatch: S, MP, or AX with selector minus two. -/
theorem total (a : Nat) (r : Registers) (ha : r 3 = a) :
    Steps exactSites (cost a) ⟨.at 23,r⟩ ⟨.at (target a),write r 3 (a-2)⟩ := by
  cases a with
  | zero =>
    have hw : write r 3 0 = r := by rw [← ha]; exact write_same r 3
    simpa only [cost,target,↓reduceIte,Nat.zero_sub,hw] using zero r ha
  | succ a =>
    cases a with
    | zero => exact one r ha
    | succ a =>
      have ht : target (a+2) = 25 := by simp [target]
      have hc : cost (a+2) = 2 := by simp [cost]
      change Steps exactSites (cost (a+2)) ⟨.at 23,r⟩ ⟨.at (target (a+2)),write r 3 (a+2-2)⟩
      simpa only [ht,hc,Nat.add_sub_cancel] using many a r ha

#print axioms total
end M6.Source.Dispatch

