import PA194Fetch
/-! Arithmetic proof adapted from M6.Source.Dispatch; every literal
source binding is reproved against the PA194 program. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace PA194FetchSource.Dispatch
open M6.Source

theorem resolve_48 : resolveAt PA194SourceProgram.sites 48 = some (.dec 3 (some 3661) (some 49)) := by
  rw [PA194SourceProgram.resolve_tree]
  decide +kernel
theorem resolve_49 : resolveAt PA194SourceProgram.sites 49 = some (.dec 3 (some 3554) (some 50)) := by
  rw [PA194SourceProgram.resolve_tree]
  decide +kernel

private theorem write_same (r : Registers) (k : Fin 9) : write r k (r k) = r := by
  funext j
  simp only [write]
  split <;> simp_all

private theorem write_twice (r : Registers) (k : Fin 9) (a b : Nat) :
    write (write r k a) k b = write r k b := by
  funext j
  by_cases h : j = k <;> simp [write,h]

theorem zero (r : Registers) (ha : r 3 = 0) :
    Steps PA194SourceProgram.sites 1 ⟨.at 48,r⟩ ⟨.at 3661,r⟩ := by
  apply Steps.cons
  rw [step_of_resolved resolve_48]
  simp only [execute, ha, ↓reduceIte, destination]
  exact Steps.refl _

theorem one (r : Registers) (ha : r 3 = 1) :
    Steps PA194SourceProgram.sites 2 ⟨.at 48,r⟩ ⟨.at 3554,write r 3 0⟩ := by
  apply Steps.cons
  rw [step_of_resolved resolve_48]
  simp only [execute, ha, Nat.reduceEqDiff, ↓reduceIte, destination, Nat.reduceSub]
  apply Steps.cons
  rw [step_of_resolved resolve_49]
  simp only [execute, write, ↓reduceIte, destination]
  exact Steps.refl _

theorem many (a : Nat) (r : Registers) (ha : r 3 = a+2) :
    Steps PA194SourceProgram.sites 2 ⟨.at 48,r⟩ ⟨.at 50,write r 3 a⟩ := by
  apply Steps.cons
  rw [step_of_resolved resolve_48]
  have hn : a+2 ≠ 0 := by omega
  simp only [execute, ha, hn, ↓reduceIte, destination]
  apply Steps.cons
  rw [step_of_resolved resolve_49]
  have hread : write r 3 (a+2-1) 3 = a+1 := by simp [write]
  have hn' : a+1 ≠ 0 := by omega
  simp only [execute, hread, hn', ↓reduceIte, destination, Nat.add_sub_cancel, write_twice]
  exact Steps.refl _

def target (a : Nat) : Nat := if a = 0 then 3661 else if a = 1 then 3554 else 50
def cost (a : Nat) : Nat := if a = 0 then 1 else 2

/-- Exact three-way dispatch: S, MP, or AX with selector minus two. -/
theorem total (a : Nat) (r : Registers) (ha : r 3 = a) :
    Steps PA194SourceProgram.sites (cost a) ⟨.at 48,r⟩ ⟨.at (target a),write r 3 (a-2)⟩ := by
  cases a with
  | zero =>
    have hw : write r 3 0 = r := by rw [← ha]; exact write_same r 3
    simpa only [cost,target,↓reduceIte,Nat.zero_sub,hw] using zero r ha
  | succ a =>
    cases a with
    | zero => exact one r ha
    | succ a =>
      have ht : target (a+2) = 50 := by simp [target]
      have hc : cost (a+2) = 2 := by simp [cost]
      change Steps PA194SourceProgram.sites (cost (a+2)) ⟨.at 48,r⟩ ⟨.at (target (a+2)),write r 3 (a+2-2)⟩
      simpa only [ht,hc,Nat.add_sub_cancel] using many a r ha

#print axioms total
end PA194FetchSource.Dispatch

