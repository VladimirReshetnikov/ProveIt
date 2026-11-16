module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceGuardFinite
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma guard_tail_run (xs : V) (hv : ValidStore xs) :
    finiteRun 2 (stateCode 3930 (guardStore xs 0 0)) = stateCode 3934 (guardStore xs 0 0) := by
  simp only [finiteRun,guard_step_3929 xs 0 0 hv,ite_true,guard_step_3931 xs 0 0 hv]
theorem guard_many_trace (xs h : V) (hv : ValidStore xs) :
    ∃ cs,Trace ((7:V)+(2*h+1)+2) cs (stateCode 3922 (guardStore xs ((h+1)+1) 0))
      (stateCode 3934 (guardStore xs 0 0)) := by
  obtain ⟨cs,hc⟩ := finiteRun_trace 7 (stateCode 3922 (guardStore xs ((h+1)+1) 0))
  rw [guard_many_run xs h hv] at hc
  obtain ⟨ds,hd⟩ := actual_nip_clear_H h (guardStore xs h 0) (guardStore_valid xs h 0 hv) (guard_read_H xs h 0 hv)
  rw [guard_write_H] at hd
  obtain ⟨es,he⟩ := trace_compose hc hd
  obtain ⟨fs,hf⟩ := finiteRun_trace 2 (stateCode 3930 (guardStore xs 0 0))
  rw [guard_tail_run xs hv] at hf
  simpa only [Nat.cast_ofNat] using trace_compose he hf

/-- The literal twelve-leaf guard halts exactly at H=1, and otherwise exits
with H=X=0. All values, including its clear-loop counter, range over the PA model. -/
theorem actual_nip_guard (xs h : V) (hv : ValidStore xs) :
    ∃ n cs,0<n ∧ Trace n cs (stateCode 3922 (guardStore xs h 0))
      (stateCode (if h=1 then 0 else 3934) (guardStore xs 0 0)) := by
  rcases zero_or_succ h with rfl | ⟨k,rfl⟩
  · obtain ⟨cs,hc⟩ := finiteRun_trace 6 (stateCode 3922 (guardStore xs 0 0))
    rw [guard_zero_run xs hv] at hc
    refine ⟨6,cs,by exact_mod_cast (show (0:Nat)<6 by decide),?_⟩
    simpa using hc
  · rcases zero_or_succ k with rfl | ⟨h,rfl⟩
    · obtain ⟨cs,hc⟩ := finiteRun_trace 7 (stateCode 3922 (guardStore xs 1 0))
      rw [guard_one_run xs hv] at hc
      refine ⟨7,cs,by exact_mod_cast (show (0:Nat)<7 by decide),?_⟩
      simpa using hc
    · obtain ⟨cs,hc⟩ := guard_many_trace xs h hv
      refine ⟨7+(2*h+1)+2,cs,by simp,?_⟩
      have hn : (h+1)+1≠1 := by simp
      simpa only [hn,ite_false] using hc
#print axioms guard_many_trace
#print axioms actual_nip_guard
end M6.Arithmetic.PA.InternalTrace.CodedSource

