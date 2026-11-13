module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceGuardSteps
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
lemma guard_zero_run (xs : V) (hv : ValidStore xs) :
    finiteRun 7 (stateCode 3811 (guardStore xs 0 0)) = stateCode 12 (guardStore xs 0 0) := by
  simp only [finiteRun,guard_extra_jump,guard_step_3921 xs 0 0 hv,zero_add,
    guard_step_3922 xs 0 1 hv,ite_true,guard_step_3926 xs 0 1 hv,
    Arithmetic.one_ne_zero,ite_false,Arithmetic.sub_self,guard_step_3927 xs 0 0 hv,
    guard_step_3929 xs 0 0 hv,guard_step_3931 xs 0 0 hv]
lemma guard_one_run (xs : V) (hv : ValidStore xs) :
    finiteRun 8 (stateCode 3811 (guardStore xs 1 0)) = stateCode 0 (guardStore xs 0 0) := by
  simp only [finiteRun,guard_extra_jump,guard_step_3921 xs 1 0 hv,zero_add,
    guard_step_3922 xs 1 1 hv,Arithmetic.one_ne_zero,ite_false,Arithmetic.sub_self,
    guard_step_3923 xs 0 1 hv,guard_step_3924 xs 0 0 hv,
    guard_step_3922 xs 0 0 hv,ite_true,guard_step_3926 xs 0 0 hv,
    guard_step_3932 xs 0 0 hv]
lemma guard_many_run (xs h : V) (hv : ValidStore xs) :
    finiteRun 8 (stateCode 3811 (guardStore xs ((h+1)+1) 0)) = stateCode 6 (guardStore xs h 0) := by
  have h1 : h+1≠0 := by simp
  have h2 : (h+1)+1≠0 := by simp
  simp only [finiteRun,guard_extra_jump,guard_step_3921 xs ((h+1)+1) 0 hv,zero_add,
    guard_step_3922 xs ((h+1)+1) 1 hv,h2,ite_false,add_sub_self,
    guard_step_3923 xs (h+1) 1 hv,Arithmetic.one_ne_zero,Arithmetic.sub_self,
    guard_step_3924 xs (h+1) 0 hv,guard_step_3922 xs (h+1) 0 hv,h1,
    guard_step_3923 xs h 0 hv,ite_true,guard_step_3925 xs h 0 hv]
#print axioms guard_zero_run
#print axioms guard_one_run
#print axioms guard_many_run
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

