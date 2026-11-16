module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceGuardSteps
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma guard_zero_run (xs : V) (hv : ValidStore xs) :
    finiteRun 6 (stateCode 3922 (guardStore xs 0 0)) = stateCode 3934 (guardStore xs 0 0) := by
  simp only [finiteRun,guard_step_3921 xs 0 0 hv,zero_add,
    guard_step_3922 xs 0 1 hv,ite_true,guard_step_3926 xs 0 1 hv,
    Arithmetic.one_ne_zero,ite_false,Arithmetic.sub_self,guard_step_3927 xs 0 0 hv,
    guard_step_3929 xs 0 0 hv,guard_step_3931 xs 0 0 hv]
lemma guard_one_run (xs : V) (hv : ValidStore xs) :
    finiteRun 7 (stateCode 3922 (guardStore xs 1 0)) = stateCode 0 (guardStore xs 0 0) := by
  simp only [finiteRun,guard_step_3921 xs 1 0 hv,zero_add,
    guard_step_3922 xs 1 1 hv,Arithmetic.one_ne_zero,ite_false,Arithmetic.sub_self,
    guard_step_3923 xs 0 1 hv,guard_step_3924 xs 0 0 hv,
    guard_step_3922 xs 0 0 hv,ite_true,guard_step_3926 xs 0 0 hv,
    guard_step_3932 xs 0 0 hv]
lemma guard_many_run (xs h : V) (hv : ValidStore xs) :
    finiteRun 7 (stateCode 3922 (guardStore xs ((h+1)+1) 0)) = stateCode 3928 (guardStore xs h 0) := by
  have h1 : h+1≠0 := by simp
  have h2 : (h+1)+1≠0 := by simp
  simp only [finiteRun,guard_step_3921 xs ((h+1)+1) 0 hv,zero_add,
    guard_step_3922 xs ((h+1)+1) 1 hv,h2,ite_false,add_sub_self,
    guard_step_3923 xs (h+1) 1 hv,Arithmetic.one_ne_zero,Arithmetic.sub_self,
    guard_step_3924 xs (h+1) 0 hv,guard_step_3922 xs (h+1) 0 hv,h1,
    guard_step_3923 xs h 0 hv,ite_true,guard_step_3925 xs h 0 hv]
#print axioms guard_zero_run
#print axioms guard_one_run
#print axioms guard_many_run
end M6.Arithmetic.PA.InternalTrace.CodedSource

