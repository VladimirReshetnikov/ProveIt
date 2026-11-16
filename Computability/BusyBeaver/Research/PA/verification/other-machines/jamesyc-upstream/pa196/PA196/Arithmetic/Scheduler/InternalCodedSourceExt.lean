module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.InternalCodedSourceStep
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

/-- Nine logical register equality determines exactly the valid HFS store;
model indices below the fixed bound are explicitly reduced to numerals. -/
theorem registers_ext {xs ys : V} (hx : ValidStore xs) (hy : ValidStore ys)
    (h : registers xs=registers ys) : xs=ys := by
  apply nth_ext (hx.trans hy.symm)
  intro i hi
  have hx' : len xs=9 := hx
  have hi' : i<ORingStructure.numeral 9 := by
    simpa only [hx',numeral_eq_natCast,Nat.cast_ofNat] using hi
  obtain ⟨j,hj,he⟩ := iff_lt_numeral_exists_numeral.mp hi'
  have hj' : j<9 := hj
  have hh := congrFun h (⟨j,hj'⟩ : Fin 9)
  simpa only [registers,he,numeral_eq_natCast] using hh

lemma state_reconstruct {c : V} (h : ValidStore (store c)) :
    stateCode (control c) (store c)=c := by
  rcases nil_or_adjoin c with hz | ⟨a,rs,he⟩
  · subst c
    have hn : (0 : V)=9 := by simpa only [ValidStore,store,sndIdx,Arithmetic.zero_sub,pi₂_zero,len_nil] using h
    have hp : (0 : V)<9 := by exact_mod_cast (show 0<9 by decide)
    exact False.elim ((ne_of_lt hp) hn)
  · simp [he,stateCode,control,store]

theorem state_ext {a b : V} (ha : ValidStore (store a)) (hb : ValidStore (store b))
    (hc : control a=control b) (hr : registers (store a)=registers (store b)) : a=b := by
  rw [←state_reconstruct ha,←state_reconstruct hb,hc,registers_ext ha hb hr]
end Models
#print axioms registers_ext
#print axioms state_ext
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

