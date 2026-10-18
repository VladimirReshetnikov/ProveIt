import BusyBeaver.ZFC.ArithmeticControlConstructor254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254 ArithmeticControlStep254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlPair254 (twReg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlConstructor254 FiniteControlTable254 RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.impEntry_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.impExit_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.tagChain_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.constructor_middle_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.constructorFile_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.constructor_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlConstructor254.imp_constructor_run

example : (source impEntry).2 = .decnz 2 := impEntry_source
example : (source impExit).2 = .decnz 1 := impExit_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {n : Nat} {p q : Control} (h : TagChain n p q) (file : V) :
    controlRun (n : V) (liveValue (number p : V) file) =
      liveValue (number q : V) (put twReg (regValue file twReg + (n : V)) file) :=
  tagChain_run h file

example (p : Control) (file : V) :
    controlRun ((0 : Nat) : V) (liveValue (number p : V) file) =
      liveValue (number p : V) (put twReg (regValue file twReg + ((0 : Nat) : V)) file) :=
  tagChain_run (TagChain.nil p) file

example {p q : Control} (h : TagChain 1 p q) (file : V) :
    controlRun ((1 : Nat) : V) (liveValue (number p : V) file) =
      liveValue (number q : V) (put twReg (regValue file twReg + ((1 : Nat) : V)) file) :=
  tagChain_run h file

example {p q : Control} (h : TagChain 2 p q) (file : V) :
    controlRun ((2 : Nat) : V) (liveValue (number p : V) file) =
      liveValue (number q : V) (put twReg (regValue file twReg + ((2 : Nat) : V)) file) :=
  tagChain_run h file

example {p q : Control} (h : TagChain 3 p q) (file : V) :
    controlRun ((3 : Nat) : V) (liveValue (number p : V) file) =
      liveValue (number q : V) (put twReg (regValue file twReg + ((3 : Nat) : V)) file) :=
  tagChain_run h file

example (c : ConstructorShape) (file : V) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number c.pair.copy.test : V) file) =
      liveValue (number c.exit : V) (middleFile c.tag file) :=
  constructor_middle_run c file h2

example (c : ConstructorShape) (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number c.pop.readEntry : V) file) =
      liveValue (number c.exit : V) (constructorFile c.tag file) :=
  constructor_run c file h1 h2

example (tag : Fin 4) (file : V) (i : Fin 9) (ht : i ≠ twReg) (hs : i ≠ wsReg) :
    regValue (constructorFile tag file) i = regValue file i :=
  constructorFile_other tag file i ht hs

example (tag : Fin 4) (file : V) (h1 : regValue file s1Reg = 0) :
    regValue (constructorFile tag file) s1Reg = 0 :=
  (constructorFile_other tag file s1Reg (by decide) (by decide)).trans h1

example (file : V) (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number impEntry : V) file) =
      liveValue (number impExit : V)
        (put twReg (wim (first (regValue file wsReg)) (regValue file twReg))
          (put wsReg (second (regValue file wsReg)) file)) :=
  imp_constructor_run file h1 h2

example (file a rest : V) (hp : regValue file wsReg = cantor a rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number impEntry : V) file) =
      liveValue (number impExit : V)
        (put twReg (wim a (regValue file twReg)) (put wsReg rest file)) := by
  simpa only [hp, first_cantor, second_cantor] using imp_constructor_run file h1 h2
