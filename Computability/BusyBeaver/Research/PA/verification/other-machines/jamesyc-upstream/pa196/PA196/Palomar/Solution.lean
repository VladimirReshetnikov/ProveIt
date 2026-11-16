module
public import PATheoryBridge
public import NthBridge
public import PA196.Palomar.RowsBridge
public import PA196.Palomar.TraceBridge
public import PA196.Palomar.PhysicalBridge
public import PA196.Independence
@[expose] public section

/-! Exact syntax and tape bridges for the supplied 196-state machine.
The declarations below establish physical nonhalting, standard arithmetic
truth, and both unprovability directions for the explicitly presented PA.
The nonhalting direction uses the internal refutation-to-machine proof and
the second incompleteness theorem, with consistency supplied by the standard
natural-number model. -/
namespace PalomarPA.PA196
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

attribute [local irreducible] pa196Rows pa196Step nthFormula

theorem pa196Halting_toFoundation : pa196Halting.toFoundation =
    _root_.PA196.Arithmetic.Machine.Exact.PA.HaltingFormula.traceSentence := by
  rw [pa196Halting,traceFormula_exact nthFormula_toFoundation,pa196Step_exact]
  rfl

theorem pa196Nonhalting_toFoundation : pa196Nonhalting.toFoundation =
    _root_.PA196.Arithmetic.Machine.Exact.PA.HaltingFormula.nonhaltingSentence := by
  rw [pa196Nonhalting,Formula.to_neg,pa196Halting_toFoundation]
  rfl

/-- Standard truth for the independently stated PA196 arithmetic sentence. -/
theorem nonhalting_true : Nat ⊧/![] pa196Nonhalting.toFoundation := by
  rw [pa196Nonhalting_toFoundation]
  exact _root_.PA196.Arithmetic.nonhalting_true

/-- Ordinary, explicitly presented PA cannot prove that this machine halts. -/
theorem halting_unprovable : ¬ Provable PATheory pa196Halting := by
  intro h
  have hp := (pa_provable_iff pa196Halting).mp h
  rw [pa196Halting_toFoundation] at hp
  exact _root_.PA196.Arithmetic.halting_unprovable hp

/-- Ordinary, explicitly presented PA cannot prove this machine's nonhalting. -/
theorem nonhalting_unprovable : ¬ Provable PATheory pa196Nonhalting := by
  intro h
  have hp := (pa_provable_iff pa196Nonhalting).mp h
  rw [pa196Nonhalting_toFoundation] at hp
  exact _root_.PA196.Arithmetic.nonhalting_unprovable hp

/-- PA proves neither exact PA196 nonhalting nor exact PA196 halting. -/
theorem two_sided_independence :
    (¬ Provable PATheory pa196Nonhalting) ∧ (¬ Provable PATheory pa196Halting) :=
  ⟨nonhalting_unprovable,halting_unprovable⟩

/-- The independently stated nonhalting sentence is irrefutable in PA. -/
theorem nonhalting_irrefutable : ¬ Provable PATheory pa196Nonhalting.neg := by
  intro h
  have hp := (pa_provable_iff pa196Nonhalting.neg).mp h
  rw [Formula.to_neg,pa196Nonhalting_toFoundation] at hp
  exact _root_.PA196.Arithmetic.nonhalting_irrefutable hp

/-- The exact binary table runs forever from its independently stated blank tape. -/
theorem machine_nonhalting :
    ¬ ∃ n c, machineRun n blank=some c ∧ machineStep c=none := by
  rintro ⟨n,c,hr,hs⟩
  apply _root_.PA196.machine_nonhalting
  refine ⟨c.toZip,⟨n,?_⟩,?_⟩
  · have hb : blank.toZip=_root_.PA196.Startup.blank := rfl
    simpa only [hr,Option.map_some,hb] using (machineRun_eq n blank).symm
  · simpa only [hs,Option.map_none] using (machineStep_eq c).symm

#print axioms pa196Halting_toFoundation
#print axioms pa196Nonhalting_toFoundation
#print axioms nonhalting_true
#print axioms halting_unprovable
#print axioms nonhalting_unprovable
#print axioms two_sided_independence
#print axioms nonhalting_irrefutable
#print axioms machine_nonhalting
end PalomarPA.PA196
