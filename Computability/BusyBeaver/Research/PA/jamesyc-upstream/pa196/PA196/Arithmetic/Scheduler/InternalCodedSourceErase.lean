module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDrainSpec
public import PA196.Source.NIPBinding
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def eraseFormula (entry exit : Nat) (r : Fin 9) : ArithmeticSemisentence 1 :=
  “n. ∀ xs, (!lenDef 9 xs ∧ !nthDef n xs ↑r.val) →
    ∃ ys a b cs, !(replaceGraph r.val) ys xs 0 ∧
      !adjoinDef a ↑(entry+1) xs ∧ !adjoinDef b ↑(exit+1) ys ∧
      !traceGraph (2*n+1) cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
theorem erase_formula (entry exit : Nat) (r : Fin 9) (n : V) :
    (eraseFormula entry exit r).Evalb ![n] ↔
      ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
        Trace (2*n+1) cs (stateCode ((entry+1:Nat):V) xs)
          (stateCode ((exit+1:Nat):V) (replace r.val xs 0)) := by
  simp [eraseFormula,(replace_defined r.val).df,trace_correct,ValidStore,registers,stateCode,
    numeral_eq_natCast,eq_comm,Matrix.comp_vecCons'']

theorem erase_loop (entry jumpPC exit : Nat) (r : Fin 9)
    (he : entry<3812) (hj : jumpPC<3812)
    (be : Source.resolveAt PA196.Program.sites entry=some (.dec r (some exit) (some jumpPC)))
    (bj : Source.resolveAt PA196.Program.sites jumpPC=some (.jump (some entry)))
    (n xs : V) (hv : ValidStore xs) (hr : registers xs r=n) :
    ∃ cs, Trace (2*n+1) cs (stateCode ((entry+1:Nat):V) xs)
      (stateCode ((exit+1:Nat):V) (replace r.val xs 0)) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ PA196.Arithmetic.Machine.PA.theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory)
  have all : ∀ n : V, ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
      Trace (2*n+1) cs (stateCode ((entry+1:Nat):V) xs)
        (stateCode ((exit+1:Nat):V) (replace r.val xs 0)) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V => ∀ xs : V, ValidStore xs → registers xs r=n → ∃ cs,
        Trace (2*n+1) cs (stateCode ((entry+1:Nat):V) xs)
          (stateCode ((exit+1:Nat):V) (replace r.val xs 0))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb (eraseFormula entry exit r),by trivial,?_⟩
      intro n; simpa using (erase_formula (V:=V) entry exit r n).symm
    · intro xs hv hr
      have hz : replace r.val xs 0=xs := by simpa only [hr] using replace_current r xs hv
      have hstep : stepValue (stateCode ((entry+1:Nat):V) xs)=stateCode ((exit+1:Nat):V) xs := by
        rw [literal_step entry he _ be]; simp [instructionValue,hr,destinationCode]
      refine ⟨?[stateCode ((entry+1:Nat):V) xs,stateCode ((exit+1:Nat):V) xs],?_⟩
      simpa only [mul_zero,zero_add,hz,hstep] using trace_one (stateCode ((entry+1:Nat):V) xs)
    · intro n ih xs hv hr
      let ys := replace r.val xs n
      have hy : ValidStore ys := replace_valid xs n hv r
      have hyr : registers ys r=n := registers_replace_same xs n hv r
      obtain ⟨cs,htrace⟩ := ih ys hy hyr
      have hend : replace r.val ys 0=replace r.val xs 0 := replace_same r.val xs n 0
      rw [hend] at htrace
      have hdec : stepValue (stateCode ((entry+1:Nat):V) xs)=stateCode ((jumpPC+1:Nat):V) ys := by
        rw [literal_step entry he _ be]; simp [instructionValue,hr,destinationCode,ys]
      have hjump : stepValue (stateCode ((jumpPC+1:Nat):V) ys)=stateCode ((entry+1:Nat):V) ys := by
        rw [literal_step jumpPC hj _ bj]; rfl
      obtain ⟨ds,hd⟩ := trace_prepend _ hjump htrace
      obtain ⟨es,hh⟩ := trace_prepend _ hdec hd
      refine ⟨es,?_⟩
      have htwo : (2:V)=1+1 := one_add_one_eq_two.symm
      simpa only [mul_add,mul_one,htwo,add_assoc] using hh
  exact all n xs hv hr

theorem actual_nip_clear_H (n xs : V) (hv : ValidStore xs) (hh : registers xs 5=n) :
    ∃ cs, Trace (2*n+1) cs (stateCode 6 xs) (stateCode 8 (replace 5 xs 0)) := by
  apply erase_loop 5 6 7 5 (by decide) (by decide)
  · exact PA196.Source.nip_resolved_at ⟨6,by decide⟩
  · exact PA196.Source.nip_resolved_at ⟨7,by decide⟩
  · exact hv
  · exact hh
#print axioms erase_loop
#print axioms actual_nip_clear_H
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

