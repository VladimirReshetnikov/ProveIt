module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceUnpairDecode
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
noncomputable def unpairIterationFormula (r x y : Fin 9) (base : Nat) : ArithmeticSemisentence 1 :=
  “n. ∀ xs k m, !lenDef 9 xs → ∃ ys zs a b t cs,
    !(unpairDecodedStoreGraph r x y) ys xs (n+m) k ∧
    !(unpairDecodedStoreGraph r x y) zs xs m (k+n) ∧
    !adjoinDef a ↑(base+1) ys ∧ !adjoinDef b ↑(base+1) zs ∧ !traceGraph t cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma unpair_iteration_formula (r x y : Fin 9) (base : Nat) (n : V) :
    (unpairIterationFormula r x y base).Evalb ![n] ↔
    ∀ xs k m : V,ValidStore xs → ∃ t cs,
      Trace t cs (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs (n+m) k))
        (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs m (k+n))) := by
  simp [unpairIterationFormula,unpairDecodedStore_graph,adjoin_defined.df,trace_correct,
    ValidStore,stateCode,len_defined.df,numeral_eq_natCast,Nat.cast_ofNat,eq_comm]

theorem unpair_iteration (r x y : Fin 9) (base : Nat) (hrx : r≠x) (hry : r≠y) (hxy : x≠y)
    (hbound : base+7<3947) (hb : UnpairLoopBound r x y base)
    (n xs k m : V) (hv : ValidStore xs) :
    ∃ t cs,Trace t cs (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs (n+m) k))
      (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs m (k+n))) := by
  letI : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have all : ∀ n : V,∀ xs k m : V,ValidStore xs → ∃ t cs,
      Trace t cs (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs (n+m) k))
        (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs m (k+n))) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun n : V=>∀ xs k m : V,ValidStore xs → ∃ t cs,
        Trace t cs (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs (n+m) k))
          (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs m (k+n)))) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb (unpairIterationFormula r x y base),by trivial,?_⟩
      intro n
      simpa using (unpair_iteration_formula (V:=V) r x y base n).symm
    · intro xs k m hv
      refine ⟨0,?[stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs m k)],?_⟩
      simpa only [zero_add,add_zero] using trace_zero (stateCode ((base+1:Nat):V) (unpairDecodedStore r x y xs m k))
    · intro n ih xs k m hv
      obtain ⟨t,cs,hc⟩ := unpair_round_decode r x y base hrx hry hxy hbound hb xs (n+m) k hv
      obtain ⟨u,ds,hd⟩ := ih xs (k+1) m hv
      obtain ⟨es,he⟩ := trace_compose hc hd
      refine ⟨t+u,es,?_⟩
      simpa only [add_assoc,add_comm,add_left_comm] using he
  exact all n xs k m hv
#print axioms unpair_iteration_formula
#print axioms unpair_iteration
end M6.Arithmetic.PA.InternalTrace.CodedSource

