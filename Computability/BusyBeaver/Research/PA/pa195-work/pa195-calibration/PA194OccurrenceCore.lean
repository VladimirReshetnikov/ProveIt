import PA194PackedDescent
import DiophantineConsistency.PRABoundedFormula
import DiophantineConsistency.PRAHistoryFixpointSuccCode
import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-! Bounded one-step core of PA194's numeric variable occurrence relation.
This file constructs only the core and its candidate-PRA characteristic code;
the model-length fixpoint iterator and equality with the full decoder are
separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194OccurrenceCore
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRABoundedFormula
  PRABoundedCharacteristic PRACharacteristicBit

abbrev firstGraph := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.firstDef
abbrev secondGraph := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.secondDef
abbrev seedPairGraph := LO.FirstOrder.Arithmetic.pairDef

/-- `x` packs `(formula code, label)` by Foundation pairing; `ih` is a set
of previously established packed occurrences. PA194's own child fields are
instead decoded via quotient by four followed by Cantor unpairing. Implication
recurses to both fields; membership/equality expose both labels; universal
quantification exposes the second field and recurses into the first. Zero is
truth and contributes no occurrence. Recursive history indices are required
to be less than the current packed index. -/
def occurrenceCore : 𝚺₀.Semisentence 2 := .mkSigma
  “x ih. ∃ n <⁺ x, ∃ v <⁺ x, !pi₁Def n x ∧ !pi₂Def v x ∧ 0 < n ∧
    ∃ q <⁺ n, !divDef q n 4 ∧
    ∃ a <⁺ q, !firstGraph a q ∧
    ∃ b <⁺ q, !secondGraph b q ∧
    ∃ t < 4, !remDef t n 4 ∧
      ((t = 0 ∧ ((∃ y < x, !seedPairGraph y a v ∧ y ∈ ih) ∨
                  (∃ z < x, !seedPairGraph z b v ∧ z ∈ ih))) ∨
       ((t = 1 ∨ t = 3) ∧ (v = a ∨ v = b)) ∨
       (t = 2 ∧ (v = b ∨ (∃ y < x, !seedPairGraph y a v ∧ y ∈ ih))))”

/-- Semantic reading of the exact one-step core in an arbitrary IOpen model.
Membership in the history is the bounded bit graph, not an assumed full model
of set theory. -/
def coreMeaning {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x ih : V) : Prop :=
  let n := π₁ x
  let v := π₂ x
  let a := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (n / 4)
  let b := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (n / 4)
  0 < n ∧
    ((n % 4 = 0 ∧ ((pair a v < x ∧ bitDef.val.Evalb ![pair a v,ih]) ∨
                     (pair b v < x ∧ bitDef.val.Evalb ![pair b v,ih]))) ∨
     ((n % 4 = 1 ∨ n % 4 = 3) ∧ (v = a ∨ v = b)) ∨
     (n % 4 = 2 ∧ (v = b ∨ (pair a v < x ∧ bitDef.val.Evalb ![pair a v,ih]))))

theorem occurrenceCore_eval {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x ih : V) :
    occurrenceCore.val.Evalb ![x,ih] ↔ coreMeaning x ih := by
  have hpi1 (a b : V) : pi₁Def.val.Evalb ![a,b] ↔ a = π₁ b := pi₁_defined.defined ![a,b]
  have hpi2 (a b : V) : pi₂Def.val.Evalb ![a,b] ↔ a = π₂ b := pi₂_defined.defined ![a,b]
  have hdiv (a b : V) : divDef.val.Evalb ![a,b,4] ↔ a = b / 4 := div_defined.defined ![a,b,4]
  have hrem (a b : V) : remDef.val.Evalb ![a,b,4] ↔ a = b % 4 := rem_defined.defined ![a,b,4]
  have hfirst (a b : V) : firstGraph.val.Evalb ![a,b] ↔ a = SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first b :=
    SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first_defined.defined ![a,b]
  have hsecond (a b : V) : secondGraph.val.Evalb ![a,b] ↔ a = SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second b :=
    SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second_defined.defined ![a,b]
  have hpair (a b c : V) : seedPairGraph.val.Evalb ![a,b,c] ↔ a = pair b c := pair_defined.defined ![a,b,c]
  have hfirst_le := (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.projections_spec (π₁ x / 4)).1
  have hsecond_le := (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.projections_spec (π₁ x / 4)).2.1
  simp [occurrenceCore, coreMeaning, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, operator_mem_def,
    hpi1, hpi2, hdiv, hrem, hfirst, hsecond, hpair, hfirst_le, hsecond_le]

/-- The semantic core without explicit rank guards; packed-child descent makes
the guards redundant for every positive source formula code. -/
def coreRecMeaning {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x ih : V) : Prop :=
  let n := π₁ x
  let v := π₂ x
  let a := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (n / 4)
  let b := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (n / 4)
  0 < n ∧
    ((n % 4 = 0 ∧ (bitDef.val.Evalb ![pair a v,ih] ∨ bitDef.val.Evalb ![pair b v,ih])) ∨
     ((n % 4 = 1 ∨ n % 4 = 3) ∧ (v = a ∨ v = b)) ∨
     (n % 4 = 2 ∧ (v = b ∨ bitDef.val.Evalb ![pair a v,ih])))

theorem occurrenceCore_eval_rec {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x ih : V) :
    occurrenceCore.val.Evalb ![x,ih] ↔ coreRecMeaning x ih := by
  rw [occurrenceCore_eval]
  by_cases hn : 0 < π₁ x
  · have he : pair (π₁ x) (π₂ x) = x := pair_unpair x
    have hd := PA194PackedDescent.packed_children_lt (π₁ x) (π₂ x) hn
    rw [he] at hd
    simp [coreMeaning, coreRecMeaning, hn, hd.1, hd.2]
  · simp [coreMeaning, coreRecMeaning, hn]

noncomputable def mappedCore : Semisentence language 2 := Semiformula.lMap embedding occurrenceCore.val

theorem PRA_has_occurrenceCoreCode : ∃ c : Code 2, Primrec (eval c) ∧
    PRA ⊢ bitSentence c ∧ PRA ⊢ oneCorrectSentence c mappedCore := by
  apply PRA_proves_boundedBooleanCharacteristic mappedCore
  exact ParsonsHierarchyMap.hierarchy occurrenceCore.sigma_prop

/-- The exact bounded occurrence core as a Δ₁ fixpoint blueprint. -/
noncomputable def occurrenceBlueprint : Fixpoint.Blueprint 0 where
  core := occurrenceCore.ofZero 𝚫₁

theorem occurrenceSigmaCore_eq :
    PRAHistoryFixpointSuccCode.sigmaCore occurrenceBlueprint = mappedCore := by
  rfl

theorem occurrencePiCore_eq :
    PRAHistoryFixpointSuccCode.piCore occurrenceBlueprint = mappedCore := by
  rfl

/-- Candidate PRA supplies a primitive-recursive function code whose
represented graph performs one bounded-history update for the exact PA194
occurrence core. Iterating this update to obtain the recursive occurrence
predicate is a separate construction. -/
theorem PRA_has_occurrenceSuccCode : ∃ c : Code 2,
    PRA ⊢ PRAHistoryFixpointSuccCode.graphSentence occurrenceBlueprint c := by
  obtain ⟨good, _, hbit, hcorrect⟩ := PRA_has_occurrenceCoreCode
  apply PRAHistoryFixpointSuccCode.PRA_has_fixSuccCode occurrenceBlueprint good hbit
  · simpa only [occurrenceSigmaCore_eq] using hcorrect
  · simpa only [occurrencePiCore_eq] using hcorrect

#print axioms PRA_has_occurrenceSuccCode
#print axioms occurrenceCore_eval_rec
#print axioms occurrenceCore_eval
#print axioms PRA_has_occurrenceCoreCode
end PA194OccurrenceCore
