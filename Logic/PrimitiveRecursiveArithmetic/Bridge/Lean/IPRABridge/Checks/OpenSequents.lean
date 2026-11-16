import IPRABridge.OpenSequents

/-! Exercise proof transport under compound assignments, induction with a
parameter under a binder, and existential elimination. -/

set_option autoImplicit false

namespace IPRABridge.Checks

open LO LO.FirstOrder LO.Entailment LeanProofs.ConciseIPRA
open DiophantineConsistency
open IPRAStandardTheory (standardTheory)
open IPRATheoryHilbertBridge (extended)

local notation "L" => PRALanguage.language

local instance nativeDecidableEq : PRALanguage.language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

private def xEqY : Fm PTm 2 := .eq (.var 0) (.var 1)

private def yEqX : Fm PTm 2 := .eq (.var 1) (.var 0)

private def compoundEnv (i : Fin 2) : Term L ℕ :=
  .func PRAFiniteFunctionCodes.Code.succ (fun _ => .fvar (i.val + 7))

private theorem twoHypotheses : Prf PRAAx [.imp xEqY yEqX, xEqY] yEqX :=
  .impE Prf.hyp0 Prf.hyp1

/-- Both hypotheses are used after substituting compound Foundation terms
for the Concise variables. -/
theorem twoHypothesesAtCompoundTerms :
    [toStandardInEnv compoundEnv (.imp xEqY yEqX), toStandardInEnv compoundEnv xEqY]
      ⊢[extended standardTheory] toStandardInEnv compoundEnv yEqX :=
  conciseToStandardSequent twoHypotheses compoundEnv

/-- Mapping the resulting sequent back specializes the entire context
and the conclusion by the same substitution. -/
theorem twoHypothesesMappedBack (free : ℕ → PTm 2) :
    let sub : Fin 2 → PTm 2 := fun i => PTm.succ (free (i.val + 7))
    Prf PRAAx [(.imp xEqY yEqX : Fm PTm 2).subst sub, xEqY.subst sub] (yEqX.subst sub) := by
  have mapTerm (i : Fin 2) :
      toConciseTerm Fin.elim0 free (Semiterm.lMap IPRAOrderErasure.termsToReference (compoundEnv i)) =
        PTm.succ (free (i.val + 7)) := by
    simp only [compoundEnv, Semiterm.lMap_func, IPRAOrderErasure.termsToReference,
      toConciseTerm, toConciseCode, PTm.succ, Function.comp_def]
    rfl
  simpa only [List.map_cons, List.map_nil, toConciseProposition_inEnv, mapTerm] using
    standardToConciseSequent twoHypothesesAtCompoundTerms free

private def successorEquality : Fm PTm 2 :=
  .eq (PTm.succ (.var 0)) (PTm.succ (.var 1))

/-- Apply the Concise successor-injectivity theorem under Foundation
assumptions and at compound terms. -/
theorem applyImportedSuccessorInjectivity :
    [toStandardInEnv compoundEnv yEqX, toStandardInEnv compoundEnv successorEquality]
      ⊢[extended standardTheory] toStandardInEnv compoundEnv xEqY := by
  have portable : Prf PRAAx [] (.imp successorEquality xEqY) := Prf.axm PRAAx.succInj
  have imported := conciseToStandardSequent portable compoundEnv
  have implication : extended standardTheory ⊢!
      toStandardInEnv compoundEnv successorEquality 🡒 toStandardInEnv compoundEnv xEqY :=
    FiniteContext.emptyPrf imported.some
  exact ⟨FiniteContext.of implication ⨀ FiniteContext.byAxm₁⟩

private def parameterInduction (body : Fm PTm 2) : Fm PTm 1 :=
  .imp (body.subst (Syn.inst PTm.zero))
    (.imp (.all (.imp body (body.subst (Syn.repl (PTm.succ (.var 0)))))) (.all body))

private def parameterLabel : Fin 1 ↪ ℕ :=
  ⟨fun i => i.val + 11, fun _ _ h => Fin.ext (Nat.add_right_cancel h)⟩

/-- The induction formula mentions a parameter that remains free under the
binder for the induction variable. -/
theorem inductionAtParameter :
    [] ⊢[extended standardTheory]
      toStandardInEnv (fun i => .fvar (parameterLabel i)) (parameterInduction xEqY) := by
  have inductionProof : Prf PRAAx [] (parameterInduction xEqY) := Prf.axm (.ind xEqY trivial)
  exact conciseToStandardSequent inductionProof _

theorem inductionMappedBack : Prf PRAAx [] (parameterInduction xEqY) :=
  (conciseSequent_iff parameterLabel [] _).2 inductionAtParameter

private def witnessConclusion : Fm PTm 1 := .eq (.var 0) PTm.zero

private def witnessHypotheses : List (Fm PTm 1) :=
  [.ex xEqY, .all (.imp xEqY witnessConclusion.shift)]

private theorem eliminateWitness : Prf PRAAx witnessHypotheses witnessConclusion := by
  have witness : Prf PRAAx witnessHypotheses (.ex xEqY) := Prf.hyp0
  have elimination : Prf PRAAx witnessHypotheses (.all (.imp xEqY witnessConclusion.shift)) :=
    Prf.hyp1
  exact .exE witness (.impE elimination.allOpen.wk Prf.hyp0)

/-- The existential witness is available in the shifted context while the
conclusion still depends only on the original parameter. -/
theorem existentialElimination :
    witnessHypotheses.map (toStandardInEnv (fun i => .fvar (parameterLabel i)))
      ⊢[extended standardTheory]
        toStandardInEnv (fun i => .fvar (parameterLabel i)) witnessConclusion :=
  (conciseSequent_iff parameterLabel _ _).1 eliminateWitness

theorem existentialEliminationMappedBack : Prf PRAAx witnessHypotheses witnessConclusion :=
  (conciseSequent_iff parameterLabel _ _).2 existentialElimination

#print axioms twoHypothesesMappedBack
#print axioms applyImportedSuccessorInjectivity
#print axioms inductionMappedBack
#print axioms existentialEliminationMappedBack

end IPRABridge.Checks
