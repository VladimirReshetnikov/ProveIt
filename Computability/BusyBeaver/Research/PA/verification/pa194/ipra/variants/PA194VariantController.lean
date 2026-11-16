import ConPAMachineSourceSimulation
import PA194ControllerHaltReach

/-! Interface from a literal implementation of the primary resolved source
controller to its model-length halting predicate. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194VariantController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ClockInvariantDefinable PA194SourceControllerCode PA194IteratedSimulation

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/- The four root inputs are the source state, header gap, additional spare
   count, and first spare value. The last stays fixed along the source orbit. -/
private def Aligned (root : Code 4) (bound spare : M) (s c : M) : Prop :=
  F pc ![s] < bound ∧ ∃ gap count : M, c = F root ![s,gap,count,spare]

omit [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem alignmentDef (p : M → M) (r : M → M → M → M → M) (bound spare : M)
    (hp : 𝚺₁-Function₁ p) (hr : 𝚺₁-Function₄ r) :
    𝚺₁-Relation (fun s c => p s < bound ∧ ∃ gap count, c = r s gap count spare) := by
  letI := hp
  letI := hr
  definability

private theorem alignedDef (root : Code 4) (bound spare : M) :
    𝚺₁-Relation (Aligned (M := M) root bound spare) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 4 → M => F root e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) root)
  have hr : 𝚺₁-Function₄ (fun s gap count spare : M => F root ![s,gap,count,spare]) := by
    convert h using 1
    funext e
    apply congrArg (fun args : Fin 4 → M => F root args)
    funext i
    fin_cases i <;> rfl
  exact alignmentDef (fun s => F pc ![s]) (fun s gap count v => F root ![s,gap,count,v])
    bound spare (unaryCodeDef pc) hr

/-- The source implementation proof reduces to initialization, source
instruction returns, and the literal run from the terminal source site. -/
theorem halt_iff_site (T : ConPA.Machine.Table) (halt : Nat) (root : Code 4) (next : Code 1)
    (terminal bound seed startup spare initialGap initialCount : M)
    (hseed : F pc ![seed] < bound)
    (initial : ConPA.Machine.run T startup = F root ![seed,initialGap,initialCount,spare])
    (live : ∀ s gap count : M, F pc ![s] < bound →
      π₁ (F root ![s,gap,count,spare]) ≠ (halt : M))
    (absorb : ∀ c : M, π₁ c = (halt : M) → ConPA.Machine.step T c = c)
    (advance : ∀ s gap count : M, F pc ![s] < bound →
      F pc ![s] ≠ terminal → ∃ k nextGap nextCount : M, 0 < k ∧
        F pc ![F next ![s]] < bound ∧
        ConPA.Machine.runFrom T k (F root ![s,gap,count,spare]) =
          F root ![F next ![s],nextGap,nextCount,spare])
    (finish : ∀ s gap count : M, F pc ![s] = terminal →
      ∃ k : M, π₁ (ConPA.Machine.runFrom T k (F root ![s,gap,count,spare])) = (halt : M)) :
    (∃ t : M, π₁ (ConPA.Machine.run T t) = (halt : M)) ↔
      ∃ n : M, F pc ![F (iterate next) ![n,seed]] = terminal := by
  let source : M → M := fun n => F (iterate next) ![n,seed]
  have hs : 𝚺₁-Function₁ source := bindBinary _ seed (binaryCodeDef (iterate next))
  have hbase : Aligned root bound spare (source 0) (ConPA.Machine.run T startup) := by
    have hz : source 0 = seed := iterateZero next seed
    rw [hz]
    exact ⟨hseed, initialGap, initialCount, initial⟩
  refine (ConPA.Machine.halt_iff_source T halt source hs
    (fun s => F pc ![s] = terminal) (Aligned root bound spare) (alignedDef root bound spare)
    startup hbase ?_ absorb ?_ ?_)
  · rintro s c ⟨hpc, gap, count, rfl⟩
    exact live s gap count hpc
  · rintro n c ⟨hpc, gap, count, rfl⟩ hn
    obtain ⟨k, nextGap, nextCount, hk, hp, hrun⟩ := advance (source n) gap count hpc hn
    have he : source (n + 1) = F next ![source n] := iterateSucc next n seed
    rw [he]
    exact ⟨k, hk, hp, nextGap, nextCount, hrun⟩
  · rintro s c ⟨_, gap, count, rfl⟩ ht
    exact finish s gap count ht

/-- The source implementation proof reduces to initialization, source
instruction returns, and the literal halt at source site 10. -/
theorem halt_iff_controller (T : ConPA.Machine.Table) (halt : Nat) (root : Code 4)
    (seed startup spare initialGap initialCount : M)
    (hseed : F pc ![seed] < modelNumeral M 3673)
    (initial : ConPA.Machine.run T startup = F root ![seed,initialGap,initialCount,spare])
    (live : ∀ s gap count : M, F pc ![s] < modelNumeral M 3673 →
      π₁ (F root ![s,gap,count,spare]) ≠ (halt : M))
    (absorb : ∀ c : M, π₁ c = (halt : M) → ConPA.Machine.step T c = c)
    (advance : ∀ s gap count : M, F pc ![s] < modelNumeral M 3673 →
      F pc ![s] ≠ modelNumeral M 10 → ∃ k nextGap nextCount : M, 0 < k ∧
        F pc ![F step ![s]] < modelNumeral M 3673 ∧
        ConPA.Machine.runFrom T k (F root ![s,gap,count,spare]) =
          F root ![F step ![s],nextGap,nextCount,spare])
    (finish : ∀ s gap count : M, F pc ![s] = modelNumeral M 10 →
      ∃ k : M, π₁ (ConPA.Machine.runFrom T k (F root ![s,gap,count,spare])) = (halt : M)) :
    (∃ t : M, π₁ (ConPA.Machine.run T t) = (halt : M)) ↔
      ∃ n : M, F pc ![F run ![n,seed]] = modelNumeral M 3674 :=
  (halt_iff_site T halt root step (modelNumeral M 10) (modelNumeral M 3673)
    seed startup spare initialGap initialCount hseed initial live absorb advance finish).trans
      (PA194ControllerHaltReach.reachesHaltIffSite10 seed hseed).symm

#print axioms halt_iff_site
#print axioms halt_iff_controller
end models
end PA194VariantController
