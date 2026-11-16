import PA194SourceSentinel
import PA194ControllerRunAdd

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194SourceSchedulerOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls
open PA194SourceControllerCode PA194IteratedSimulation PA194ClockInvariantDefinable

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

private theorem runHalted (seed : M) (h : F pc ![seed] = modelNumeral M 3674) :
    ∀ c : M, F run ![c,seed] = seed := by
  haveI : 𝚺₁-Function₁ (fun c : M => F run ![c,seed]) :=
    bindBinary _ seed (binaryCodeDef run)
  have hd : 𝚺₁-Predicate (fun c : M => F run ![c,seed] = seed) := by definability
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => exact hd
  | zero => exact iterateZero step seed
  | succ c ih =>
    change F (iterate step) ![c+1,seed] = seed
    rw [iterateSucc]
    change F step ![F run ![c,seed]] = seed
    rw [ih]
    exact PA194SourceSentinel.stepHalted seed h

theorem haltPersists (seed a b : M) (hle : a ≤ b)
    (hh : F pc ![F run ![a,seed]] = modelNumeral M 3674) :
    F pc ![F run ![b,seed]] = modelNumeral M 3674 := by
  obtain ⟨c,rfl⟩ := exists_add_of_le hle
  change F pc ![F (iterate step) ![a+c,seed]] = _
  rw [PA194ControllerRunAdd.iterateAdd]
  change F pc ![F run ![c,F run ![a,seed]]] = _
  rw [runHalted _ hh]
  exact hh

private theorem alignedDef (p q : M → M)
    (hp : 𝚺₁-Function₁ p) (hq : 𝚺₁-Function₁ q) :
    𝚺₁-Predicate (fun n : M => ∃ t : M, n ≤ t ∧ p t = q n) := by
  haveI := hp
  haveI := hq
  definability

private theorem one_le_of_positive (c : M) (hc : 0 < c) : (1 : M) ≤ c := by
  rcases zero_or_succ c with (rfl | ⟨k,rfl⟩)
  · exact (_root_.lt_irrefl _ hc).elim
  · simpa only [zero_add] using
      (add_le_add (zero_le : (0 : M) ≤ k) (le_rfl : (1 : M) ≤ 1))

/-- Align the scheduler after each command with a controller root. A command
supplies its own positive model clock. The invariant does not require a code
computing that clock uniformly. -/
theorem synchronize (next frame : Code 1) (seed start : M)
    (hseed : start = F frame ![seed])
    (advance : ∀ n t : M, F run ![t,start] = F frame ![F (iterate next) ![n,seed]] →
      ∃ c : M, 0 < c ∧ F run ![c,F frame ![F (iterate next) ![n,seed]]] =
        F frame ![F next ![F (iterate next) ![n,seed]]]) :
    ∀ n : M, ∃ t : M, n ≤ t ∧
      F run ![t,start] = F frame ![F (iterate next) ![n,seed]] := by
  have hsource := bindBinary _ start (binaryCodeDef (M := M) run)
  have hsched := bindBinary _ seed (binaryCodeDef (M := M) (iterate next))
  have hframed := composeUnary _ _ (unaryCodeDef (M := M) frame) hsched
  intro n
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact alignedDef _ _ hsource hframed
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    change F (iterate step) ![0,start] = _
    rw [iterateZero,iterateZero]
    exact hseed
  | succ n ih =>
    obtain ⟨t,hle,ht⟩ := ih
    obtain ⟨c,hc,hstep⟩ := advance n t ht
    refine ⟨t+c,add_le_add hle (one_le_of_positive c hc),?_⟩
    change F (iterate step) ![t+c,start] = _
    rw [PA194ControllerRunAdd.iterateAdd,iterateSucc]
    change F run ![c,F run ![t,start]] = _
    rw [ht]
    exact hstep

/-- Reduce source-controller halting to the command contracts.

An ordinary command must reach the next scheduler frame. A command whose
scheduler flag is one must reach the source absorbing halt. A site-25 frame
has a smaller program counter than the absorbing halt, so no source halt
can occur within any segment completing an ordinary command. -/
theorem equivalent (next flag frame : Code 1) (seed start : M)
    (hseed : start = F frame ![seed])
    (hroot : ∀ s : M, F pc ![F frame ![s]] = modelNumeral M 25)
    (advance : ∀ s : M, F flag ![s] ≠ 1 →
      ∃ c : M, 0 < c ∧ F run ![c,F frame ![s]] = F frame ![F next ![s]])
    (terminate : ∀ s : M, F flag ![s] = 1 →
      ∃ c : M, F pc ![F run ![c,F frame ![s]]] = modelNumeral M 3674) :
    (∃ t : M, F pc ![F run ![t,start]] = modelNumeral M 3674) ↔
      (∃ n : M, F flag ![F (iterate next) ![n,seed]] = 1) := by
  classical
  constructor
  · rintro ⟨t,hh⟩
    by_contra h
    have sync := synchronize next frame seed start hseed (fun n _ _ =>
      advance _ (fun he => h ⟨n,he⟩))
    obtain ⟨u,htu,hu⟩ := sync t
    have hp := haltPersists start t u htu hh
    rw [hu,hroot] at hp
    exact (ne_of_lt (PA194StateOne.modelNumeralStrict 25 3674 (by decide))) hp
  · rintro ⟨n,hn⟩
    by_contra h
    have rejects (m t : M)
        (ht : F run ![t,start] = F frame ![F (iterate next) ![m,seed]]) :
        F flag ![F (iterate next) ![m,seed]] ≠ 1 := by
      intro he
      obtain ⟨c,hc⟩ := terminate _ he
      apply h
      refine ⟨t+c,?_⟩
      change F pc ![F (iterate step) ![t+c,start]] = _
      rw [PA194ControllerRunAdd.iterateAdd]
      change F pc ![F run ![c,F run ![t,start]]] = _
      rw [ht]
      exact hc
    have sync := synchronize next frame seed start hseed (fun m t ht =>
      advance _ (rejects m t ht))
    obtain ⟨t,_,ht⟩ := sync n
    exact rejects n t ht hn

#print axioms haltPersists
#print axioms synchronize
#print axioms equivalent
end models
end PA194SourceSchedulerOrbit
