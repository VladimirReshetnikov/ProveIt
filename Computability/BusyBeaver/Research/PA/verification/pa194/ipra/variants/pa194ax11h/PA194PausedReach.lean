import PA194ModelMPDrain

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace PA194PausedReach
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ClockInvariantDefinable PA194IteratedSimulation PA194ModelMPDrain

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Reaches (code : Code 1) (s t : M) : Prop := ∃ k : M, F (iterate code) ![k,s] = t

theorem append (code : Code 1) {s t u : M}
    (h : Reaches code s t) (h' : Reaches code t u) : Reaches code s u := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨d,hd⟩ := h'
  refine ⟨c+d,?_⟩
  rw [PA194ControllerRunAdd.iterateAdd, hc, hd]

theorem oneStep (code : Code 1) {s t : M} (h : F code ![s] = t) : Reaches code s t := by
  refine ⟨1,?_⟩
  rw [←zero_add (1 : M),iterateSucc,iterateZero,h]

private theorem pathDef (r c : M → M) (n : M)
    (hr : 𝚺₁-Function₁ r) (hc : 𝚺₁-Function₁ c) :
    𝚺₁-Predicate (fun j : M => n < j ∨ ∃ t : M, r t = c j) := by
  haveI := hr
  haveI := hc
  definability

/-- Model-length concatenation for any primitive-recursive transition code. -/
theorem runMany (code : Code 1) (frame : M → M) (n : M)
    (hframe : 𝚺₁-Function₁ frame)
    (hstep : ∀ j, j < n → Reaches code (frame j) (frame (j+1))) :
    ∀ j, j ≤ n → Reaches code (frame 0) (frame j) := by
  have hr : 𝚺₁-Function₁ (fun t => F (iterate code) ![t,frame 0]) :=
    bindBinary _ _ (binaryCodeDef (iterate code))
  have h : ∀ j, n < j ∨ Reaches code (frame 0) (frame j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction with
    | hP => exact pathDef _ _ n hr hframe
    | zero => exact Or.inr ⟨0,iterateZero code _⟩
    | succ j ih =>
      by_cases hbig : n < j+1
      · exact Or.inl hbig
      · right
        have hj : j < n := lt_of_lt_of_le (lt_add_one j) (not_lt.mp hbig)
        exact append code (ih.resolve_left (not_lt_of_ge (le_of_lt hj))) (hstep j hj)
  exact fun j hj => (h j).resolve_left (not_lt_of_ge hj)

#print axioms append
#print axioms oneStep
#print axioms runMany
end models
end PA194PausedReach
