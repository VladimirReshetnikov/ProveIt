import PA194AX11HFieldPaused
import PA194SchedulerIteration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HFieldAlignedDef
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SchedulerIteration PA194AX11HFieldPaused PA194FiniteControls
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def alignedPair (s : M) : Prop := aligned (pi₁ s) (pi₂ s)

private theorem alignedPair_generic (a b c : M) (f g h j : M → M)
    (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g)
    (hh : 𝚺₁-Function₁ h) (hj : 𝚺₁-Function₁ j) :
    𝚺₁-Predicate (fun s : M => ∃ k : M, k < a ∧
      f s = b + k ∧ g s = c + k ∧ h s = j s) := by
  haveI := hf
  haveI := hg
  haveI := hh
  haveI := hj
  definability

theorem alignedPair_def : 𝚺₁-Predicate (alignedPair (M := M)) := by
  have he (s : M) : F pc ![s] = pi₁ s := by
    rw [PA194SourceControllerCode.pc]
    convert PackedDecoderModel.modelDecodeLeft s using 1
    apply congrArg (fun e : Fin 1 → M => F PackedClock.decodeLeft e)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hf : 𝚺₁-Function₁ (fun s : M => F pc ![pi₁ s]) := by
    simp_rw [he]
    definability
  have hg : 𝚺₁-Function₁ (fun s : M => F pc ![pi₂ s]) := by
    simp_rw [he]
    definability
  have hh : 𝚺₁-Function₁ (fun s : M => pi₂ (pi₁ s)) := by definability
  have hj : 𝚺₁-Function₁ (fun s : M => pi₂ (pi₂ s)) := by definability
  exact alignedPair_generic (modelNumeral M 15) (modelNumeral M 3554)
    (modelNumeral M 3572) _ _ _ _ hf hg hh hj

#print axioms alignedPair_def
end models
end PA194AX11HFieldAlignedDef
