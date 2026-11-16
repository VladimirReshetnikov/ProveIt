import PA194AX11HFieldAlignedDef
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HFieldIteration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194PathIterator
open PA194SourceControllerCode PA194SchedulerIteration PA194AX11HFieldPaused PA194AX11HFieldAlignedDef PA194StackCode

def pairedStep : Code 1 := bin pairCode (unary oldPaused (fst (.proj 0))) (unary newPaused (snd (.proj 0)))
def pairedRun : Code 2 := dropCode pairedStep

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

theorem pairedStep_model (s : M) :
    F pairedStep ![s] = pair (F oldPaused ![pi₁ s]) (F newPaused ![pi₂ s]) := by
  simp only [pairedStep,modelBin,modelPairCode,modelUnary,fst_model,snd_model,modelProjection,Matrix.cons_val_zero]
  have hv (x : M) : (fun _ : Fin 1 => x) = ![x] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv, hv]

theorem pairedStep_preserves (s : M) (h : alignedPair s) : alignedPair (F pairedStep ![s]) := by
  rw [pairedStep_model]
  simpa [alignedPair] using aligned_step (pi₁ s) (pi₂ s) h

theorem pairedRun_base (s : M) : F pairedRun ![0,s] = s := modelDropBase pairedStep s

theorem pairedRun_succ (k s : M) : F pairedRun ![k+1,s] = F pairedStep ![F pairedRun ![k,s]] := by
  rw [pairedRun,modelDropStep]
  have hv : (fun _ : Fin 1 => F (dropCode pairedStep) ![k,s]) = ![F (dropCode pairedStep) ![k,s]] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

theorem pairedRun_def (s : M) : 𝚺₁-Function₁ (fun n : M => F pairedRun ![n,s]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F pairedRun e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) pairedRun)
  have hf : 𝚺₁-Function₂ (fun n s : M => F pairedRun ![n,s]) := by
    convert h using 1
    funext e
    exact congrArg (fun e : Fin 2 → M => F pairedRun e) (Matrix.fun_eq_vec_two e).symm
  exact unary_from_binary _ s hf

/-- Synchronization for all model-valued lengths, including nonstandard lengths. -/
theorem pairedRun_preserves (s k : M) (hs : alignedPair s) : alignedPair (F pairedRun ![k,s]) := by
  haveI := alignedPair_def (M := M)
  haveI := pairedRun_def s
  have hp : 𝚺₁-Predicate (fun k : M => alignedPair (F pairedRun ![k,s])) := by definability
  induction k using ISigma1.sigma1_succ_induction with
  | hP => exact hp
  | zero => rw [pairedRun_base]; exact hs
  | succ k ih => rw [pairedRun_succ]; exact pairedStep_preserves _ ih

#print axioms pairedStep_model
#print axioms pairedRun_preserves
end models
end PA194AX11HFieldIteration
