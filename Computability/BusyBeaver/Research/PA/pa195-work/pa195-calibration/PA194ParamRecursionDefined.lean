import PA194ParamRecursionGraph
import PA194ParamTrace

/-! From candidate-PRA histories to arithmetic graphs for primitive recursion.
The graph construction assumes arithmetic base and step definitions valid on
all elements of the model; the history-existence hypothesis is discharged.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ParamRecursionDefined
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194ParamIterator PA194ParamTrace PA194ParamRecursionGraph
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The candidate history supplies a Foundation sequence at every internal
stage, for every internal parameter tuple. -/
theorem modelTraceExists [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {k : ℕ} (base : Code k) (step : Code (k+2)) (v : Fin k → M) (n : M) :
    ∃ s, Seq s ∧ lh s = n+1 ∧
      ∀ i < n+1, pair i (F (.prec base step) (Fin.cases i v)) ∈ s := by
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  let s := F (historyCode cons base step) (Fin.cases n v)
  have ht := modelTraceHistory cons base step hcons n v
  obtain ⟨hseq,hlh,hmem⟩ := (trace_eval (.prec base step) n s v).mp ht
  refine ⟨s,?_,?_,?_⟩
  · exact seq_defined.iff.mp hseq
  · exact (lh_defined.iff.mp hlh).symm
  · intro i hi
    exact memRel_defined.iff.mp (hmem i hi)

/-- General parameterized recursion has the Blueprint's arithmetic graph once
its base and step agree with the Blueprint throughout the model. -/
theorem model_defined [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {k : ℕ} (B : PR.Blueprint k) (c : PR.Construction M B)
    (base : Code k) (step : Code (k+2))
    (hz : ∀ v, c.zero v = F base v)
    (hs : ∀ v i z, c.succ v i z = F step (Fin.cases i (Fin.cases z v))) :
    𝚺₁.DefinedFunction (fun e : Fin (k+1) → M => F (.prec base step) e) B.resultDef :=
  model_defined_of_traces B c base step hz hs (modelTraceExists base step)

#print axioms modelTraceExists
#print axioms model_defined
end models
end PA194ParamRecursionDefined
