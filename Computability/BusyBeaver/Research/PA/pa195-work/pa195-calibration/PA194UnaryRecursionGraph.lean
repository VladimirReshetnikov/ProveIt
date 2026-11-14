import DiophantineConsistency.PRAHistoryResultGraph

/-! A nonstandard-model graph bridge for parameter-free unary primitive recursion.

The base and step hypotheses below are semantic graph certificates in the
arithmetic reduct of the model, not merely correctness on standard naturals.
The parameterized recursion needed for PA194 term closing is not covered here.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194UnaryRecursionGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryIterator
  PRAHistoryTrace PRAHistoryResultGraph

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The explicit candidate-PRA history yields the arithmetic computation graph,
for every model element, without induction on an external natural number. -/
theorem modelResultFromSemanticGraphs (B : PR.Blueprint 0) (base : Code 0) (step : Code 2)
    (hzero : B.zero.val.Evalb ![F base Fin.elim0])
    (hstep : ∀ i z : M, B.succ.val.Evalb ![F step ![i,z],z,i]) (n : M) :
    B.resultDef.val.Evalb ![F (valueCode base step) (fun _ => n),n] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have hh := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at hh
    exact hh
  obtain ⟨cons,hcons⟩ := PRAHistorySeqConsCode.PRA_has_seqConsCode
  let h := F (historyCode cons base step) (fun _ => n)
  have ht := modelTraceHistory cons base step hcons n
  have hc := modelCseqFromTrace B base step n h ht hzero hstep
  obtain ⟨_,_,hm⟩ := (trace_eval _ n h).mp ht
  have hmem := hm n (by simp)
  simp [PR.Blueprint.resultDef, Semiformula.Operator.val, memRelOpr]
  exact ⟨h,hc,hmem⟩

/-- In an IΣ₁ arithmetic reduct, any such candidate-PRA unary recursion agrees
on all model elements with Foundation's arithmetically defined recursion. -/
theorem modelResult_eq [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (B : PR.Blueprint 0) (c : PR.Construction M B) (base : Code 0) (step : Code 2)
    (hzero : B.zero.val.Evalb ![F base Fin.elim0])
    (hstep : ∀ i z : M, B.succ.val.Evalb ![F step ![i,z],z,i]) (n : M) :
    F (valueCode base step) (fun _ => n) = c.result Fin.elim0 n := by
  have h := modelResultFromSemanticGraphs B base step hzero hstep n
  have hs := (c.result_defined_iff ![F (valueCode base step) (fun _ => n),n]).mp h
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
    hs.trans (congrArg (fun p => c.result p n) (Subsingleton.elim _ _))

/-- The graph is definable in the arithmetic reduct, uniformly through B.resultDef. -/
theorem modelResult_defined [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (B : PR.Blueprint 0) (c : PR.Construction M B) (base : Code 0) (step : Code 2)
    (hzero : B.zero.val.Evalb ![F base Fin.elim0])
    (hstep : ∀ i z : M, B.succ.val.Evalb ![F step ![i,z],z,i]) :
    𝚺₁-Function₁ (fun n => F (valueCode base step) (fun _ => n)) via B.resultDef := by
  apply HierarchySymbol.Defined.mk
  intro v
  have h := c.result_defined_iff v
  change B.resultDef.val.Evalb v ↔ v 0 = F (valueCode base step) (fun _ => v 1)
  rw [modelResult_eq B c base step hzero hstep]
  have he : (fun i : Fin 0 => v i.succ.succ) = Fin.elim0 := Subsingleton.elim _ _
  simpa only [he] using h


/-- If the base and step graphs are arithmetically definable on the whole
model, then so is the candidate-PRA recursion. The step's graph is ordered
as `(previous, index)` to match Foundation's recursion blueprint. -/
theorem modelResult_definable_of_defined [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (base : Code 0) (step : Code 2) (φ : 𝚺₁.Semisentence 1) (ψ : 𝚺₁.Semisentence 3)
    (hbase : 𝚺₁.DefinedFunction (fun _ : Fin 0 → M => F base Fin.elim0) φ)
    (hstep : 𝚺₁.DefinedFunction (fun v : Fin 2 → M => F step ![v 1,v 0]) ψ) :
    𝚺₁-Function₁ (fun n : M => F (valueCode base step) (fun _ => n)) := by
  let B : PR.Blueprint 0 := ⟨φ,ψ⟩
  let c : PR.Construction M B := {
    zero := fun _ => F base Fin.elim0
    succ := fun _ i z => F step ![i,z]
    zero_defined := hbase
    succ_defined := hstep
  }
  have hz : B.zero.val.Evalb ![F base Fin.elim0] := by
    apply hbase.iff.mpr
    rfl
  have hs (i z : M) : B.succ.val.Evalb ![F step ![i,z],z,i] := by
    apply hstep.iff.mpr
    rfl
  exact HierarchySymbol.Defined.to_definable B.resultDef (modelResult_defined B c base step hz hs)

#print axioms modelResult_definable_of_defined

#print axioms modelResultFromSemanticGraphs
#print axioms modelResult_eq
#print axioms modelResult_defined
end models
end PA194UnaryRecursionGraph
