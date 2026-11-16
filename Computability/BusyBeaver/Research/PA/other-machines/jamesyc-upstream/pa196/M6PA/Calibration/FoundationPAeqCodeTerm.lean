module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermBlueprint
@[expose] public section

/-! A genuine IΣ₁-total numeric term translation obtained from the unchanged
parameter TermRec. Invalid original source term codes return zero by that
recursor's policy; this is not acceptance of malformed syntax. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def termCode (t : V) : V := termConstruction.result ℒₒᵣ ![] t
noncomputable def termVector (k ts : V) : V := termConstruction.resultVec ℒₒᵣ ![] k ts
noncomputable def termCodeGraph : 𝚺ᴬ₁.Semisentence 2 := termBlueprint.result ℒₒᵣ
noncomputable def termVectorGraph : 𝚺ᴬ₁.Semisentence 3 := termBlueprint.resultVec ℒₒᵣ
instance termCode_defined : 𝚺ᴬ₁-Function₁ (termCode : V→V) via termCodeGraph :=
  .mk fun v => by simpa [termCodeGraph,termCode] using! termConstruction.result_defined.defined v
instance termCode_definable : 𝚺ᴬ₁-Function₁ (termCode : V→V) := termCode_defined.to_definable
instance termVector_defined : 𝚺ᴬ₁-Function₂ (termVector : V→V→V) via termVectorGraph :=
  .mk fun v => by simpa [termVectorGraph,termVector] using! termConstruction.resultVec_defined.defined v
instance termVector_definable : 𝚺ᴬ₁-Function₂ (termVector : V→V→V) := termVector_defined.to_definable

theorem termCode_graph (out t : V) : termCodeGraph.val.Evalb ![out,t] ↔ out=termCode t :=
  termCode_defined.defined ![out,t]
theorem termVector_graph (out k ts : V) :
    termVectorGraph.val.Evalb ![out,k,ts] ↔ out=termVector k ts := termVector_defined.defined ![out,k,ts]
theorem termCode_total_unique (t : V) : ∃! out,termCodeGraph.val.Evalb ![out,t] := by
  refine ⟨termCode t,(termCode_graph _ _).mpr rfl,?_⟩
  intro out h; exact (termCode_graph _ _).mp h
theorem termCode_invalid (t : V) (ht : ¬IsUTerm ℒₒᵣ t) : termCode t=0 :=
  termConstruction.result_prop_not ℒₒᵣ ![] ht

@[simp] theorem termCode_bvar (i : V) : termCode (qqBvar i)=qqBvar i := by
  simp [termCode,termConstruction]
@[simp] theorem termCode_fvar (i : V) : termCode (qqFvar i)=qqFvar i := by
  simp [termCode,termConstruction]
theorem termCode_func {k f ts : V} (hf : (ℒₒᵣ).IsFunc k f) (ht : IsUTermVec ℒₒᵣ k ts) :
    termCode (qqFunc k f ts)=functionCode k f (termVector k ts) := by
  simp [termCode,termConstruction,hf,ht]; rfl
@[simp] theorem termVector_length {k ts : V} (ht : IsUTermVec ℒₒᵣ k ts) :
    len (termVector k ts)=k := termConstruction.resultVec_lh ℒₒᵣ ![] ht
@[simp] theorem termVector_nth {k ts i : V} (ht : IsUTermVec ℒₒᵣ k ts) (hi : i<k) :
    nth (termVector k ts) i=termCode (nth ts i) := termConstruction.nth_resultVec ℒₒᵣ ![] ht hi
@[simp] theorem termVector_nil : termVector (0:V) 0=0 := termConstruction.resultVec_nil ℒₒᵣ ![]
theorem termVector_cons {k t ts : V} (ht : IsUTerm ℒₒᵣ t) (hs : IsUTermVec ℒₒᵣ k ts) :
    termVector (k+1) (t∷ts)=termCode t∷termVector k ts :=
  termConstruction.resultVec_cons ℒₒᵣ ![] hs ht
@[simp] theorem termVector_two {s t : V} (hs : IsUTerm ℒₒᵣ s) (ht : IsUTerm ℒₒᵣ t) :
    termVector (2:V) (s∷(t∷0))=termCode s∷(termCode t∷0) := by
  rw [show (2:V)=0+1+1 by simp [one_add_one_eq_two],termVector_cons] <;> simp [hs,ht]
  simpa using termVector_cons (k:=0) (ts:=0) ht (by simp)

theorem original_functions (k f : V) : (ℒₒᵣ).IsFunc k f ↔
    (k=0 ∧ f=0) ∨ (k=0 ∧ f=1) ∨ (k=2 ∧ f=0) ∨ (k=2 ∧ f=1) := by
  change (V ⊧/![k,f] “k f. (k=0 ∧ f=0) ∨ (k=0 ∧ f=1) ∨ (k=2 ∧ f=0) ∨ (k=2 ∧ f=1)”) ↔ _
  simp

@[simp] theorem termCode_zero : termCode (qqFunc (0:V) 0 0)=zeroCode := by
  rw [termCode_func (by simp [original_functions]) (by simp)]
  simp [functionCode]
@[simp] theorem termCode_one : termCode (qqFunc (0:V) 1 0)=oneCode := by
  rw [termCode_func (by simp [original_functions]) (by simp)]
  simp [functionCode]
@[simp] theorem termCode_add {s t : V} (hs : IsUTerm ℒₒᵣ s) (ht : IsUTerm ℒₒᵣ t) :
    termCode (qqFunc (2:V) 0 (s∷(t∷0)))=qqFunc (2:V) 2 (termCode s∷(termCode t∷0)) := by
  rw [termCode_func (by simp [original_functions]) (by simp [hs,ht])]
  simp [functionCode,hs,ht]
@[simp] theorem termCode_mul {s t : V} (hs : IsUTerm ℒₒᵣ s) (ht : IsUTerm ℒₒᵣ t) :
    termCode (qqFunc (2:V) 1 (s∷(t∷0)))=qqFunc (2:V) 3 (termCode s∷(termCode t∷0)) := by
  rw [termCode_func (by simp [original_functions]) (by simp [hs,ht])]
  simp [functionCode,hs,ht]

#print axioms termCode_defined
#print axioms termVector_defined
#print axioms termCode_total_unique
#print axioms termCode_invalid
#print axioms termCode_bvar
#print axioms termCode_fvar
#print axioms termCode_func
#print axioms termVector_two
#print axioms termCode_zero
#print axioms termCode_one
#print axioms termCode_add
#print axioms termCode_mul
#print axioms termCode_graph
#print axioms termVector_graph
#print axioms termVector_length
#print axioms termVector_nth
#print axioms termVector_nil
#print axioms termVector_cons
#print axioms original_functions
end M6.PA.FoundationPAeqCode

