module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermLanguage
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
namespace FreeBound

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = 0”
  fvar := .mkSigma “y x. y = x + 1”
  func := .mkSigma “y k f v v'. !listMaxDef y v'”
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ _) := 0
  fvar (_ x) := x + 1
  func (_ _ _ _ v') := listMax v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [listMax_defined.df]
end FreeBound
open FreeBound
noncomputable def freeBound (t : V) : V := construction.result L ![] t
noncomputable def freeBoundVec (k v : V) : V := construction.resultVec L ![] k v
noncomputable def freeBoundGraph : 𝚺ᴬ₁.Semisentence 2 := blueprint.result L
noncomputable def freeBoundVecGraph : 𝚺ᴬ₁.Semisentence 3 := blueprint.resultVec L
@[simp] theorem freeBound_bvar (z : V) : freeBound (qqBvar z)=0 := by simp [freeBound,construction]
@[simp] theorem freeBound_fvar (x : V) : freeBound (qqFvar x)=x+1 := by simp [freeBound,construction]
@[simp] theorem freeBound_func {k f v : V} (hf : Presentation.language.IsFunc k f) (hv : IsUTermVec L k v) :
    freeBound (qqFunc k f v)=listMax (freeBoundVec k v) := by simp [freeBound,construction,hf,hv]; rfl
@[simp] theorem freeBoundVec_length {k v : V} (hv : IsUTermVec L k v) : len (freeBoundVec k v)=k :=
  construction.resultVec_lh L _ hv
@[simp] theorem freeBoundVec_nth {k v i : V} (hv : IsUTermVec L k v) (hi : i<k) :
    nth (freeBoundVec k v) i=freeBound (nth v i) := construction.nth_resultVec L _ hv hi
@[simp] theorem freeBoundVec_nil : freeBoundVec (0:V) 0=0 := construction.resultVec_nil L _
instance freeBound_defined : 𝚺ᴬ₁-Function₁ (freeBound : V→V) via freeBoundGraph := construction.result_defined
instance freeBoundVec_defined : 𝚺ᴬ₁-Function₂ (freeBoundVec : V→V→V) via freeBoundVecGraph := construction.resultVec_defined

def FreeSupported (l t : V) : Prop := IsUTerm L t ∧ freeBound t≤l
noncomputable def freeSupportedGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “l t. !((isUTerm L).sigma) t ∧ ∃ b, !freeBoundGraph b t ∧ b≤l”
theorem freeSupported_graph (l t : V) : freeSupportedGraph.val.Evalb ![l,t] ↔ FreeSupported l t := by
  simp [freeSupportedGraph,FreeSupported,freeBound_defined.df,Matrix.comp_vecCons'']
@[simp] theorem freeSupported_bvar (l i : V) : FreeSupported l (qqBvar i) := by simp [FreeSupported]
@[simp] theorem freeSupported_fvar (l i : V) : FreeSupported l (qqFvar i) ↔ i<l := by
  simp [FreeSupported,succ_le_iff_lt]
theorem freeSupported_func {l k f ts : V} (hf : Presentation.language.IsFunc k f) (hv : IsUTermVec L k ts) :
    FreeSupported l (qqFunc k f ts) ↔ ∀ i<k, FreeSupported l (nth ts i) := by
  simp only [FreeSupported,IsUTerm.func_iff,hf,hv,true_and,freeBound_func hf hv]
  constructor
  · intro h i hi
    exact ⟨hv.nth hi,by simpa only [freeBoundVec_nth hv hi] using listMaxss_le_iff.mp h i (by simpa [hv] using hi)⟩
  · intro h
    apply listMaxss_le_iff.mpr
    intro i hi
    have hi' : i<k := by simpa [hv] using hi
    simpa only [freeBoundVec_nth hv hi'] using (h i hi').2
#print axioms freeBound_defined
#print axioms freeSupported_graph
#print axioms freeSupported_func
end M6.PA.NumericPAeqTerm

