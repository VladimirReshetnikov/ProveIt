import PA194ContextAndProjectionCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextIffApplicationCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextAndProjectionCode PA194ContextModusPonensCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Apply the forward implication in a contextual equivalence. -/
noncomputable def contextIffForwardCode (p q g hi hp : M) : M :=
  let f := neg SourceL p ^⋎ q
  let b := neg SourceL q ^⋎ p
  let left := contextAndLeftCode f b g hi
  contextMPCode p q g left hp

noncomputable def contextIffForwardGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g hi hp. ∃ np, !(negGraph SourceL) np p ∧ ∃ nq, !(negGraph SourceL) nq q ∧
    ∃ f, !qqOrDef f np q ∧ ∃ b, !qqOrDef b nq p ∧ ∃ left, !contextAndLeftGraph left f b g hi ∧
    !contextMPGraph out p q g left hp”

theorem contextIffForwardGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextIffForwardCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextIffForwardGraph := by
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [contextIffForwardGraph,contextIffForwardCode]

noncomputable def contextIffForwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (hi : T ⊢!ᵈᵉʳ insert ((p 🡒 q) ⋏ (q 🡒 p)) Γ)
    (hp : T ⊢!ᵈᵉʳ insert p Γ) : T ⊢!ᵈᵉʳ insert q Γ :=
  contextMPProof T Γ p q (contextAndLeftProof T Γ (p 🡒 q) (q 🡒 p) hi) hp

@[simp] theorem contextIffForwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (hi : T ⊢!ᵈᵉʳ insert ((p 🡒 q) ⋏ (q 🡒 p)) Γ)
    (hp : T ⊢!ᵈᵉʳ insert p Γ) :
    (contextIffForwardProof T Γ p q hi hp).val = contextIffForwardCode p.val q.val Γ.val hi.val hp.val := by
  simp [contextIffForwardProof,contextIffForwardCode,Semiformula.imp_def]

/-- Apply the reverse implication in a contextual equivalence. -/
noncomputable def contextIffBackwardCode (p q g hi hq : M) : M :=
  let f := neg SourceL p ^⋎ q
  let b := neg SourceL q ^⋎ p
  let right := contextAndRightCode f b g hi
  contextMPCode q p g right hq

noncomputable def contextIffBackwardGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g hi hq. ∃ np, !(negGraph SourceL) np p ∧ ∃ nq, !(negGraph SourceL) nq q ∧
    ∃ f, !qqOrDef f np q ∧ ∃ b, !qqOrDef b nq p ∧ ∃ right, !contextAndRightGraph right f b g hi ∧
    !contextMPGraph out q p g right hq”

theorem contextIffBackwardGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextIffBackwardCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextIffBackwardGraph := by
  haveI := contextAndRightGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [contextIffBackwardGraph,contextIffBackwardCode]

noncomputable def contextIffBackwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (hi : T ⊢!ᵈᵉʳ insert ((p 🡒 q) ⋏ (q 🡒 p)) Γ)
    (hq : T ⊢!ᵈᵉʳ insert q Γ) : T ⊢!ᵈᵉʳ insert p Γ :=
  contextMPProof T Γ q p (contextAndRightProof T Γ (p 🡒 q) (q 🡒 p) hi) hq

@[simp] theorem contextIffBackwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (hi : T ⊢!ᵈᵉʳ insert ((p 🡒 q) ⋏ (q 🡒 p)) Γ)
    (hq : T ⊢!ᵈᵉʳ insert q Γ) :
    (contextIffBackwardProof T Γ p q hi hq).val = contextIffBackwardCode p.val q.val Γ.val hi.val hq.val := by
  simp [contextIffBackwardProof,contextIffBackwardCode,Semiformula.imp_def]

#print axioms contextIffForwardGraph_defined
#print axioms contextIffForwardProof
#print axioms contextIffForwardProof_val
#print axioms contextIffBackwardGraph_defined
#print axioms contextIffBackwardProof
#print axioms contextIffBackwardProof_val
end models
end PA194ContextIffApplicationCode
