import PA194BranchSeed
import DiophantineConsistency.PRAExhaustion

/-! Pair-plus-one stack lookup as a potential course-of-values store. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194StackCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion
  PRAModelIOpenPairing PRAHerbrandSelection PA194BranchSeed

/-- For nonzero `pair(head,tail)+1`, decode the requested component. -/
def stackComponent (projection : Code 1) : Code 1 :=
  .comp projection (.cons predCode (.nil 1))
/-- Primitive recursion on the model index, dropping one stack cell each step. -/
def dropStep (tail : Code 1) : Code 3 := .comp tail (.cons (.proj 1) (.nil 3))
def dropCode (tail : Code 1) : Code 2 := .prec (.proj 0) (dropStep tail)
def lookupCode (head tail : Code 1) : Code 2 :=
  .comp head (.cons (dropCode tail) (.nil 2))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelStackHead (proj : Code 1)
    (hproj : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) proj)
    (x tail : M) :
    Structure.func (L := language) (stackComponent proj) (fun _ => pair x tail + 1) = x := by
  rw [stackComponent,modelComposition]
  have hv : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons predCode (.nil 1)) i) (fun _ => pair x tail + 1)) =
      (fun _ : Fin 1 => pair x tail) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) predCode (fun _ => pair x tail + 1) = _
    change Structure.func (L := language) predCode
      (fun _ => Structure.func (L := language) addCode ![pair x tail,Structure.func (L := language) oneCode Fin.elim0]) = _
    rw [modelAddOne,modelPredSucc]
  rw [hv,modelPi1Code proj hproj,pi₁_pair]

theorem modelStackTail (proj : Code 1)
    (hproj : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) proj)
    (x tail : M) :
    Structure.func (L := language) (stackComponent proj) (fun _ => pair x tail + 1) = tail := by
  rw [stackComponent,modelComposition]
  have hv : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons predCode (.nil 1)) i) (fun _ => pair x tail + 1)) =
      (fun _ : Fin 1 => pair x tail) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) predCode (fun _ => pair x tail + 1) = _
    change Structure.func (L := language) predCode
      (fun _ => Structure.func (L := language) addCode ![pair x tail,Structure.func (L := language) oneCode Fin.elim0]) = _
    rw [modelAddOne,modelPredSucc]
  rw [hv,modelPi2Code proj hproj,pi₂_pair]

theorem modelDropBase (tail : Code 1) (v : M) :
    Structure.func (L := language) (dropCode tail) ![0,v] = v := by
  have h := modelBase (M := M) (.proj 0) (dropStep tail) ![v]
  change Structure.func (L := language) (dropCode tail) ![0,v] =
    Structure.func (L := language) (.proj 0) ![v] at h
  rw [modelProjection] at h
  exact h

theorem modelDropStep (tail : Code 1) (i v : M) :
    Structure.func (L := language) (dropCode tail) ![i+1,v] =
      Structure.func (L := language) tail
        (fun _ => Structure.func (L := language) (dropCode tail) ![i,v]) := by
  have h := modelStep (M := M) (.proj 0) (dropStep tail) ![i,v]
  have h' : Structure.func (L := language) (dropCode tail)
      ![Structure.func (L := language) Code.succ (fun _ => i),v] =
      Structure.func (L := language) (dropStep tail)
        ![i,Structure.func (L := language) (dropCode tail) ![i,v],v] := h
  change Structure.func (L := language) (dropCode tail)
    ![Structure.func (L := language) addCode ![i,Structure.func (L := language) oneCode Fin.elim0],v] = _
  rw [modelAddOne,h']
  rw [dropStep,modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => Fin.elim0 k) j
  exact modelProjection 1 _

/-- One more represented drop removes the head of any decoded stack cell. -/
theorem modelDropPop (projTail : Code 1)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) projTail)
    (i v x rest : M)
    (h : Structure.func (L := language) (dropCode (stackComponent projTail)) ![i,v] = pair x rest + 1) :
    Structure.func (L := language) (dropCode (stackComponent projTail)) ![i+1,v] = rest := by
  rw [modelDropStep,h,modelStackTail projTail htail]

theorem modelLookupValue (head tail : Code 1) (i v : M) :
    Structure.func (L := language) (lookupCode head tail) ![i,v] =
      Structure.func (L := language) head (fun _ =>
        Structure.func (L := language) (dropCode tail) ![i,v]) := by
  rw [lookupCode,modelComposition]
  congr 1
  funext j
  exact Fin.cases rfl (fun k => Fin.elim0 k) j

theorem modelLookupZero (projHead projTail : Code 1)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) projHead)
    (x tail : M) :
    Structure.func (L := language) (lookupCode (stackComponent projHead) (stackComponent projTail))
      ![0,pair x tail + 1] = x := by
  rw [modelLookupValue,modelDropBase,modelStackHead projHead hhead]

#print axioms modelDropPop
#print axioms modelLookupValue
#print axioms modelLookupZero
#print axioms modelStackHead
#print axioms modelStackTail
#print axioms modelDropBase
#print axioms modelDropStep
end models

theorem PRA_has_stackProjections : ∃ f g : Code 1,
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) f) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) g) := by
  obtain ⟨f,_,hf⟩ := PRA_has_pi1Code
  obtain ⟨g,_,hg⟩ := PRA_has_pi2Code
  exact ⟨f,g,hf,hg⟩
#print axioms PRA_has_stackProjections
end PA194StackCode
