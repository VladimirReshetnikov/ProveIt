import PA194ClosedAtomic
import PA194ClosedMembershipInternal

/-! Internal typed meaning of a closed equality atom for arbitrary model labels. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ClosedAtomicInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAHerbrandSelection PA194CloseEquality PA194ClosedAtomic
  PA194ClosedMembership PA194ClosedMembershipInternal PA194ClosedTemplateInternal
  PA194ChildCodes PA194TagDecoder

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : DecidableEq M := Classical.decEq M

noncomputable def closedVar (label value : M) (depth : Nat) : Bootstrapping.Semiterm M ℒₒᵣ (depth+1) :=
  if label = value then Bootstrapping.Semiterm.bvar (Fin.last depth) else Bootstrapping.Semiterm.fvar value

/-- For arbitrary model-valued labels, equality and its negation are the
exact typed formulas whose numeric pair the PR code produces at depth zero. -/
theorem modelCloseEqComplement (label a b : M) (depth : Nat) :
    let terms : Bootstrapping.SemitermVec M ℒₒᵣ 2 (depth+1) := ![closedVar label a depth,closedVar label b depth]
    let φ : Bootstrapping.Semiformula M ℒₒᵣ (depth+1) := Bootstrapping.Semiformula.rel Language.ORing.Rel.eq terms
    F closeEqDual ![label,a,b,(depth : M)] = pair φ.val (∼φ).val := by
  dsimp only
  have h := modelCloseEqDual (M := M) label a b (depth : M)
  simp only at h
  rw [h]
  simp [Bootstrapping.Semiformula.rel_val, Bootstrapping.Semiformula.nrel_val,
    Bootstrapping.Semiformula.neg_rel, Bootstrapping.SemitermVec.val,
    closedVar, Bootstrapping.Semiterm.fvar, Bootstrapping.Semiterm.bvar, qqFvar, qqBvar,
    matrixToVec, adjoin_def]
  simp only [qqRel,qqNRel]
  split_ifs <;> simp
  all_goals
    change (0 : M) = ((Encodable.encode Language.ORing.Rel.eq : Nat) : M)
    rw [PA194EqAtomCode.equalitySymbolCode]
    simp


/-- For arbitrary model-valued source fields, the equality branch of the
actual atomic dispatcher yields a typed formula and its negation. -/
theorem modelAtomicEqualityInternal (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    let terms : Bootstrapping.SemitermVec M ℒₒᵣ 2 1 := ![closedVar label a 0,closedVar label b 0]
    let φ : Bootstrapping.Semiformula M ℒₒᵣ 1 := Bootstrapping.Semiformula.rel Language.ORing.Rel.eq terms
    F (closedAtomicDual tagCode firstChild secondChild) ![label,4 * cantor a b + 3] = pair φ.val (∼φ).val := by
  dsimp only
  rw [modelAtomicEquality tagCode firstChild secondChild ht hf hs]
  have h := modelCloseEqComplement (M := M) label a b 0
  simpa only [Nat.cast_zero] using h

/-- The membership branch likewise yields a typed formula and its negation
after substitution into the model-valued closing environment. -/
theorem modelAtomicMembershipInternal (tagCode firstChild secondChild : Code 1)
    (ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tagCode)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (label a b : M) :
    let φ := Bootstrapping.Semiformula.subst (closedSubstEnv label b a 0)
      (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)
    F (closedAtomicDual tagCode firstChild secondChild) ![label,4 * cantor a b + 1] = pair φ.val (∼φ).val := by
  dsimp only
  rw [modelAtomicMembership tagCode firstChild secondChild ht hf hs,
    modelBitCloseInternal, modelNegativeBitCloseInternal,
    quoteNegBit, Bootstrapping.Semiformula.substs_neg]

#print axioms modelAtomicEqualityInternal
#print axioms modelAtomicMembershipInternal
#print axioms modelCloseEqComplement
end models
end PA194ClosedAtomicInternal
