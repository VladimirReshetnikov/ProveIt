import PA194FiniteControls
set_option autoImplicit false
namespace PAVariantRowDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAModelIOpenPairing PRAHistoryPairCode BinaryTapeCodes TableDispatch

abbrev Action := Nat × Nat × Nat

def writes (rows : List Action) : List Nat := rows.map (fun r => r.1)
def directions (rows : List Action) : List Nat := rows.map (fun r => r.2.1)
def targets (rows : List Action) : List Nat := rows.map (fun r => r.2.2)
def writeCode (rows : List Action) : Code 1 := lookupCode 0 (writes rows)
def directionCode (rows : List Action) : Code 1 := lookupCode 0 (directions rows)
def targetCode (halt : Nat) (rows : List Action) : Code 1 := lookupCode halt (targets rows)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelWriteNumeral (halt : Nat) (rows : List Action) (i : Nat) :
    F (writeCode rows) (fun _ => modelNumeral M i) =
      modelNumeral M (rows.getD i (0,0,halt)).1 := by
  rw [writeCode, modelLookupNumeral]
  exact congrArg (modelNumeral M) (getDMap (fun r : Action => r.1) rows i (0,0,halt))

theorem modelDirectionNumeral (halt : Nat) (rows : List Action) (i : Nat) :
    F (directionCode rows) (fun _ => modelNumeral M i) =
      modelNumeral M (rows.getD i (0,0,halt)).2.1 := by
  rw [directionCode, modelLookupNumeral]
  exact congrArg (modelNumeral M) (getDMap (fun r : Action => r.2.1) rows i (0,0,halt))

theorem modelTargetNumeral (halt : Nat) (rows : List Action) (i : Nat) :
    F (targetCode halt rows) (fun _ => modelNumeral M i) =
      modelNumeral M (rows.getD i (0,0,halt)).2.2 := by
  rw [targetCode, modelLookupNumeral]
  exact congrArg (modelNumeral M) (getDMap (fun r : Action => r.2.2) rows i (0,0,halt))

/-- Generic fixed-table dispatch in every PRA model. The state bound and table
are arbitrary fixed Lean data; model-valued tape is unrestricted. -/
theorem modelWorkingRow (states halt : Nat) (rows : List Action) (q r : M)
    (hq : q < modelNumeral M states) :
    ∃ i : Fin states, ∃ b : Fin 2,
      q = modelNumeral M i.val ∧ F parityCode (fun _ => r) = modelNumeral M b.val ∧
      let address := q + q + F parityCode (fun _ => r)
      let row := rows.getD (2*i.val+b.val) (0,0,halt)
      F (writeCode rows) (fun _ => address) = modelNumeral M row.1 ∧
      F (directionCode rows) (fun _ => address) = modelNumeral M row.2.1 ∧
      F (targetCode halt rows) (fun _ => address) = modelNumeral M row.2.2 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  obtain ⟨i, hi⟩ := PA194FiniteControls.modelBelowNumeral states q hq
  obtain ⟨b, hb⟩ := PA194FiniteControls.modelParityNumeral r
  refine ⟨i,b,hi,hb,?_⟩
  dsimp only
  have ha : q+q+F parityCode (fun _ => r) = modelNumeral M (2*i.val+b.val) := by
    rw [hi,hb, ←PA194FiniteControls.modelNumeralAdd, ←PA194FiniteControls.modelNumeralAdd]
    congr 1
    omega
  rw [ha]
  exact ⟨modelWriteNumeral _ _ _, modelDirectionNumeral _ _ _, modelTargetNumeral _ _ _⟩

#print axioms modelWriteNumeral
#print axioms modelDirectionNumeral
#print axioms modelTargetNumeral
#print axioms modelWorkingRow
end models
end PAVariantRowDispatch
