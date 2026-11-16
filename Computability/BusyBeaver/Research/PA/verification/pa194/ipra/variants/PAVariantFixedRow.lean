import PAVariantModelStep
import PackedRootModel
set_option autoImplicit false
namespace PAVariantFixedRow
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRASelectCode
open TableDispatch TableModelSemantics ConfigurationStep BinaryTapeCodes
open PAVariantRowDispatch PAVariantModelStep PackedRootModel

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
noncomputable local instance : DecidableEq M := Classical.decEq M
local notation "F" => Structure.func (L := language) (M := M)
local notation "Z" => (F (Code.zero 0) Fin.elim0)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

noncomputable def rowStep (row : PAVariantRowDispatch.Action) (l r : M) : M × M × M :=
  let w := modelNumeral M row.1
  let d := modelNumeral M row.2.1
  let t := modelNumeral M row.2.2
  let add := fun a b : M => F addCode ![a,b]
  let parity := fun a : M => F parityCode (fun _ => a)
  let half := fun a : M => F halfCode (fun _ => a)
  if d = Z then (t,half l,add (parity l) (add (add w w) (add (add (half r) (half r)) (add (half r) (half r)))))
  else (t,add (add l l) w,half r)

theorem modelFixedRow (states halt : Nat) (rows : List PAVariantRowDispatch.Action) (q bit : Nat) (l r : M)
    (hq : modelNumeral M q < modelNumeral M states)
    (hb : F parityCode (fun _ => r) = modelNumeral M bit) :
    (F (nextQ states halt rows) ![modelNumeral M q,l,r],
     F (nextL states rows) ![modelNumeral M q,l,r],
     F (nextR states rows) ![modelNumeral M q,l,r]) =
      rowStep (rows.getD (2*q+bit) (0,0,halt)) l r := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  have ha : (modelNumeral M q)+(modelNumeral M q)+F parityCode (fun _ => r) =
      modelNumeral M (2*q+bit) := by
    rw [hb, ←PA194FiniteControls.modelNumeralAdd, ←PA194FiniteControls.modelNumeralAdd]
    congr 1
    omega
  have hw : lookupSem 0 (writes rows) (modelNumeral M (2*q+bit)) =
      modelNumeral M (rows.getD (2*q+bit) (0,0,halt)).1 := by
    rw [←modelLookupAll]
    exact modelWriteNumeral halt rows _
  have hd : lookupSem 0 (directions rows) (modelNumeral M (2*q+bit)) =
      modelNumeral M (rows.getD (2*q+bit) (0,0,halt)).2.1 := by
    rw [←modelLookupAll]
    exact modelDirectionNumeral halt rows _
  have ht : lookupSem halt (targets rows) (modelNumeral M (2*q+bit)) =
      modelNumeral M (rows.getD (2*q+bit) (0,0,halt)).2.2 := by
    rw [←modelLookupAll]
    exact modelTargetNumeral halt rows _
  have hactive : F ltBitCode ![modelNumeral M q,modelNumeral M states] ≠ Z := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hn := PAVariantModelStep.modelNext states halt rows (![modelNumeral M q,l,r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hn
  change _ = PAVariantModelStep.stepSem states halt rows (modelNumeral M q) l r at hn
  rw [hn]
  change _ = rowStep (rows.getD (2*q+bit) (0,0,halt)) l r
  simp only [PAVariantModelStep.stepSem, rowStep]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd, ha, hw, hd, ht, hactive, ite_false]

#print axioms modelFixedRow
end models
end PAVariantFixedRow
