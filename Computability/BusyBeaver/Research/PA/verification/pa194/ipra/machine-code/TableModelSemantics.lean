import TableDispatch

/-! A finite decision-list semantics for the table lookup in every candidate
PRA model, including nonstandard inputs. The meta-level finite list is fixed;
model predecessor and zero test provide the branch semantics. -/
set_option autoImplicit false
namespace TableModelSemantics
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion
open TableDispatch

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
noncomputable local instance : DecidableEq M := Classical.decEq M

/-- The list is external finite syntax; `x` may be any element of the model. -/
noncomputable def lookupSem (default : Nat) : List Nat → M → M
  | [], _ => modelNumeral M default
  | a :: as, x => if x = Structure.func (L := language) (Code.zero 0) Fin.elim0
    then modelNumeral M a
    else lookupSem default as (Structure.func (L := language) predCode (fun _ => x))

theorem modelLookupAll (default : Nat) (xs : List Nat) (x : M) :
    Structure.func (L := language) (lookupCode default xs) (fun _ => x) =
      lookupSem default xs x := by
  classical
  induction xs generalizing x with
  | nil => exact modelConstant default x
  | cons a as ih =>
    simp only [lookupSem]
    split
    · rename_i h
      subst x
      rw [modelLookupZero, modelConstant]
    · rename_i h
      have hx := (modelZeroOrSuccPred x).resolve_left h
      have ht : Structure.func (L := language) (lookupCode default (a :: as)) (fun _ => x) =
          Structure.func (L := language) (lookupCode default as)
            (fun _ => Structure.func (L := language) predCode (fun _ => x)) := by
        conv_lhs => rw [← hx]
        exact modelLookupSucc _ _ _ _
      rw [ht, ih]

/-- The three concrete row columns satisfy the finite decision-list semantics
at arbitrary model elements, not just at standard numerals. -/
theorem modelConcreteRows (x : M) :
    Structure.func (L := language) writeCode (fun _ => x) = lookupSem 0 writes x ∧
    Structure.func (L := language) directionCode (fun _ => x) = lookupSem 0 directions x ∧
    Structure.func (L := language) targetCode (fun _ => x) = lookupSem 194 targets x := by
  exact ⟨modelLookupAll 0 writes x, modelLookupAll 0 directions x,
    modelLookupAll 194 targets x⟩
end models
#print axioms modelLookupAll
#print axioms modelConcreteRows
end TableModelSemantics
