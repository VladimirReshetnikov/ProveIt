import PA194InductionSupplier
import PA194UniformOrdinalFullSource
import PA194SourceInhabited
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The induction supplier for the actual source theory

For every model of the candidate PRA presentation whose arithmetic reduct satisfies `IΣ₁`:

* `ordinalInductionCode_eq`: the ordinal induction statement of `pa194-model-axioms` is
  `indCode`;
* `indCode_provable`: the adjunctive theory with full separation proves `indCode q` for every
  internal property `q` (from `fullSourceOrdinalProof`);
* `induction_supplier_fullSource`: the hypothesis `hind` of `refutation_of_remaining`, from
  the term facts and the twelve source facts for that theory.
-/
noncomputable section
namespace PA194OrdinalInductionLink
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open PA194GuardedCompiler
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance linkZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance linkOne : One M := ⟨F oneCode Fin.elim0⟩
local instance linkAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance linkMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance linkLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance linkIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local instance] adjunctiveFullSepTheoryDelta

theorem ordinalInductionCode_eq (q : M) :
    PA194OrdinalFixed.ordinalInductionCode q = indCode q := by
  rw [indCode_quotes]
  rfl

theorem indCode_provable (q : M) (hq : IsSemiformula SourceL 1 q) :
    Provable adjunctiveFullSepTheory (indCode q) := by
  have h := PA194UniformOrdinalFullSource.fullSourceOrdinalProof (M := M) q hq
  have h' : Provable adjunctiveFullSepTheory (PA194OrdinalFixed.ordinalInductionCode q) :=
    (TProvable.iff_provable (T := PA194FullSepWitnessBranch.fullSourceInternal (M := M))
      (σ := (⟨PA194OrdinalFixed.ordinalInductionCode q,
        PA194OrdinalFixed.ordinalInductionCode_scoped q hq⟩ : Formula M SourceL))).mp ⟨h⟩
  rw [← ordinalInductionCode_eq]
  exact h'

/-- The induction supplier of the guarded interpretation for the actual source theory. -/
theorem induction_supplier_fullSource
    (facts : TermFacts (V := M) adjunctiveFullSepTheory)
    (S : SourceFacts (V := M) adjunctiveFullSepTheory) (p : M)
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    Provable adjunctiveFullSepTheory
      (translateFormula (rootParameters (PA194PAeqBind.closedInduction p))
        (PA194PAeqBind.closedInduction p)) :=
  induction_supplier facts S indCode_provable (PA194SourceInhabited.inhabited_provable (M := M)) p hp

#print axioms ordinalInductionCode_eq
#print axioms indCode_provable
#print axioms induction_supplier_fullSource
end models
end PA194OrdinalInductionLink
