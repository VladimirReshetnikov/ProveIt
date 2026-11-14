import PA194SourceShiftHistory
import DiophantineConsistency.PRABoundedSearchUniversal
import DiophantineConsistency.PRABoundedSearchBound
/-! Model-uniform bounded search using the fixed source-formula shift code.

The lookup is the pair-plus-one stack operation. Its identification with the
Foundation sequent representation is a separate obligation; `find_match` uses
an explicit validity assumption for each searched entry. This theorem is not a
machine calibration or a PA refutation compiler. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194SearchModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAEqualityCode PRAIsZero PRANonzeroCharacter PRABooleanOps PRAOpenFormulaCompiler
 PRABoundedSearchCode PRABoundedSearchInvariant PRABoundedSearchUniversal PRABoundedSearchBound
 PA194StackCode PA194StackHistory PA194TermShiftCodeModel PA194SourceShiftHistory PA194TermRecursion

noncomputable def lookup : Code 2 := lookupCode (stackComponent firstProjection) (stackComponent secondProjection)
noncomputable def current : Code 3 := bin lookup (.proj 0) (.proj 1)
noncomputable def shifted : Code 3 := .comp fixedFormulaShiftCode (.cons current (.nil 3))
noncomputable def mismatch : Code 3 := notCode (bin equalityCode shifted (.proj 2))
noncomputable def search : Code 3 := searchCode mismatch

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

 theorem mismatch_model (i v target : M)
    (hi : IsUFormula M6.PA.RelationalSource.language (F lookup ![i,v])) :
    F mismatch ![i,v,target] = 0 ↔ shift M6.PA.RelationalSource.language (F lookup ![i,v]) = target := by
  rw [mismatch, modelNotCode, modelBin, modelProjection]
  have he : F shifted ![i,v,target] = shift M6.PA.RelationalSource.language (F lookup ![i,v]) := by
    rw [shifted, modelComposition]
    have hv : (fun j : Fin 1 => F (getCode (.cons current (.nil 3)) j) ![i,v,target]) = ![F lookup ![i,v]] := by
      funext j
      refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp [getCode, current, modelBin, modelProjection]
    rw [hv]
    exact fixedFormulaShiftCode_correct hi
  change F isZeroCode (fun _ => F equalityCode ![F shifted ![i,v,target],target]) = 0 ↔ _
  rw [he]
  have h := modelEqualityCode (shift M6.PA.RelationalSource.language (F lookup ![i,v])) target
  rcases h.1 with hz | ho
  · rw [hz, modelIsZeroZero]
    constructor
    · intro hfalse
      exact False.elim (modelOneNeZero hfalse)
    · intro heq
      exact False.elim (modelOneNeZero ((h.2.mpr heq).symm.trans hz))
  · rw [ho, modelOneSuccZero, modelIsZeroSucc]
    exact ⟨fun _ => h.2.mp ho, fun _ => rfl⟩

 theorem find_match (bound v target j : M)
    (hj : j < bound)
    (hvalid : ∀ i, i < bound → IsUFormula M6.PA.RelationalSource.language (F lookup ![i,v]))
    (hmatch : shift M6.PA.RelationalSource.language (F lookup ![j,v]) = target) :
    let found := F search ![bound,v,target]
    found < bound ∧ shift M6.PA.RelationalSource.language (F lookup ![found,v]) = target := by
  let params : ℕ → M := fun n => if n = 0 then v else target
  have hp : (fun i : Fin 2 => params i.val) = ![v,target] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [params]
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp [params]
  have hw : F mismatch ![j,v,target] = 0 := (mismatch_model j v target (hvalid j hj)).mpr hmatch
  have hu := modelSearchUniversal mismatch bound params
  have hi := modelSearchCandidateInvariant mismatch bound params
  have hb := modelSearchBound mismatch bound params
  rw [hp] at hu hi hb
  change (F search ![bound,v,target] = bound ↔ ∀ x, x < bound → F mismatch ![x,v,target] ≠ 0) at hu
  change F mismatch ![F search ![bound,v,target],v,target] = 0 ∨ F search ![bound,v,target] = bound at hi
  change F search ![bound,v,target] < bound ∨ F search ![bound,v,target] = bound at hb
  have hne : F search ![bound,v,target] ≠ bound := by
    intro he
    exact (hu.mp he j hj) hw
  have hlt : F search ![bound,v,target] < bound := hb.resolve_right hne
  have hz : F mismatch ![F search ![bound,v,target],v,target] = 0 := hi.resolve_right hne
  exact ⟨hlt, (mismatch_model _ v target (hvalid _ hlt)).mp hz⟩

#print axioms mismatch_model
#print axioms find_match
end models
end PA194SearchModel
