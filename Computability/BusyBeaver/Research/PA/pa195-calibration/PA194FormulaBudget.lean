import PA194ParamHistory
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic
/-! A candidate-PRA history indexed by a packed formula and depth budget. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194FormulaBudget
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
  PA194StackCode PA194StackHistory PA194ParamHistory

def packedResult (next : Code 4) : Code 4 :=
  .comp (translationCode next)
    (.cons (bin pairCode (.proj 0) (.proj 1))
      (.cons (.proj 2) (.cons (.proj 3) (.nil 4))))
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

theorem modelPackedResult (next : Code 4) (p budget label ceiling : M) :
    F (packedResult next) ![p,budget,label,ceiling] =
      F (translationCode next) ![pair p budget,label,ceiling] := by
  rw [packedResult,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change F (bin pairCode (.proj 0) (.proj 1)) ![p,budget,label,ceiling] = pair p budget
    rw [modelBin,modelPairCode,modelProjection,modelProjection]
    rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact modelProjection 2 _
    · exact Fin.cases (modelProjection 3 _) (fun j => Fin.elim0 j) j

/-- A child at the same budget precedes its parent. -/
theorem same_budget_lt (child parent budget : M) (h : child < parent) :
    pair child budget < pair parent budget := pair_lt_pair_left h budget

/-- Under a quantifier, both the source code and budget decrease. -/
theorem binder_budget_lt (child parent budget : M) (h : child < parent) :
    pair child budget < pair parent (budget+1) := pair_lt_pair h (lt_add_one budget)

/-- The history computes an earlier child with unchanged budget. -/
theorem lookup_same (next : Code 4) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (child parent budget label ceiling : M) (h : child < parent) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![F distanceCode ![pair parent budget,pair child budget],
        F (historyCode next) ![pair parent budget,label,ceiling]] =
      F (packedResult next) ![child,budget,label,ceiling] := by
  rw [modelPackedResult]
  exact modelLookupEarlier next head tail hhead htail _ _ _ _ (same_budget_lt _ _ _ h)

/-- The history computes an earlier child with one less remaining budget. -/
theorem lookup_binder (next : Code 4) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (child parent budget label ceiling : M) (h : child < parent) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![F distanceCode ![pair parent (budget+1),pair child budget],
        F (historyCode next) ![pair parent (budget+1),label,ceiling]] =
      F (packedResult next) ![child,budget,label,ceiling] := by
  rw [modelPackedResult]
  exact modelLookupEarlier next head tail hhead htail _ _ _ _ (binder_budget_lt _ _ _ h)

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Both quantifier constructors have a strictly earlier packed body. -/
theorem all_body_lt (p budget : M) : pair p budget < pair (^∀ p) (budget+1) :=
  binder_budget_lt p _ budget (by simp)
theorem exs_body_lt (p budget : M) : pair p budget < pair (^∃ p) (budget+1) :=
  binder_budget_lt p _ budget (by simp)

/-- Both Boolean children are earlier at the same budget. -/
theorem and_left_lt (p q budget : M) : pair p budget < pair (p ^⋏ q) budget :=
  same_budget_lt p _ budget (by simp)
theorem and_right_lt (p q budget : M) : pair q budget < pair (p ^⋏ q) budget :=
  same_budget_lt q _ budget (by simp)
theorem or_left_lt (p q budget : M) : pair p budget < pair (p ^⋎ q) budget :=
  same_budget_lt p _ budget (by simp)
theorem or_right_lt (p q budget : M) : pair q budget < pair (p ^⋎ q) budget :=
  same_budget_lt q _ budget (by simp)

#print axioms all_body_lt
#print axioms and_left_lt
#print axioms modelPackedResult
#print axioms lookup_same
#print axioms lookup_binder
end models
end PA194FormulaBudget
