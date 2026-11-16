import PA194Schematic
import PA194NameForms
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic

def ar : Fin 3 → ℕ := ![1,1,2]
abbrev L := boxL ar
abbrev Term (n : ℕ) := FirstOrder.Semiterm L Empty n
abbrev Formula (n : ℕ) := FirstOrder.Semiformula L Empty n

def dom {n : ℕ} (x : Term n) : Formula n := .rel (.box 0) ![x]
def rest {n : ℕ} (x : Term n) : Formula n := .rel (.box 1) ![x]
def rel {n : ℕ} (x y : Term n) : Formula n := .rel (.box 2) ![x,y]

def succTotal : Sentence L := ∀⁰ (dom (.bvar 0) 🡒
  (∃⁰ (dom (.bvar 0) ⋏ rel (.bvar 1) (.bvar 0))))
def hasValue : Sentence L := ∃⁰ (dom (.bvar 0) ⋏ rest (.bvar 0))
def succValue : Sentence L := ∃⁰ (dom (.bvar 0) ⋏
  (∃⁰ ((dom (.bvar 0) ⋏ rest (.bvar 0)) ⋏ rel (.bvar 0) (.bvar 1))))
def schema : Sentence L := succTotal 🡒 (hasValue 🡒 succValue)

theorem schema_valid (M : Type) [Nonempty M] [Structure L M] : M↓[L] ⊧ schema := by
  simp [models_iff,schema,succTotal,hasValue,succValue,Semiformula.eval_ex,Semiformula.eval_all,
    dom,rest,rel,Semiformula.eval_rel,Function.comp_def]
  intro h x hdx hrx
  obtain ⟨z, hdz, hzx⟩ := h x hdx
  refine ⟨z,hdz,x,⟨hdx,hrx⟩,?_⟩
  convert hzx using 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
#print axioms schema_valid
end PA194SuccValueSchema
