import PA194Schematic
import PA194NameForms
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194NameValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic

def ar : Fin 4 → ℕ := ![1,2,1,2]
abbrev L := boxL ar
abbrev Term (n : ℕ) := FirstOrder.Semiterm L Empty n
abbrev Formula (n : ℕ) := FirstOrder.Semiformula L Empty n

def dom {n : ℕ} (x : Term n) : Formula n := .rel (.box 0) ![x]
def var {n : ℕ} (x y : Term n) : Formula n := .rel (.box 1) ![x,y]
def val {n : ℕ} (x : Term n) : Formula n := .rel (.box 2) ![x]
def iso {n : ℕ} (x y : Term n) : Formula n := .rel (.box 3) ![x,y]

def schema : Sentence L :=
  (∃⁰ (dom (.bvar 0) ⋏ (∃⁰ (∃⁰ (var (.bvar 1) (.bvar 2) ⋏
    (val (.bvar 0) ⋏ iso (.bvar 1) (.bvar 0))))))) 🡒 (∃⁰ val (.bvar 0))

theorem schema_valid (M : Type) [Nonempty M] [Structure L M] : M↓[L] ⊧ schema := by
  simp [models_iff,schema,Semiformula.eval_ex]
  intro x _ v w _ hval _
  refine ⟨w, ?_⟩
  simpa [val,Semiformula.eval_rel,Function.comp_def] using hval
#print axioms schema_valid
end PA194NameValueSchema
