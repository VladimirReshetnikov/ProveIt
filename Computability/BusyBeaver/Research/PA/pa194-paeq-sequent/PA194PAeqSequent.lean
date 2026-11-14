import PA194PAeqFormulaClosure
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-! Exact HFS sequent image under the original-to-PAeq syntax function.
This uses actual Sigma-one replacement, not a host list/set map. -/
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sequent_existsUnique (s : V) :
    ∃! t : V, ∀ y : V, y∈t ↔ ∃ x : V, x∈s ∧ y=formulaCode (0:V) x := sigma₁_replacement (by definability) s
noncomputable def sequentCode (s : V) : V := Classical.choose! (sequent_existsUnique s)
theorem mem_sequentCode {s y : V} : y∈sequentCode s ↔ ∃ x : V, x∈s ∧ y=formulaCode (0:V) x :=
  Classical.choose!_spec (sequent_existsUnique s) y
attribute [local irreducible] formulaCodeGraph
noncomputable def sequentGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out s. (∀ y∈'out, ∃ x∈'s, !formulaCodeGraph y 0 x) ∧
    (∀ x∈'s, ∃y, !formulaCodeGraph y 0 x ∧ y∈out)”
theorem sequent_graph_iff (out s : V) : out=sequentCode s ↔
    (∀y∈out,∃ x : V, x∈s ∧ y=formulaCode (0:V) x) ∧ (∀x∈s,formulaCode (0:V) x∈out) := by
  constructor
  · rintro rfl
    exact ⟨fun _ h=>mem_sequentCode.mp h,fun x h=>mem_sequentCode.mpr ⟨x,h,rfl⟩⟩
  · rintro ⟨h₁,h₂⟩
    apply mem_ext; intro y; constructor
    · intro h; exact mem_sequentCode.mpr (h₁ y h)
    · intro h; obtain ⟨x,hx,rfl⟩:=mem_sequentCode.mp h; exact h₂ x hx
instance sequent_defined : 𝚺₁-Function₁ (sequentCode : V→V) via sequentGraph :=
  .mk fun v => by simp [sequentGraph,sequent_graph_iff,Matrix.comp_vecCons'']
instance sequent_definable : 𝚺₁-Function₁ (sequentCode : V→V) := sequent_defined.to_definable

theorem sequent_graph (out s : V) : sequentGraph.val.Evalb ![out,s] ↔ out=sequentCode s :=
  sequent_defined.defined ![out,s]
theorem sequent_member {s p : V} (hp : p∈s) : formulaCode (0:V) p∈sequentCode s :=
  mem_sequentCode.mpr ⟨p,hp,rfl⟩
@[simp] theorem sequent_empty : sequentCode (∅:V)=∅ := mem_ext (by simp [mem_sequentCode])
@[simp] theorem sequent_insert (p s : V) : sequentCode (insert p s)=insert (formulaCode (0:V) p) (sequentCode s) :=
  mem_ext (by simp [mem_sequentCode])
@[simp] theorem sequent_singleton (p : V) : sequentCode ({p}:V)={formulaCode (0:V) p} := by
  exact mem_ext (by simp [mem_sequentCode])

theorem sequent_valid {s : V} (hs : IsFormulaSet ℒₒᵣ s) : IsFormulaSet PA194PAeq.language (sequentCode s) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=mem_sequentCode.mp hp
  exact formulaCode_valid 0 (hs q hq)
theorem sequent_mono {s t : V} (h : s⊆t) : sequentCode s⊆sequentCode t := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=mem_sequentCode.mp hp
  exact sequent_member (h hq)

theorem sequent_shift {s : V} (hs : IsFormulaSet ℒₒᵣ s) :
    sequentCode (setShift ℒₒᵣ s)=setShift PA194PAeq.language (sequentCode s) := by
  apply mem_ext; intro y
  constructor
  · intro hy
    obtain ⟨q,hq,rfl⟩:=mem_sequentCode.mp hy
    obtain ⟨p,hp,rfl⟩:=mem_setShift_iff.mp hq
    rw [formulaCode_shift 0 (hs p hp).isUFormula]
    exact shift_mem_setShift (sequent_member hp)
  · intro hy
    obtain ⟨q,hq,rfl⟩:=mem_setShift_iff.mp hy
    obtain ⟨p,hp,rfl⟩:=mem_sequentCode.mp hq
    rw [←formulaCode_shift 0 (hs p hp).isUFormula]
    exact sequent_member (shift_mem_setShift hp)

#print axioms sequent_existsUnique
#print axioms mem_sequentCode
#print axioms sequent_graph_iff
#print axioms sequent_defined
#print axioms sequent_graph
#print axioms sequent_member
#print axioms sequent_empty
#print axioms sequent_insert
#print axioms sequent_singleton
#print axioms sequent_valid
#print axioms sequent_mono
#print axioms sequent_shift
end PA194PAeqTermBlueprint

