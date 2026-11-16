module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeClosure
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
@[expose] public section

/-! Exact HFS sequent image under the original-to-PAeq syntax function.
This uses actual Sigma-one replacement, not a host list/set map. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sequent_existsUnique (s : V) :
    ∃! t : V, ∀ y,y∈t ↔ ∃x∈s,y=formulaCode 0 x := sigma₁_replacement (by definability) s
noncomputable def sequentCode (s : V) : V := Classical.choose! (sequent_existsUnique s)
theorem mem_sequentCode {s y : V} : y∈sequentCode s ↔ ∃x∈s,y=formulaCode 0 x :=
  Classical.choose!_spec (sequent_existsUnique s) y
attribute [local irreducible] formulaCodeGraph
noncomputable def sequentGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out s. (∀ y∈'out, ∃ x∈'s, !formulaCodeGraph y 0 x) ∧
    (∀ x∈'s, ∃y, !formulaCodeGraph y 0 x ∧ y∈out)”
theorem sequent_graph_iff (out s : V) : out=sequentCode s ↔
    (∀y∈out,∃x∈s,y=formulaCode 0 x) ∧ (∀x∈s,formulaCode 0 x∈out) := by
  constructor
  · rintro rfl
    exact ⟨fun _ h=>mem_sequentCode.mp h,fun x h=>mem_sequentCode.mpr ⟨x,h,rfl⟩⟩
  · rintro ⟨h₁,h₂⟩
    apply mem_ext; intro y; constructor
    · intro h; exact mem_sequentCode.mpr (h₁ y h)
    · intro h; obtain ⟨x,hx,rfl⟩:=mem_sequentCode.mp h; exact h₂ x hx
instance sequent_defined : 𝚺ᴬ₁-Function₁ (sequentCode : V→V) via sequentGraph :=
  .mk fun v => by simp [sequentGraph,sequent_graph_iff,formulaCode_graph,Matrix.comp_vecCons'']
instance sequent_definable : 𝚺ᴬ₁-Function₁ (sequentCode : V→V) := sequent_defined.to_definable

theorem sequent_graph (out s : V) : sequentGraph.val.Evalb ![out,s] ↔ out=sequentCode s :=
  sequent_defined.defined ![out,s]
theorem sequent_member {s p : V} (hp : p∈s) : formulaCode 0 p∈sequentCode s :=
  mem_sequentCode.mpr ⟨p,hp,rfl⟩
@[simp] theorem sequent_empty : sequentCode (∅:V)=∅ := mem_ext (by simp [mem_sequentCode])
@[simp] theorem sequent_insert (p s : V) : sequentCode (insert p s)=insert (formulaCode 0 p) (sequentCode s) :=
  mem_ext (by simp [mem_sequentCode])
@[simp] theorem sequent_singleton (p : V) : sequentCode ({p}:V)={formulaCode 0 p} := by
  exact mem_ext (by simp [mem_sequentCode])

theorem sequent_valid {s : V} (hs : IsFormulaSet ℒₒᵣ s) : IsFormulaSet Presentation.language (sequentCode s) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=mem_sequentCode.mp hp
  exact formulaCode_valid 0 (hs q hq)
theorem sequent_mono {s t : V} (h : s⊆t) : sequentCode s⊆sequentCode t := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=mem_sequentCode.mp hp
  exact sequent_member (h hq)

theorem sequent_shift {s : V} (hs : IsFormulaSet ℒₒᵣ s) :
    sequentCode (setShift ℒₒᵣ s)=setShift Presentation.language (sequentCode s) := by
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
end M6.PA.FoundationPAeqCode

