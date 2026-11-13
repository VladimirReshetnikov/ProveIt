module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateNegation
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
@[expose] public section
/-! A finite host multiset of templates becomes an actual model HFS sequent.
Multiplicity is intentionally forgotten, as in the pinned numeric calculus. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance : LeftCommutative (fun a s : V => insert a s) where
  left_comm a b s := mem_ext (by intro x; simp; tauto)
noncomputable def modelSet (s : Multiset V) : V := s.foldr (fun a s => insert a s) ∅
theorem mem_modelSet (s : Multiset V) (x : V) : x∈modelSet s ↔ x∈s := by
  induction s using Multiset.induction_on with
  | empty => simp [modelSet]
  | cons a s ih =>
    simp only [modelSet,Multiset.foldr_cons,mem_bitInsert_iff,Multiset.mem_cons]
    exact or_congr_right ih
noncomputable def sequentValue (Γ : LK.Sequent sourceLanguage) (P f : V) : V :=
  modelSet (Γ.map (fun p => formulaValue p P 0 f))
theorem mem_sequentValue (Γ : LK.Sequent sourceLanguage) (P f x : V) :
    x∈sequentValue Γ P f ↔ ∃p∈Γ,x=formulaValue p P 0 f := by
  simp only [sequentValue,mem_modelSet,Multiset.mem_map]
  constructor
  · rintro ⟨p,hp,hx⟩; exact ⟨p,hp,hx.symm⟩
  · rintro ⟨p,hp,hx⟩; exact ⟨p,hp,hx.symm⟩
@[simp] theorem sequentValue_empty (P f : V) : sequentValue 0 P f=∅ := by
  apply mem_ext; intro x; simp [mem_sequentValue]
@[simp] theorem sequentValue_cons (p : Formula 0) (Γ : LK.Sequent sourceLanguage) (P f : V) :
    sequentValue (p::ₘΓ) P f=insert (formulaValue p P 0 f) (sequentValue Γ P f) := by
  apply mem_ext; intro x; simp [mem_sequentValue]
@[simp] theorem sequentValue_add (Γ Δ : LK.Sequent sourceLanguage) (P f : V) :
    sequentValue (Γ+Δ) P f=sequentValue Γ P f ∪ sequentValue Δ P f := by
  apply mem_ext; intro x; simp only [mem_sequentValue,Multiset.mem_add,mem_cup_iff]
  aesop

def SequentCovered (Γ : LK.Sequent sourceLanguage) (f : V) : Prop :=
  ∀p∈Γ,∀i,p.FVar? i→(i:V)<len f

theorem sequentValue_isFormulaSet (Γ : LK.Sequent sourceLanguage) {P f : V}
    (hP : IsSemiformula RelationalSource.language 1 P)
    (hf : IsSemitermVec RelationalSource.language (len f) 0 f)
    (hΓ : SequentCovered Γ f) : IsFormulaSet RelationalSource.language (sequentValue Γ P f) := by
  intro x hx
  rcases (mem_sequentValue Γ P f x).mp hx with ⟨p,hp,rfl⟩
  exact formulaValue_isSemiformula p hP ⟨by simp,hf⟩ (hΓ p hp)
#print axioms mem_sequentValue
#print axioms sequentValue_add
#print axioms sequentValue_isFormulaSet
end M6.PA.RelationalPredicateTemplate
