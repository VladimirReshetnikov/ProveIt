import DiophantineConsistency.PRAModelISigmaZero
import Foundation.FirstOrder.Arithmetic.IOpen.Basic
set_option autoImplicit false
namespace DiophantineConsistency.PRAModelIOpenPairing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelISigmaZero

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem reduct_eq_standard :
    (inferInstance : Structure language M).lMap embedding = LO.FirstOrder.Arithmetic.standardModel M := by
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  apply standardModel_unique'
  · constructor
    simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Semiterm.val_func]
    change Structure.func (L := language) (M := M) (Code.zero 0) (Semiterm.val ![] Empty.elim ∘ ![]) = Structure.func (L := language) (M := M) (Code.zero 0) Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  · constructor
    simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
    change Structure.func (L := language) (M := M) oneCode (Semiterm.val ![] Empty.elim ∘ ![]) = Structure.func (L := language) (M := M) oneCode Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  · exact ⟨fun _ _ => rfl⟩
  · exact ⟨fun _ _ => rfl⟩
  · constructor
    intro x y
    exact eqRel ![x,y]
  · exact ⟨fun _ _ => Iff.rfl⟩

theorem standardModelISigmaZero : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  have h := modelReductISigmaZero (M := M)
  rw [reduct_eq_standard] at h
  exact h

theorem standardModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺₀) standardModelISigmaZero
/-- Foundation's pairing and both projections satisfy their full round trip
in every candidate-PRA model, not just the standard naturals. -/
theorem modelPairing (a b : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    pi₁ (pair a b) = a ∧ pi₂ (pair a b) = b ∧ a ≤ pair a b ∧ b ≤ pair a b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  exact ⟨pi₁_pair a b, pi₂_pair a b, le_pair_left a b, le_pair_right a b⟩
theorem pairGraph_spec (a b t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    (Semiformula.lMap embedding pairDef.val).Eval ![t,a,b] Empty.elim ↔ t = pair a b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [Semiformula.eval_lMap]
  rw [reduct_eq_standard]
  simpa [pairDef] using (pair_graph (a := a) (b := b) (c := t)).symm
/-- The mapped bounded graph has a pair value, uniquely determines both
components, and bounds each component in every candidate-PRA model. -/
theorem modelPairGraph (a b : M) :
    ∃ t : M,
      (Semiformula.lMap embedding pairDef.val).Eval ![t,a,b] Empty.elim ∧
      (∀ a' b', (Semiformula.lMap embedding pairDef.val).Eval ![t,a',b'] Empty.elim → a' = a ∧ b' = b) ∧
      ¬Structure.rel (L := language) Language.ORing.Rel.lt ![t,a] ∧
      ¬Structure.rel (L := language) Language.ORing.Rel.lt ![t,b] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  refine ⟨pair a b, (pairGraph_spec a b _).mpr rfl, ?_, ?_, ?_⟩
  · intro a' b' h
    have he := (pairGraph_spec a' b' _).mp h
    exact pair_ext_iff.mp he.symm
  · change ¬pair a b < a
    exact not_lt_of_ge (le_pair_left a b)
  · change ¬pair a b < b
    exact not_lt_of_ge (le_pair_right a b)
end models
end DiophantineConsistency.PRAModelIOpenPairing
