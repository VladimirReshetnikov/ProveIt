import DiophantineConsistency.PRAWitnessBoundTerms
/-! Transfer an insert-graph output bound through an existential at arbitrary
input indices, without assuming IΣ₁ in candidate-PRA models. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessInsertExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
noncomputable def insertBoundAt {n : ℕ} (i j : Fin n) : BoundTerm n :=
  add (poly ((Rew.subst ![#j]) ‘#0’)) (exp2 (poly ‘1’) (poly ((Rew.subst ![#i]) ‘#0’)))
theorem insertBoundAt_spec {n : ℕ} (i j : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    insert (e i) (e j) ≤ (insertBoundAt i j).vval e := by
  have h := insert_le_of_le_of_le (i := e i) (j := e i) (a := e j) (b := e j) le_rfl le_rfl
  have hexp := exp_monotone_le.mpr (le_of_lt (lt_exp (e i)))
  simpa [insertBoundAt, BoundTerm.vval, Semiterm.val_rew, numeral_eq_natCast] using le_trans h (add_le_add le_rfl hexp)
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_exs_insert {n : ℕ} (i j : Fin n) (ψ : ArithmeticSemisentence (n+1))
    (hψ : Hierarchy 𝚺 1 ψ) (hWB : WB M ψ)
    (hgraph : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (y : V),
      ψ.Eval (y :> e) Empty.elim → insertDef.val.Evalb ![y,e i,e j]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (insertBoundAt i j) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact insertBoundAt_spec i j e
end DiophantineConsistency.PRAWitnessInsertExistential
