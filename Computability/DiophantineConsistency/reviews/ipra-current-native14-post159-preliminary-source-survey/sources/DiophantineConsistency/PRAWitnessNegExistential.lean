import DiophantineConsistency.PRAWitnessBoundTerms
/-! Transfer the formula-negation output bound at any chosen input index
through an existential in Foundation arithmetic syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessNegExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
noncomputable def negBoundAt {n : ℕ} (i : Fin n) : BoundTerm n :=
  exp2 (poly ((Rew.subst ![#i]) ‘#0 + 8 + 4’))
    (poly ((Rew.subst ![#i]) ‘2 * #0 + 6’))
theorem negBoundAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    neg ℒₛₑₜ (e i) ≤ (negBoundAt i).vval e := by
  by_cases h : IsUFormula ℒₛₑₜ (e i)
  · simpa [negBoundAt, BoundTerm.vval, Semiterm.val_rew, numeral_eq_natCast, tau] using neg_le (e i) h
  · rw [neg_not_uformula h]; simp
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_exs_neg {n : ℕ} (i : Fin n) (ψ : ArithmeticSemisentence (n+1))
    (hψ : Hierarchy 𝚺 1 ψ) (hWB : WB M ψ)
    (hgraph : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (y : V),
      ψ.Eval (y :> e) Empty.elim → (negGraph ℒₛₑₜ).val.Evalb ![y,e i]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (negBoundAt i) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact negBoundAt_spec i e
end DiophantineConsistency.PRAWitnessNegExistential
