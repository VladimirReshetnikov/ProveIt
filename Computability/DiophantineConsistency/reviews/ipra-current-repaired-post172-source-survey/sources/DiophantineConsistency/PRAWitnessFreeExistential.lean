import DiophantineConsistency.PRAWitnessBoundTerms
/-! Transfer a freeGraph output bound at any selected input index through an
existential, without assuming IΣ₁ in candidate-PRA models. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessFreeExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
noncomputable def freeBoundAt {n : ℕ} (i : Fin n) : BoundTerm n :=
  exp2 (poly ((Rew.subst ![#i]) ‘(#0 + 2) * (#0 + 2) + 1 + 8 + 4’))
    (poly ((Rew.subst ![#i]) ‘4 * #0 + 6’))
theorem freeBoundAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    free ℒₛₑₜ (e i) ≤ (freeBoundAt i).vval e := by
  simpa [freeBoundAt, BoundTerm.vval, Semiterm.val_rew, numeral_eq_natCast, tau] using free_le (e i)
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_exs_free {n : ℕ} (i : Fin n) (ψ : ArithmeticSemisentence (n+1))
    (hψ : Hierarchy 𝚺 1 ψ) (hWB : WB M ψ)
    (hgraph : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (y : V),
      ψ.Eval (y :> e) Empty.elim → (freeGraph ℒₛₑₜ).val.Evalb ![y,e i]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (freeBoundAt i) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact freeBoundAt_spec i e
end DiophantineConsistency.PRAWitnessFreeExistential
