import DiophantineConsistency.PRAWitnessBoundTerms
/-! Transfer a substs1Graph output bound through an existential at arbitrary
input indices, without assuming IΣ₁ in candidate-PRA models. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessSubstsExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
noncomputable def substs1BoundAt {n : ℕ} (i j : Fin n) : BoundTerm n :=
  exp2 (poly ((Rew.subst ![#i,#j]) ‘#0 + #1 + 8 + 4’))
    (poly ((Rew.subst ![#i,#j]) ‘4 * #1 + 6’))
theorem substs1BoundAt_spec {n : ℕ} (i j : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    substs1 ℒₛₑₜ (e i) (e j) ≤ (substs1BoundAt i j).vval e := by
  simpa [substs1BoundAt, BoundTerm.vval, Semiterm.val_rew, numeral_eq_natCast, tau] using substs1_le (e i) (e j)
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_exs_substs1 {n : ℕ} (i j : Fin n) (ψ : ArithmeticSemisentence (n+1))
    (hψ : Hierarchy 𝚺 1 ψ) (hWB : WB M ψ)
    (hgraph : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (y : V),
      ψ.Eval (y :> e) Empty.elim → (substs1Graph ℒₛₑₜ).val.Evalb ![y,e i,e j]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (substs1BoundAt i j) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact substs1BoundAt_spec i j e
end DiophantineConsistency.PRAWitnessSubstsExistential
