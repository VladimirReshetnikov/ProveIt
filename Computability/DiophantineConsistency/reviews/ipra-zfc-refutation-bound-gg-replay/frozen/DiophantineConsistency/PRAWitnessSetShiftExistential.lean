import DiophantineConsistency.PRAWitnessSetShiftOutput
/-! Transfer a setShift output bound at any chosen input index through an
existential in the actual Foundation arithmetic syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessSetShiftExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus

noncomputable def setShiftBoundAt {n : ℕ} (i : Fin n) : BoundTerm n :=
  exp2 (poly ‘1’) (poly ((Rew.subst ![#i])
    ‘((#0+2)*(#0+2)+1+8+4)*(#0*#0*64)+1’))

theorem setShiftBoundAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    setShift ℒₛₑₜ (e i) ≤ (setShiftBoundAt i).vval e := by
  simpa [setShiftBoundAt, BoundTerm.vval, Semiterm.val_rew, numeral_eq_natCast] using setShift_le (e i)

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_exs_setShift {n : ℕ} (i : Fin n) (ψ : ArithmeticSemisentence (n+1))
    (hψ : Hierarchy 𝚺 1 ψ) (hWB : WB M ψ)
    (hgraph : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (y : V),
      ψ.Eval (y :> e) Empty.elim → (setShiftGraph ℒₛₑₜ).val.Evalb ![y,e i]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (setShiftBoundAt i) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact setShiftBoundAt_spec i e
end DiophantineConsistency.PRAWitnessSetShiftExistential
