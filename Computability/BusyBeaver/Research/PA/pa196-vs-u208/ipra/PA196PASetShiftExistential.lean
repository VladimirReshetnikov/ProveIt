import PA196PASetShift
import DiophantineConsistency.PRAWitnessSetShiftExistential

/-! Bounded existential witnesses for arithmetic set-shift outputs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASetShiftExistential
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm

noncomputable def boundAt {n : ℕ} (i : Fin n) : BoundTerm n :=
  exp2 (poly ‘1’) (add (tauT (poly ((Rew.subst ![#i]) ‘3*#0+8’))
    (poly ((Rew.subst ![#i]) ‘22*#0+30’))) (poly ‘1’))

theorem boundAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    setShift ℒₒᵣ (e i) ≤ (boundAt i).vval e := by
  simpa [boundAt, BoundTerm.vval, vval_tauT, Semiterm.val_rew, numeral_eq_natCast] using
    PA196PASetShift.setShift_le (e i)

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
      ψ.Eval (y :> e) Empty.elim → (setShiftGraph ℒₒᵣ).val.Evalb ![y,e i]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (boundAt i) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact boundAt_spec i e

#print axioms boundAt_spec
#print axioms wb_exs_setShift
end PA196PASetShiftExistential
