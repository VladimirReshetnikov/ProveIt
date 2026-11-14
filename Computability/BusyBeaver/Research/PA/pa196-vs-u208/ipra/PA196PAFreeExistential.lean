import PA196PRAWitnessNestedTower
import PA196PAFreeGrowth

/-! Bound any existential whose witness is a value of the arithmetic free
function, using a candidate-PRA tower of an exponential bound. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PAFreeExistential
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
  PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PA196PAQVecTowerAlgebra PA196PRAWitnessNestedTower PA196PAFreeGrowth

noncomputable def freeArgumentAt {n : ℕ} (i : Fin n) : BoundTerm n :=
  add (tauT (poly ((Rew.subst ![#i]) ‘3 * #0 + 8’))
      (poly ((Rew.subst ![#i]) ‘22 * #0 + 30’))) (poly ‘37’)

theorem freeArgumentAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    freeArgument (e i) ≤ (freeArgumentAt i).vval e := by
  have hf : (^&(0:V)) ≤ 5 := by
    have hh := PRAWitnessFormulaFunctions.code2_le (1 : V) 0
    change ⟪(1:V),0⟫ + 1 ≤ (5:V)
    convert hh using 1 <;> norm_num
  have hc : ((^&(0:V)+1)*(^&(0:V)+1)+1) ≤ 37 := by
    have h1 : (^&(0:V))+1 ≤ (5:V)+1 := add_le_add hf le_rfl
    have h : ((^&(0:V))+1)*((^&(0:V))+1)+1 ≤ ((5:V)+1)*((5:V)+1)+1 :=
      add_le_add (mul_le_mul' h1 h1) le_rfl
    norm_num at h
    exact h
  simpa [freeArgumentAt, freeArgument, vval_tauT, BoundTerm.vval, Semiterm.val_rew, numeral_eq_natCast]
    using add_le_add (le_refl (tau (3*(e i)+8) (22*(e i)+30))) hc

theorem freeBoundAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    free ℒₒᵣ (e i) ≤ iter ((freeArgumentAt i).vval e+2) (4*(freeArgumentAt i).vval e+1) := by
  have h := freeArgumentAt_spec i e
  exact le_trans (free_le_tower (e i))
    (le_trans (iter_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl h) le_rfl))
      (iter_index_mono _ _ _ (add_le_add h le_rfl)))

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
      ψ.Eval (y :> e) Empty.elim → (freeGraph ℒₒᵣ).val.Evalb ![y,e i]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_nested ψ hψ (freeArgumentAt i) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact freeBoundAt_spec i e

#print axioms freeBoundAt_spec
#print axioms wb_exs_free
end PA196PAFreeExistential
