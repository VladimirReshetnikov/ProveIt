import PA196PANegationBound
import DiophantineConsistency.PRAWitnessNegExistential

/-! A growth bound and bounded existential rule for arithmetic-language
negation. The bound is transferred to every classical PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PANegBoundTerms
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
open PRAWitnessNegExistential

section sigma1
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem lift_tau_id {p P y : V} (hp : p + 2 ≤ P)
    (hy : y ≤ tau (p + 8) (2 * p + 6)) : y ≤ tau (P + 8) (2 * P + 2) :=
  le_trans hy (tau_mono (add_le_add (le_trans le_self_add hp) le_rfl) (depth_step hp))

theorem neg_le : ∀ p : V, IsUFormula ℒₒᵣ p → neg ℒₒᵣ p ≤ tau (p + 8) (2 * p + 6) := by
  refine IsUFormula.ISigma1.sigma1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv
    rw [neg_rel hR hv]
    set P := ^rel k R v
    have h := code4_le_tau (le_tau_of P 1 0 (by simpa using small_le P (n := 1) (by norm_num)))
      (le_tau_of P k 0 (le_trans (arity_lt_rel k R v).le le_self_add))
      (le_tau_of P R 0 (le_trans (r_lt_rel k R v).le le_self_add))
      (le_tau_of P v 0 (le_trans (v_lt_rel k R v).le le_self_add))
    exact le_trans (by simpa [qqNRel] using h) (tau_mono le_rfl (depth6_le _))
  · intro k R v hR hv
    rw [neg_nrel hR hv]
    set P := ^nrel k R v
    have h := code4_le_tau (le_tau_of P 0 0 (by simp))
      (le_tau_of P k 0 (le_trans (arity_lt_nrel k R v).le le_self_add))
      (le_tau_of P R 0 (le_trans (r_lt_nrel k R v).le le_self_add))
      (le_tau_of P v 0 (le_trans (v_lt_nrel k R v).le le_self_add))
    exact le_trans (by simpa [qqRel] using h) (tau_mono le_rfl (depth6_le _))
  · rw [neg_verum]
    have h := code2_le_tau (le_tau_of (^⊤ : V) 3 0 (by simpa using small_le (^⊤ : V) (n := 3) (by norm_num)))
      (le_tau_of (^⊤ : V) 0 0 (by simp))
    exact le_trans (by simpa [qqFalsum] using h) (tau_mono le_rfl (depth2_le _))
  · rw [neg_falsum]
    have h := code2_le_tau (le_tau_of (^⊥ : V) 2 0 (by simpa using small_le (^⊥ : V) (n := 2) (by norm_num)))
      (le_tau_of (^⊥ : V) 0 0 (by simp))
    exact le_trans (by simpa [qqVerum] using h) (tau_mono le_rfl (depth2_le _))
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq]
    set P := p ^⋏ q
    have hp2 := add_two_le_and_left p q; have hq2 := add_two_le_and_right p q
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have hnq : neg ℒₒᵣ q ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hq2 ihq
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    exact le_trans (by simpa [qqOr] using h) (tau_mono le_rfl (depth_three P))
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq]
    set P := p ^⋎ q
    have hp2 := add_two_le_or_left p q; have hq2 := add_two_le_or_right p q
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have hnq : neg ℒₒᵣ q ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hq2 ihq
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    exact le_trans (by simpa [qqAnd] using h) (tau_mono le_rfl (depth_three P))
  · intro p hp ihp
    rw [neg_all hp]
    set P := ^∀ p
    have hp2 := add_two_le_all p
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    exact le_trans (by simpa [qqExs] using h) (tau_mono le_rfl (depth_two P))
  · intro p hp ihp
    rw [neg_ex hp]
    set P := ^∃ p
    have hp2 := add_two_le_exs p
    have hnp : neg ℒₒᵣ p ≤ tau (P + 8) (2 * P + 2) :=
      lift_tau_id hp2 ihp
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    exact le_trans (by simpa [qqAll] using h) (tau_mono le_rfl (depth_two P))

end sigma1

theorem negBoundAt_spec {n : ℕ} (i : Fin n) {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) :
    neg ℒₒᵣ (e i) ≤ (negBoundAt i).vval e := by
  by_cases h : IsUFormula ℒₒᵣ (e i)
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
      ψ.Eval (y :> e) Empty.elim → (negGraph ℒₒᵣ).val.Evalb ![y,e i]) :
    WB M (∃⁰ ψ) := by
  refine wb_exs_bt ψ hψ (negBoundAt i) ?_ hWB
  intro V _ _ e y hy
  have h := hgraph V e y hy
  simp at h
  rw [h]
  exact negBoundAt_spec i e

#print axioms neg_le
#print axioms wb_exs_neg
end PA196PANegBoundTerms
