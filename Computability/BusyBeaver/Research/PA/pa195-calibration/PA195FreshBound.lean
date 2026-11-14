import BusyBeaver.ZFC.ArithmeticCantor
import DiophantineConsistency.PRAWitnessTransfer

/-! Bounds for the exact PA195 tagged Cantor formula codes. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA195FreshBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAModelIOpenPairing

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem pair_lt_tagged (a b tag : V) (hpos : 0 < 4 * cantor a b + tag) :
    a < 4 * cantor a b + tag ∧ b < 4 * cantor a b + tag := by
  let p := cantor a b
  have hpq : p < 4 * p + tag := by
    rcases Arithmetic.zero_le p with hp | hp
    · have hp0 : cantor a b = 0 := hp.symm
      change cantor a b < 4 * cantor a b + tag
      simp only [hp0, mul_zero, zero_add] at hpos ⊢
      exact hpos
    · have hp' : p < p + p := by simpa using (lt_add_of_pos_right p hp)
      have hle : p + p ≤ 4 * p + tag := by
        calc
          p + p ≤ (p + p) + (p + p) := by simp
          _ = 4 * p := by ring
          _ ≤ 4 * p + tag := by simp
      exact lt_of_lt_of_le hp' hle
  exact ⟨lt_of_le_of_lt (components_le a b).1 hpq,
    lt_of_le_of_lt (components_le a b).2 hpq⟩

abbrev cantorGraph := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef

noncomputable def fieldBound : ArithmeticSemisentence 4 :=
  “p a b tag. !cantorGraph p a b → (0 < 4 * p + tag →
    (a < 4 * p + tag ∧ b < 4 * p + tag))”

theorem candidate_pra_fieldBound : PRA ⊢ Semiformula.lMap embedding (∀⁰* fieldBound) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  rw [Semiformula.models_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  have h (hp : e 0 = cantor (e 1) (e 2)) (hpos : 0 < 4 * e 0 + e 3) :
      e 1 < 4 * e 0 + e 3 ∧ e 2 < 4 * e 0 + e 3 := by
    rw [hp] at hpos ⊢
    exact pair_lt_tagged (e 1) (e 2) (e 3) hpos
  simpa [fieldBound, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, cantorGraph, SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef, cantor_graph] using h

#print axioms candidate_pra_fieldBound
#print axioms pair_lt_tagged
end PA195FreshBound
