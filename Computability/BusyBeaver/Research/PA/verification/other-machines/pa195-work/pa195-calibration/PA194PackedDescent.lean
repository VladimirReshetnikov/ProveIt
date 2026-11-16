import PA195DecodedFields

/-! Packed-index descent for a PA194 numeric occurrence fixpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PackedDescent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAModelIOpenPairing

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- The auxiliary Foundation-pair index decreases for either exact PA194
formula child when the formula code is positive. -/
theorem packed_children_lt (n v : V) (hn : 0 < n) :
    pair (first (n / 4)) v < pair n v ∧ pair (second (n / 4)) v < pair n v := by
  have hc := PA195DecodedFields.decoded_fields_lt n hn
  exact ⟨pair_lt_pair_left hc.1 v, pair_lt_pair_left hc.2 v⟩

abbrev seedPairGraph := LO.FirstOrder.Arithmetic.pairDef

noncomputable def packedChildBody : ArithmeticSemisentence 8 :=
  “n v q a b x y z. !divDef q n 4 → !PA195FreshBound.cantorGraph q a b →
    !seedPairGraph x n v → !seedPairGraph y a v → !seedPairGraph z b v →
    (0 < n → (y < x ∧ z < x))”

theorem candidate_pra_packedChildDescent :
    PRA ⊢ Semiformula.lMap embedding (∀⁰* packedChildBody) := by
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
  have h (hq : e 2 = e 0 / 4) (hc : e 2 = cantor (e 3) (e 4))
      (hx : e 5 = pair (e 0) (e 1)) (hy : e 6 = pair (e 3) (e 1))
      (hz : e 7 = pair (e 4) (e 1)) (hn : 0 < e 0) :
      e 6 < e 5 ∧ e 7 < e 5 := by
    have he : cantor (e 3) (e 4) = e 0 / 4 := hc.symm.trans hq
    have ht := packed_children_lt (e 0) (e 1) hn
    rw [← he, first_cantor, second_cantor, ← hx, ← hy, ← hz] at ht
    exact ht
  simpa [packedChildBody, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.def_of_Eq_of_LT,
    Semiformula.val_operator_or, le_iff_eq_or_lt, PA195FreshBound.cantorGraph,
    SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef, cantor_graph,
    seedPairGraph, LO.FirstOrder.Arithmetic.pairDef, pair_graph, divDef, div_graph] using h

#print axioms candidate_pra_packedChildDescent
#print axioms packed_children_lt
end PA194PackedDescent
