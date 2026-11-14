import PA195FreshBound
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA195DecodedFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAModelIOpenPairing

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- The exact quotient-and-Cantor fields read by PA195's numeric decoder
are strictly below every positive code in arbitrary IOpen models. -/
theorem decoded_fields_lt (n : V) (hn : 0 < n) :
    first (n / 4) < n ∧ second (n / 4) < n := by
  have hq : n / 4 < n := div_lt_of_pos_of_one_lt hn (by simp)
  exact ⟨lt_of_le_of_lt (projections_spec (n / 4)).1 hq,
    lt_of_le_of_lt (projections_spec (n / 4)).2.1 hq⟩

noncomputable def decodedFieldBound : ArithmeticSemisentence 4 :=
  “n p a b. !divDef p n 4 → !PA195FreshBound.cantorGraph p a b →
    (0 < n → (a < n ∧ b < n))”

theorem candidate_pra_decodedFieldBound :
    PRA ⊢ Semiformula.lMap embedding (∀⁰* decodedFieldBound) := by
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
  have h (hp : e 1 = e 0 / 4) (hc : e 1 = cantor (e 2) (e 3))
      (hn : 0 < e 0) : e 2 < e 0 ∧ e 3 < e 0 := by
    have he : cantor (e 2) (e 3) = e 0 / 4 := hc.symm.trans hp
    have hn' := decoded_fields_lt (e 0) hn
    rw [← he, first_cantor, second_cantor] at hn'
    exact hn'
  simpa [decodedFieldBound, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.def_of_Eq_of_LT,
    Semiformula.val_operator_or, le_iff_eq_or_lt, PA195FreshBound.cantorGraph,
    SetTheory.BusyBeaver.ZFC.ArithmeticCantor.pairDef, cantor_graph, divDef, div_graph] using h

#print axioms candidate_pra_decodedFieldBound
#print axioms decoded_fields_lt
end PA195DecodedFields
