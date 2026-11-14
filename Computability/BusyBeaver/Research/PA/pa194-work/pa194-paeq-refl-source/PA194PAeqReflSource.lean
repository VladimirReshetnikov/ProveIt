import PA194PAeqTargetAxiom
import PA194PAeqFormulaCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmetic_refl_mem : Theory.Eq.refl ℒₒᵣ ∈ PeanoMinus :=
  PeanoMinus.equal _ Theory.eqAxiom.refl

theorem refl_translation : formulaCode (0:V) (⌜Theory.Eq.refl ℒₒᵣ⌝ : V) =
    (⌜PA194PAeq.reflexivity.univCl⌝ : V) := by
  have hclosed : PA194PAeq.reflexivity.freeVariables = ∅ := by decide
  simp only [Sentence.quote_def, Theory.Eq.refl, PA194PAeq.reflexivity,
    Semiformula.coe_univCl_eq_univCl']
  rw [Semiformula.univCl'_eq_self_of _ (by simpa [PA194PAeq.reflexivity] using hclosed)]
  change formulaCode 0 (^∀ ⌜(.rel Language.ORing.Rel.eq ![#0,#0] : ArithmeticSemiformula ℕ 1)⌝) =
    ^∀ ⌜(PA194PAeq.eq (#0) (#0) : Semiproposition PA194PAeq.language 1)⌝
  rw [formulaCode_all _ _ (Semiformula.quote_isSemiformula
    (.rel Language.ORing.Rel.eq ![#0,#0] : ArithmeticSemiformula ℕ 1)).isUFormula]
  simp only [PA194PAeq.eq, Semiformula.quote_rel]
  have hv : IsSemiformula ℒₒᵣ (↑(1:ℕ) : V)
      (^rel (↑(2:ℕ) : V) ⌜Language.ORing.Rel.eq⌝
        (SemitermVec.val fun i => (⌜(![#0,#0] : Fin 2 → SyntacticSemiterm ℒₒᵣ 1) i⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1))) := by
    simpa only [Semiformula.quote_rel] using
      (Semiformula.quote_isSemiformula (V := V)
        (.rel Language.ORing.Rel.eq ![#0,#0] : ArithmeticSemiformula ℕ 1))
  obtain ⟨hr, ht⟩ := IsSemiformula.rel.mp hv
  rw [formulaCode_rel _ _ _ _ hr ht.isUTerm]
  have hs : (⌜Language.ORing.Rel.eq⌝ : V) = 0 := by
    change ((0 : ℕ) : V) = 0
    simp
  simp [atomCode, equalityCode, hs, SemitermVec.val,
    Matrix.vecHead, Matrix.vecTail, termCode_bvar]
  change 0 = ((0 : ℕ) : V)
  simp

theorem target_reflexivity_mem :
    PA194PAeq.reflexivity.univCl ∈ PA194PAeq.targetFixedTheory := by
  change PA194PAeq.reflexivity.univCl ∈ PA194PAeq.targetFixedSentences
  apply List.mem_map.mpr
  exact ⟨PA194PAeq.reflexivity, by simp [PA194PAeq.fixedAxioms], rfl⟩

theorem translated_reflexivity_witness :
    Proof PA194PAeq.targetFixedTheory
      (Bootstrapping.axm {⌜PA194PAeq.reflexivity.univCl⌝}
        ⌜PA194PAeq.reflexivity.univCl⌝ : V)
      (formulaCode 0 (⌜Theory.Eq.refl ℒₒᵣ⌝ : V)) := by
  rw [refl_translation]
  exact PA194PAeq.target_axiom_witness PA194PAeq.targetFixedTheory _ target_reflexivity_mem

theorem translated_reflexivity_provable :
    Provable PA194PAeq.targetFixedTheory
      (formulaCode 0 (⌜Theory.Eq.refl ℒₒᵣ⌝ : V)) :=
  ⟨_, translated_reflexivity_witness⟩


#print axioms arithmetic_refl_mem
#print axioms refl_translation
#print axioms target_reflexivity_mem
#print axioms translated_reflexivity_witness
#print axioms translated_reflexivity_provable
end PA194PAeqTermBlueprint
