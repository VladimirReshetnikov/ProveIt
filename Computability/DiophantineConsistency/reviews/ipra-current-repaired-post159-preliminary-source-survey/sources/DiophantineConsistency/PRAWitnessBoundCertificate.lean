import DiophantineConsistency.PRAWitnessCalculus
import DiophantineConsistency.PRAStrictConReverse
import DiophantineConsistency.PRAModelIOpenPairing

/-! # From semantic witness bounds to the fixed PRA certificate

This is the final generic bridge from a witness bound valid in every
candidate-PRA model to the proof-existence certificate required by
`PRAStrictConReverse`. It does not assert such a bound for ZFC. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessBoundCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAStrictConReverse PRANoZeroUnary

local instance {M : Type} [Structure language M] : Zero M :=
  ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {M : Type} [Structure language M] : One M :=
  ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {M : Type} [Structure language M] : Add M :=
  ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {M : Type} [Structure language M] : Mul M :=
  ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {M : Type} [Structure language M] : LT M :=
  ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem certificate_of_witness_bounds (π : ArithmeticSentence)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], WB M π) : BoundCertificate π := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [Semantics.Imp.models_imply, models_iff, Semiformula.eval_lMap,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_ex]
  rw [PRAModelIOpenPairing.reduct_eq_standard]
  intro hp
  obtain ⟨w, hw⟩ := exists_bound (h M) ![] hp
  exact ⟨w, by simpa using hw⟩

/-- The exact no-zero equivalence follows from an IΣ₁ equivalence and
witness bounds for the fixed refutation sentence in all candidate-PRA models.
Both are explicit hypotheses; this does not prove the ZFC instance. -/
theorem comparison_of_witness_bounds (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (π : ArithmeticSentence) (hπ : Hierarchy 𝚺 1 π)
    (heq : 𝗜𝚺₁ ⊢ (noZero n a b 🡘 ∼π))
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], WB M π) :
    PRA ⊢ (Semiformula.lMap embedding (noZero n a b) 🡘 Semiformula.lMap embedding (∼π)) :=
  comparison_if_bound n a b π hπ heq (certificate_of_witness_bounds π h)

end DiophantineConsistency.PRAWitnessBoundCertificate
