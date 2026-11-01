import DiophantineConsistency.StrictPiTwoBridge
import DiophantineConsistency.PRAModelIOpenPairing
set_option autoImplicit false
namespace DiophantineConsistency.PRAConBForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  StrictPiTwoBridge StrictSigmaOneInduction
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem model_forward (π : ArithmeticSentence)
    (h : M↓[language] ⊧ Semiformula.lMap embedding (∼π)) :
    M↓[language] ⊧ Semiformula.lMap embedding (conB π) := by
  simp only [models_iff] at h ⊢
  rw [Semiformula.eval_lMap] at h ⊢
  rw [reduct_eq_standard] at h ⊢
  have hn : ¬ π.Evalb (M := M) ![] := by simpa using h
  simp only [conB, Semiformula.eval_all, LogicalConnective.HomClass.map_neg]
  intro w hw
  have hv : (Fin.snoc (![] : Fin 0 → M) w : Fin 1 → M) = ![w] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  apply hn
  exact eval_bnd_imp π ![] w Empty.elim (by simpa only [hv] using hw)
end models

theorem PRA_proves_forward (π : ArithmeticSentence) :
    PRA ⊢ (Semiformula.lMap embedding (∼π) 🡒 Semiformula.lMap embedding (conB π)) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [Semantics.Imp.models_imply]
  exact model_forward π
/-- A candidate-PRA equivalence with the strict surrogate implies the literal
negative sentence entails the other side. This does not prove the converse. -/
theorem PRA_proves_literal_direction (π σ : ArithmeticSentence)
    (hstrict : PRA ⊢ (Semiformula.lMap embedding σ 🡘 Semiformula.lMap embedding (conB π))) :
    PRA ⊢ (Semiformula.lMap embedding (∼π) 🡒 Semiformula.lMap embedding σ) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  have hs := models_of_provable hM hstrict
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hs ⊢
  intro h
  exact hs.2 (model_forward π h)
end DiophantineConsistency.PRAConBForward
