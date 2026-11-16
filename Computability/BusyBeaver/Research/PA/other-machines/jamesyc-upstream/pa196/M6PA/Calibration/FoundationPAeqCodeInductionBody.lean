module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeDerivation
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! Literal successor-based induction body for the existing target theory.
This does not identify arithmetic addition-by-one with successor. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def paeqSubstCode {k : Nat} (t : SyntacticSemiterm Presentation.language k) : Nat :=
  Matrix.vecToNat fun i => Encodable.encode (![t] i)
theorem paeqSubstCode_eq {k : Nat} (t : SyntacticSemiterm Presentation.language k) :
    paeqSubstCode t=SemitermVec.val (![⌜t⌝] : SemitermVec Nat Presentation.language 1 k) := by
  rw [paeqSubstCode,←natCast_nat (Matrix.vecToNat _),←Semiterm.quote_eq_encode' (V:=Nat) ![t]]
  congr 1; funext i; simp [Matrix.cons_val_fin_one]

noncomputable def targetIndBody (k : V) : V :=
  imp Presentation.language (subst Presentation.language ↑(paeqSubstCode (Presentation.zero : SyntacticTerm Presentation.language)) k)
    (imp Presentation.language
      (qqAll (imp Presentation.language k
        (subst Presentation.language ↑(paeqSubstCode (Presentation.succ (.bvar 0) : SyntacticSemiterm Presentation.language 1)) k)))
      (qqAll k))
theorem le_targetIndBody (k : V) : k≤targetIndBody k :=
  (le_qqAll _).trans (lt_or_right _ _ |>.trans (lt_or_right _ _)).le

theorem targetIndBody_quote (p : Semiproposition Presentation.language 1) :
    targetIndBody (⌜p⌝ : Nat)=(⌜Presentation.inductionFormula p⌝ : Nat) := by
  have he : (⌜Presentation.inductionFormula p⌝ : Bootstrapping.Semiformula Nat Presentation.language 0)=
      ⌜p ⇜ ![(Presentation.zero : SyntacticTerm Presentation.language)]⌝ 🡒
      ((∀¹ (⌜p⌝ 🡒 ⌜p ⇜ ![(Presentation.succ (.bvar 0) : SyntacticSemiterm Presentation.language 1)]⌝)) 🡒 ∀¹⌜p⌝) := by
    change (⌜(p ⇜ ![(Presentation.zero : SyntacticTerm Presentation.language)]) 🡒
      ((∀¹ (p 🡒 (p ⇜ ![(Presentation.succ (.bvar 0) : SyntacticSemiterm Presentation.language 1)]))) 🡒 ∀¹ p)⌝ : Bootstrapping.Semiformula Nat Presentation.language 0)=_
    simp
  change _=(⌜Presentation.inductionFormula p⌝ : Bootstrapping.Semiformula Nat Presentation.language 0).val
  rw [he]
  simp [targetIndBody,paeqSubstCode_eq,Matrix.constant_eq_singleton]
  rfl

noncomputable def targetIndBodyGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “out k. ∃ a, !(substsGraph Presentation.language) a ↑(paeqSubstCode (Presentation.zero : SyntacticTerm Presentation.language)) k ∧
    ∃ s, !(substsGraph Presentation.language) s ↑(paeqSubstCode (Presentation.succ (.bvar 0) : SyntacticSemiterm Presentation.language 1)) k ∧
    ∃ i, !(impGraph Presentation.language) i k s ∧ ∃ ai, !qqAllDef ai i ∧
    ∃ ak, !qqAllDef ak k ∧ ∃ j, !(impGraph Presentation.language) j ai ak ∧
    !(impGraph Presentation.language) out a j”
instance targetIndBody_defined : 𝚺ᴬ₁-Function₁ (targetIndBody : V→V) via targetIndBodyGraph :=
  .mk fun v=>by simp [targetIndBodyGraph,numeral_eq_natCast,targetIndBody]
instance targetIndBody_definable : 𝚺ᴬ₁-Function₁ (targetIndBody : V→V) := targetIndBody_defined.to_definable

#print axioms paeqSubstCode_eq
#print axioms le_targetIndBody
#print axioms targetIndBody_quote
#print axioms targetIndBody_defined
end M6.PA.FoundationPAeqCode

