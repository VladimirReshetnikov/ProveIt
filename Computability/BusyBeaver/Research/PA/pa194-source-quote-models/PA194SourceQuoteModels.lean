import PA194SourceSearchCoding
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
namespace PA194SourceQuoteModels
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping M6.PA.RelationalSource
open PA194SourceSearchCoding
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

instance relationDecidableEq (k : Nat) : DecidableEq (Relation k) := by
  intro a b
  cases a <;> cases b
  all_goals first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance sourceLanguageDecidable : language.DecidableEq :=
  ⟨fun _ => inferInstanceAs (DecidableEq Empty), relationDecidableEq⟩

variable (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory language) [T.Δ₁]

noncomputable def quoteDerivation {Γ : List (Proposition language)} (d : Derivation Γ) :
    T.internalize V ⊢!ᵈᵉʳ (⌜Γ.toFinset⌝ : Bootstrapping.Sequent V language) :=
  (d.toDerivation2 T).typedQuote V

theorem quoteDerivation_coe {Γ : List (Proposition language)} (d : Derivation Γ) :
    ((quoteDerivation Nat T d).val : V) = (quoteDerivation V T d).val := by
  exact Derivation2.coe_typedQuote_val_eq (V := V) (d.toDerivation2 T)

theorem fixedStandardCode {Γ : List (Proposition language)} (d : Derivation Γ) :
    ∃ code : Nat, ∀ (W : Type) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      ∃ out : T.internalize W ⊢!ᵈᵉʳ (⌜Γ.toFinset⌝ : Bootstrapping.Sequent W language),
        out.val = (code : W) := by
  refine ⟨(quoteDerivation Nat T d).val, fun W _ _ => ⟨quoteDerivation W T d, ?_⟩⟩
  exact (quoteDerivation_coe W T d).symm

#print axioms fixedStandardCode
#print axioms quoteDerivation
#print axioms quoteDerivation_coe
end PA194SourceQuoteModels
