module
public import M6PA.Theory
public import M6PA.Calibration.RelationalFormulaCongruence
@[expose] public section

/-! Cache a generic finite five-binder variable-specialization combinator before instantiating
large arithmetic trace formulas. No theory premise is added or removed. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder ND

def specializeFive {Γ : List Form} (p : Semiproposition language 5)
    (a b c d e : Nat) (h : ND.Proof Γ (∀¹ ∀¹ ∀¹ ∀¹ ∀¹ p)) :
    ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar e,.fvar d,.fvar c,.fvar b,.fvar a]) p) := by
  have out := allElim _ (.fvar e) (allElim _ (.fvar d) (allElim _ (.fvar c) (allElim _ (.fvar b) (allElim _ (.fvar a) h))))
  convert out using 1
  simp only [Rewriting.subst,app_eq_rewAux,Semiformula.rewAux]
  repeat' rw [rewrite_compose]
  apply congrArg (fun ω : Rew language Nat 5 Nat 0 => Semiformula.rewAux ω p)
  ext i <;> simp [Rew.comp_app]
  all_goals fin_cases i <;> rfl

#print axioms specializeFive
end M6.PA.RelationalSource
