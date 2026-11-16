module
public import M6PA.Theory
public import M6PA.Calibration.RelationalParameterClosure
public import M6PA.Calibration.RelationalSourceRewritingAtoms
@[expose] public section

/-! Literal specialization of the reusable first-parameter closure. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder

theorem subst_fixParameter (t : Semiterm language Nat 0) :
    (Rew.subst ![t]).comp (Rew.fix : Rew language Nat 0 Nat 1) = Rew.rewrite1 t := by
  apply Rew.ext
  · intro i
    exact Fin.elim0 i
  · intro i
    cases i <;> rfl

theorem openParameter_eq (p : Proposition language) (t : Semiterm language Nat 0) :
    Semiformula.rewAux (Rew.subst ![t]) (Semiformula.rewAux Rew.fix p) =
      Semiformula.rewAux (Rew.rewrite1 t) p := by
  simp only [←app_eq_rewAux,←TransitiveRewriting.comp_app,subst_fixParameter]

def specializeParameter {Γ : List ND.Form} (p : Proposition language)
    (t : Semiterm language Nat 0) (d : ND.Proof Γ (closeParameter p)) :
    ND.Proof Γ (Semiformula.rewAux (Rew.rewrite1 t) p) := by
  have h := ND.allElim (Semiformula.rewAux Rew.fix p) t d
  change ND.Proof Γ (Semiformula.rewAux (Rew.subst ![t]) (Semiformula.rewAux Rew.fix p)) at h
  simpa only [openParameter_eq] using h

#print axioms openParameter_eq
#print axioms specializeParameter
end M6.PA.RelationalSource

