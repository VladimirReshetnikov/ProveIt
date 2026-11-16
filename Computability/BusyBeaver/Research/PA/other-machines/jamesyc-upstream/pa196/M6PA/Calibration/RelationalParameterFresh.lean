module
public import M6PA.Theory
public import M6PA.Calibration.RelationalParameterSpecialization
public import M6PA.Calibration.RelationalSourceAdjunctionLogic
@[expose] public section

/-! Opening a closed parameter at the actual fresh eigenvariable, while the
entire surrounding context is shifted. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder

def freshParameter {Γ : List ND.Form} (p : Proposition language)
    (d : ND.Proof Γ (closeParameter p)) :
    ND.Proof (ND.shifted Γ) p := by
  have hs : ND.Proof (ND.shifted Γ)
      (∀¹ (Semiformula.shift (Semiformula.rewAux Rew.fix p))) := by
    have h := ND.shiftProof d
    change ND.Proof (ND.shifted Γ) (Semiformula.rewAux Rew.shift
      (.all (Semiformula.rewAux Rew.fix p))) at h
    change ND.Proof (ND.shifted Γ) (∀¹ Semiformula.rewAux Rew.shift
      (Semiformula.rewAux Rew.fix p))
    simpa only [Semiformula.rewAux,Rew.q_shift] using h
  have h := ND.allElim (Semiformula.shift (Semiformula.rewAux Rew.fix p)) (.fvar 0) hs
  change ND.Proof (ND.shifted Γ) ((Rewriting.shift (Rewriting.fix p))/[.fvar 0]) at h
  simpa only [LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free,
    LawfulSyntacticRewriting.free_fix] using h

#print axioms freshParameter
end M6.PA.RelationalSource

