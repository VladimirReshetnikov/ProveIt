module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationTrichotomyStep
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def triProperty : Semiproposition language 1 := triAll (.bvar 0)
def triContext : List ND.Form := triBaseContext ++ [inductionFormula triProperty]

def triCertificate : ND.Proof triContext (.all triProperty) := by
  let Γ := triContext
  have incl : ∀ p,p ∈ triBaseContext → p ∈ Γ := by intro p hp; simp [Γ,triContext,hp]
  have ind : ND.Proof Γ (inductionFormula triProperty) := ND.assumption (by simp [Γ,triContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) triProperty) := by
    rw [triProperty,triAll_rew,Rew.subst_bvar]
    change ND.Proof Γ (triAll zero)
    apply ND.allIntro
    have hp : ND.Proof (ND.shifted Γ) (tri zero (.fvar 0)) :=
      ND.weaken (zeroTriInstance (.fvar 0)) (by
        intro p hp
        apply closed_members_shifted triBaseContext_closed incl
        simp [triBaseContext,hp])
    change ND.Proof (ND.shifted Γ) (Semiformula.rewAux Rew.free (tri (Rew.bShift zero) (.bvar 0)))
    simpa only [tri_rew,Rew.free_bShift_app,rew_zero,Rew.free_bvar_last_zero] using hp
  have step : ND.Proof Γ (.all (inductionStep triProperty (succ (.bvar 0)))) := by
    apply ND.allIntro
    let x : GroundTerm := .fvar 0
    have hs : ND.Proof (ND.shifted Γ) (implies (triAll x) (triAll (succ x))) := by
      apply ND.impIntro
      let Δ := triAll x :: ND.shifted Γ
      have hi : ND.Proof Δ (triAll x) := ND.assumption (by simp [Δ])
      exact triSuccessorStep (Γ := Δ)
        (fun p hp => List.mem_cons_of_mem _ (closed_members_shifted triBaseContext_closed incl p hp)) x hi
    rw [free_inductionStep]
    convert hs using 1
    change implies (Semiformula.rewAux Rew.free (triAll (.bvar 0)))
      (Semiformula.rewAux (Rew.subst ![Rew.free (succ (.bvar 0))])
        (Semiformula.rewAux Rew.shift (triAll (.bvar 0)))) = _
    simp [triAll_rew,rew_succ,Rew.shift_bvar,Rew.subst_bvar,x]
  exact ND.mp step (ND.mp base ind)

theorem triContext_mem_theory (p : ND.Form) (hp : p ∈ triContext) : p.univCl ∈ ordinaryPAeq := by
  simp only [triContext,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact triBaseContext_mem_theory p hp
  · exact ⟨inductionFormula triProperty,.induction triProperty,rfl⟩

def foundationLtTriProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.ltTri) := by
  have d := ND.parameterTheoryProof triCertificate (T := ordinaryPAeq) triContext_mem_theory
  have he : formula Arithmetic.PeanoMinus.Axiom.ltTri = (Semiformula.all triProperty).univCl := by
    apply (Semiformula.coe_inj _ _).mp
    rw [Semiformula.coe_univCl_eq_univCl']
    rw [Semiformula.univCl'_eq_self_of _ (by
      simp [triProperty,triAll,tri,less,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])]
    change Semiformula.rewAux Rew.emb (formula Arithmetic.PeanoMinus.Axiom.ltTri) = _
    rw [←formula_emb]
    rfl
  rw [he]
  exact d

#print axioms triCertificate
#print axioms foundationLtTriProof
end M6.PA.Presentation

