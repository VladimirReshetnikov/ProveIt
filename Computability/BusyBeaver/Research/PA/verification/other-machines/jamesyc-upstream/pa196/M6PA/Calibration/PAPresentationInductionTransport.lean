module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationFormulaCongruence
public import M6PA.Calibration.PAPresentationInductionImage
@[expose] public section

/-! Uniform constructive replacement of additive induction by primitive
successor induction. The allowed finite arithmetic context is explicit. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem rew_implies {n m : Nat} (ω : Rew language Nat n Nat m)
    (p q : Semiproposition language n) :
    Semiformula.rewAux ω (implies p q) =
      implies (Semiformula.rewAux ω p) (Semiformula.rewAux ω q) := by
  exact congrArg (fun r : Semiproposition language m => Semiformula.or r (Semiformula.rewAux ω q))
    (Semiformula.rewAux_neg ω p)

theorem free_substitution (p : Semiproposition language 1) (t : Semiterm language Nat 1) :
    (Semiformula.rewAux (Rew.subst ![t]) p).free =
      Semiformula.rewAux (Rew.subst ![Rew.free t]) p.shift := by
  change Semiformula.rewAux Rew.free (Semiformula.rewAux (Rew.subst ![t]) p) =
    Semiformula.rewAux (Rew.subst ![Rew.free t]) (Semiformula.rewAux Rew.shift p)
  rw [rewrite_compose,rewrite_compose,Rew.free_comp_subst_eq_subst_comp_shift]
  have hv : Rew.free ∘ (![t] : Fin 1 → Semiterm language Nat 1) = ![Rew.free t] := by
    funext i; fin_cases i; rfl
  rw [hv]

def inductionStep (p : Semiproposition language 1) (t : Semiterm language Nat 1) :
    Semiproposition language 1 := implies p (Semiformula.rewAux (Rew.subst ![t]) p)

theorem free_inductionStep (p : Semiproposition language 1) (t : Semiterm language Nat 1) :
    (inductionStep p t).free =
      implies p.free (Semiformula.rewAux (Rew.subst ![Rew.free t]) p.shift) := by
  change Semiformula.rewAux Rew.free (implies p (Semiformula.rewAux (Rew.subst ![t]) p)) = _
  rw [rew_implies]
  change implies p.free (Semiformula.rewAux (Rew.subst ![t]) p).free = _
  rw [free_substitution]

def EqualityPremises.inductionTransport {Γ : List ND.Form} (E : EqualityPremises Γ)
    (p : Semiproposition language 1)
    (ha : ND.Proof Γ (.all stepProperty)) (hi : ND.Proof Γ (inductionFormula p)) :
    ND.Proof Γ (additiveInductionFormula p) := by
  apply ND.impIntro
  apply ND.impIntro
  let base : ND.Form := Semiformula.rewAux (Rew.subst ![zero]) p
  let addStep : ND.Form := Semiformula.all (inductionStep p (Presentation.add (.bvar 0) (Presentation.succ zero)))
  let Δ := addStep :: base :: Γ
  have inc : ∀ q, q ∈ Γ → q ∈ Δ := fun q hq => by simp [Δ,hq]
  have hbase : ND.Proof Δ base := ND.assumption (by simp [Δ])
  have hstep : ND.Proof Δ addStep := ND.assumption (by simp [Δ])
  let EΔ := E.weaken inc
  have hs : ND.Proof Δ (.all (inductionStep p (Presentation.succ (.bvar 0)))) := by
    apply ND.allIntro
    have hadd : ND.Proof (ND.shifted Δ) (inductionStep p (Presentation.add (.bvar 0) (Presentation.succ zero))).free := by
      have hd : ND.Proof (ND.shifted Δ) (.all (inductionStep p (Presentation.add (.bvar 0) (Presentation.succ zero))).shift) :=
        (ND.shiftProof hstep).cast (congrArg (fun q : ND.Form => ND.negatives (ND.shifted Δ) + ⦃q⦄)
          (presentation_shift_all _))
      exact (ND.allElim _ (.fvar 0) hd).cast (by rw [open_shifted])
    have hclosed : (Semiformula.all stepProperty).freeVariables = ∅ := by
      simp [stepProperty,eq,Presentation.add,Presentation.succ,zero,Semiformula.freeVariables,
        Semiterm.freeVariables,Fin.univ_succ]
    have heq : ND.Proof (ND.shifted Δ)
        (eq (Presentation.add (.fvar 0) (Presentation.succ zero)) (Presentation.succ (.fvar 0))) := by
      have hd := ND.allElim _ (.fvar 0) (ND.shiftClosed (ND.weaken ha inc) hclosed)
      convert hd using 1 <;> dsimp [stepProperty] <;> equalityInstanceSyntax
    have hadd' : ND.Proof (ND.shifted Δ)
        (implies p.free (Semiformula.rewAux (Rew.subst ![Presentation.add (.fvar 0) (Presentation.succ zero)]) p.shift)) :=
      hadd.cast (by simp only [free_inductionStep,rew_add,rew_succ,rew_zero,Rew.free_bvar_last_zero])
    have hout : ND.Proof (ND.shifted Δ)
        (implies p.free (Semiformula.rewAux (Rew.subst ![Presentation.succ (.fvar 0)]) p.shift)) := by
      apply ND.impIntro
      have up : ∀ q, q ∈ ND.shifted Δ → q ∈ p.free :: ND.shifted Δ :=
        fun q hq => List.mem_cons_of_mem _ hq
      have hp := ND.mp (ND.assumption (Γ := p.free :: ND.shifted Δ) (by simp))
        (ND.weaken hadd' up)
      exact (EΔ.shifted.weaken up).substituteOne p.shift _ _ (ND.weaken heq up) hp
    exact hout.cast (by simp only [free_inductionStep,rew_succ,Rew.free_bvar_last_zero])
  exact ND.mp hs (ND.mp hbase (ND.weaken hi inc))

def inductionContext (p : Semiproposition language 1) : List ND.Form :=
  equalityContext ++ (stepCertificateContext ++ [inductionFormula p])

def inductionTemplate (p : Semiproposition language 1) :
    ND.Proof (inductionContext p) (additiveInductionFormula p) :=
  (equalityContextPremises.weaken (by intro q hq; simp [inductionContext,hq])).inductionTransport p
    (ND.weaken addOneSuccessorCertificate (by intro q hq; simp [inductionContext,hq]))
    (ND.assumption (by simp [inductionContext]))

theorem inductionContext_is_PAeq (p : Semiproposition language 1) (q : ND.Form)
    (hq : q ∈ inductionContext p) : PAeqAxiom q := by
  simp only [inductionContext,List.mem_append,List.mem_singleton] at hq
  rcases hq with hq | hq | rfl
  · exact equalityContext_is_PAeq q hq
  · exact stepContext_is_PAeq q hq
  · exact PAeqAxiom.induction p

#print axioms inductionTemplate

#print axioms EqualityPremises.inductionTransport
end M6.PA.Presentation
