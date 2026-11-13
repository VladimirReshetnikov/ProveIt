module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationOneLe
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def difference {ξ : Type} {n : Nat} (a b : Semiterm language ξ n) : Semiformula language ξ n :=
  .exs (.and (less (.bvar 0) (add (Rew.bShift b) (succ zero)))
    (eq (add (Rew.bShift a) (.bvar 0)) (Rew.bShift b)))

def ND.differenceIntro {Γ : List ND.Form} (a b w : GroundTerm)
    (hl : ND.Proof Γ (less w (add b (succ zero))))
    (he : ND.Proof Γ (eq (add a w) b)) : ND.Proof Γ (difference a b) := by
  apply ND.exsIntro _ w
  change ND.Proof Γ (Semiformula.rewAux (Rew.subst ![w]) _)
  have d := ND.andIntro hl he
  convert d using 1
  change Semiformula.and (Semiformula.rewAux (Rew.subst ![w]) _)
    (Semiformula.rewAux (Rew.subst ![w]) _) = _
  simp only [less_rew,eq_rew,rew_add,rew_succ,rew_zero,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero]
  rfl

theorem difference_rew {ξ ζ : Type} {n m : Nat} (ω : Rew language ξ n ζ m)
    (a b : Semiterm language ξ n) :
    Semiformula.rewAux ω (difference a b) = difference (ω a) (ω b) := by
  simp only [difference,Semiformula.rewAux,less_rew,eq_rew,rew_add,rew_succ,rew_zero,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero]
  rfl

theorem difference_shift (a b : GroundTerm) :
    (difference a b).shift = difference (Rew.shift a) (Rew.shift b) := difference_rew Rew.shift a b

def differenceContext : List ND.Form := addLawsContext ++
  (closedContext rightSuccContext ++ closedContext stepCertificateContext)
theorem differenceContext_closed (p : ND.Form) (hp : p ∈ differenceContext) : p.freeVariables = ∅ := by
  simp only [differenceContext,List.mem_append] at hp
  rcases hp with hp | hp | hp
  · exact addLawsContext_closed p hp
  · exact closedContext_closed rightSuccContext p hp
  · exact closedContext_closed stepCertificateContext p hp

theorem differenceContext_mem_theory (p : ND.Form) (hp : p ∈ differenceContext) : p.univCl ∈ ordinaryPAeq := by
  simp only [differenceContext,List.mem_append] at hp
  rcases hp with hp | hp | hp
  · exact addLawsContext_mem_theory p hp
  · exact closedContext_mem_theory (T := ordinaryPAeq)
      (fun q hq => ⟨q,rightSuccContext_is_PAeq q hq,rfl⟩) p hp
  · exact closedContext_mem_theory (T := ordinaryPAeq)
      (fun q hq => ⟨q,stepContext_is_PAeq q hq,rfl⟩) p hp

def addDifferenceInstance (a b : GroundTerm) : ND.Proof differenceContext
    (implies (less a b) (difference a b)) := by
  let Γ := differenceContext
  apply ND.impIntro
  let Δ := less a b :: Γ
  have hp : ND.Proof Δ (less a b) := ND.assumption (by simp [Δ])
  apply ND.lessElim a b hp
  let x := Rew.shift a
  let y := Rew.shift b
  let u : GroundTerm := .fvar 0
  let h := eq (add x (succ u)) y
  let Θ := h :: ND.shifted Δ
  have incl : ∀ p,p ∈ Γ → p ∈ Θ := by
    intro p hp
    apply List.mem_cons_of_mem
    exact closed_members_shifted differenceContext_closed (fun p hp => List.mem_cons_of_mem _ hp) p hp
  let E := equalityContextPremises.weaken (Δ := Θ)
    (by intro p hp; apply incl; simp [Γ,differenceContext,addLawsContext,hp])
  let A := derivedAddLaws.weaken (Δ := Θ)
    (by intro p hp; apply incl; simp [Γ,differenceContext,hp])
  have rs : ND.Proof Θ rightSuccFormula := ND.weaken rightSuccClosedCertificate
    (by intro p hp; apply incl; simp [Γ,differenceContext,hp])
  have ao : ND.Proof Θ (.all stepProperty) := ND.weaken (ND.replaceByClosures addOneSuccessorCertificate)
    (by intro p hp; apply incl; simp [Γ,differenceContext,hp])
  have h1 : ND.Proof Θ (eq (add (succ u) (succ x)) (succ (add (succ u) x))) := by
    have d := ND.allElim2 _ x (succ u) rs
    convert d using 1 <;> dsimp [rightSuccFormula] <;> equalityInstanceSyntax
  have h2 := ND.mp (A.comm (succ u) x) (E.successor (add (succ u) x) (add x (succ u)))
  have hw : ND.Proof Θ h := ND.assumption (by simp [Θ])
  have h3 := ND.mp hw (E.successor (add x (succ u)) y)
  have h4 : ND.Proof Θ (eq (add y (succ zero)) (succ y)) := by
    have d := ND.allElim _ y ao
    convert d using 1 <;> dsimp [stepProperty] <;> equalityInstanceSyntax
  have he := E.transitivityOf (E.transitivityOf (E.transitivityOf h1 h2) h3) (E.symmetryOf h4)
  have hl := ND.lessIntro (succ u) (add y (succ zero)) x he
  rw [difference_shift]
  exact ND.differenceIntro x y (succ u) hl hw

def foundationAddEqOfLtProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.addEqOfLt) := by
  let Γ := differenceContext
  have hc := differenceContext_closed
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.addEqOfLt)) := by
    apply ND.allIntro
    apply ND.allIntro
    have h := addDifferenceInstance (.fvar 1) (.fvar 0)
    convert h using 1 <;> first
      | (change ND.shifted (ND.shifted Γ) = Γ; rw [shifted_closed Γ hc,shifted_closed Γ hc])
      | (change Semiformula.rewAux Rew.free
            (Semiformula.rewAux Rew.free.q
              (Semiformula.rewAux Rew.emb.q.q
                (implies (less (.bvar 1) (.bvar 0)) (difference (.bvar 1) (.bvar 0))))) = _;
          simp only [rew_implies_any,less_rew,difference_rew]; simp [Rew.q])
  have h := ND.parameterTheoryProof hp differenceContext_mem_theory
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms addDifferenceInstance
#print axioms foundationAddEqOfLtProof
end M6.PA.Presentation
