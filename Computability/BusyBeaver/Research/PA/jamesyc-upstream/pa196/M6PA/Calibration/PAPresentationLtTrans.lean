module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationOrderTransport
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def orderLawContext : List ND.Form := addLawsContext ++ [addSucc]
theorem orderLawContext_closed (p : ND.Form) (hp : p ∈ orderLawContext) : p.freeVariables = ∅ := by
  simp only [orderLawContext,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact addLawsContext_closed p hp
  · simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
theorem orderLawContext_mem_theory (p : ND.Form) (hp : p ∈ orderLawContext) : p.univCl ∈ ordinaryPAeq := by
  simp only [orderLawContext,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact addLawsContext_mem_theory p hp
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩

def orderTransWitness {Γ : List ND.Form} (E : EqualityPremises Γ) (A : AddLaws Γ)
    (ar : ND.Proof Γ addSucc) (a b c u v : GroundTerm)
    (hu : ND.Proof Γ (eq (add a (succ u)) b))
    (hv : ND.Proof Γ (eq (add b (succ v)) c)) : ND.Proof Γ (less a c) := by
  have recu : ND.Proof Γ (eq (add (succ u) (succ v)) (succ (add u (succ v)))) := by
    have h := ND.allElim2 _ u (succ v) ar
    convert h using 1 <;> dsimp [addSucc] <;> equalityInstanceSyntax
  have h1 := E.additionOf (E.reflexive a) (E.symmetryOf recu)
  have h2 := E.symmetryOf (A.assoc a (succ u) (succ v))
  have h3 := E.additionOf hu (E.reflexive (succ v))
  exact ND.lessIntro a c (add u (succ v))
    (E.transitivityOf (E.transitivityOf (E.transitivityOf h1 h2) h3) hv)

def ltTransInstance (a b c : GroundTerm) : ND.Proof orderLawContext
    (implies (.and (less a b) (less b c)) (less a c)) := by
  let Γ := orderLawContext
  let p := Semiformula.and (less a b) (less b c)
  let Δ := p :: Γ
  apply ND.impIntro
  have hp : ND.Proof Δ p := ND.assumption (by simp [Δ])
  have hab := ND.andLeft hp
  have hbc := ND.andRight hp
  apply ND.lessElim a b hab
  let a' := Rew.shift a
  let b' := Rew.shift b
  let c' := Rew.shift c
  let u : GroundTerm := .fvar 0
  let h := eq (add a' (succ u)) b'
  let Θ := h :: ND.shifted Δ
  have first : ND.Proof Θ h := ND.assumption (by simp [Θ])
  have second : ND.Proof Θ (less b' c') := by
    have d := ND.weaken (ND.shiftProof hbc) (fun q hq => List.mem_cons_of_mem h hq)
    simpa only [less_shift] using d
  rw [less_shift]
  change ND.Proof Θ (less a' c')
  apply ND.lessElim b' c' second
  let a'' := Rew.shift a'
  let b'' := Rew.shift b'
  let c'' := Rew.shift c'
  let u' := Rew.shift u
  let v : GroundTerm := .fvar 0
  let k := eq (add b'' (succ v)) c''
  let Ω := k :: ND.shifted Θ
  have incl : ∀ q,q ∈ Γ → q ∈ Ω := by
    intro q hq
    apply List.mem_cons_of_mem
    apply closed_members_shifted orderLawContext_closed _ q hq
    intro r hr
    apply List.mem_cons_of_mem
    exact closed_members_shifted orderLawContext_closed (fun r hr => List.mem_cons_of_mem _ hr) r hr
  let E := equalityContextPremises.weaken (Δ := Ω)
    (by intro q hq; apply incl; simp [Γ,orderLawContext,addLawsContext,hq])
  let A := derivedAddLaws.weaken (Δ := Ω)
    (by intro q hq; apply incl; simp [Γ,orderLawContext,hq])
  have ar : ND.Proof Ω addSucc := ND.assumption (incl _ (by simp [Γ,orderLawContext]))
  have hu : ND.Proof Ω (eq (add a'' (succ u')) b'') := by
    have d := ND.weaken (ND.shiftProof first) (fun q hq => List.mem_cons_of_mem k hq)
    simpa only [h,eq_shift,rew_add,rew_succ] using d
  have hv : ND.Proof Ω k := ND.assumption (by simp [Ω])
  have d := orderTransWitness E A ar a'' b'' c'' u' v hu hv
  simpa only [less_shift] using d

def foundationLtTransProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.ltTrans) := by
  let Γ := orderLawContext
  have hc := orderLawContext_closed
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.ltTrans)) := by
    apply ND.allIntro
    apply ND.allIntro
    apply ND.allIntro
    have h := ltTransInstance (.fvar 2) (.fvar 1) (.fvar 0)
    convert h using 1 <;> first
      | (change ND.shifted (ND.shifted (ND.shifted Γ)) = Γ;
          rw [shifted_closed Γ hc,shifted_closed Γ hc,shifted_closed Γ hc])
      | (change Semiformula.rewAux Rew.free
            (Semiformula.rewAux (Rew.q Rew.free)
              (Semiformula.rewAux (Rew.q Rew.free).q
                (Semiformula.rewAux Rew.emb.q.q.q
                  (implies (.and (less (.bvar 2) (.bvar 1)) (less (.bvar 1) (.bvar 0)))
                    (less (.bvar 2) (.bvar 0)))))) = _;
          simp only [rew_implies_any,Semiformula.rewAux,less_rew]; simp [Rew.q]; rfl)
  have h := ND.parameterTheoryProof hp orderLawContext_mem_theory
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms ltTransInstance
#print axioms foundationLtTransProof
end M6.PA.Presentation
