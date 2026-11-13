module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationLtIrrefl
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def mulOrderContext : List ND.Form := mulLawsContext ++
  (closedContext mulCommContext ++ [mulSucc,addZero,addSucc])
theorem mulOrderContext_closed (p : ND.Form) (hp : p ∈ mulOrderContext) : p.freeVariables = ∅ := by
  simp only [mulOrderContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | rfl | rfl | rfl
  · exact mulLawsContext_closed p hp
  · exact closedContext_closed mulCommContext p hp
  · simp [mulSucc,eq,add,mul,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
  · simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
  · simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
theorem mulOrderContext_mem_theory (p : ND.Form) (hp : p ∈ mulOrderContext) : p.univCl ∈ ordinaryPAeq := by
  simp only [mulOrderContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | rfl | rfl | rfl
  · exact mulLawsContext_mem_theory p hp
  · exact closedContext_mem_theory mulCommContext_mem_theory p hp
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩

def mulOrderWitness {Γ : List ND.Form} (incl : ∀ p,p ∈ mulOrderContext → p ∈ Γ)
    (a b c u v : GroundTerm) (hu : ND.Proof Γ (eq (add a (succ u)) b))
    (hv : ND.Proof Γ (eq (add zero (succ v)) c)) : ND.Proof Γ (less (mul a c) (mul b c)) := by
  let E := equalityContextPremises.weaken (Δ := Γ)
    (by intro p hp; apply incl; simp [mulOrderContext,mulLawsContext,addLawsContext,hp])
  let M := derivedMulLaws.weaken (Δ := Γ) (by intro p hp; apply incl; simp [mulOrderContext,hp])
  have comm (x y : GroundTerm) : ND.Proof Γ (eq (mul x y) (mul y x)) :=
    ND.weaken (mulCommInstance x y) (by intro p hp; apply incl; simp [mulOrderContext,hp])
  have mr : ND.Proof Γ mulSucc := ND.assumption (incl _ (by simp [mulOrderContext]))
  have az : ND.Proof Γ addZero := ND.assumption (incl _ (by simp [mulOrderContext]))
  have ar : ND.Proof Γ addSucc := ND.assumption (incl _ (by simp [mulOrderContext]))
  have hz : ND.Proof Γ (eq (add zero (succ v)) (succ v)) := by
    have h := ND.allElim _ (succ v) az
    convert h using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
  have hc := E.transitivityOf (E.symmetryOf hz) hv
  have h1 : ND.Proof Γ (eq (mul (succ u) c) (add c (mul u c))) := by
    have h := ND.allElim2 _ c u mr
    convert h using 1 <;> dsimp [mulSucc] <;> equalityInstanceSyntax
  have h2 := E.additionOf (E.symmetryOf hc) (E.reflexive (mul u c))
  have h3 : ND.Proof Γ (eq (add (succ v) (mul u c)) (succ (add v (mul u c)))) := by
    have h := ND.allElim2 _ v (mul u c) ar
    convert h using 1 <;> dsimp [addSucc] <;> equalityInstanceSyntax
  have positive := E.transitivityOf (E.transitivityOf h1 h2) h3
  have leftDistr : ND.Proof Γ (eq (mul (add a (succ u)) c)
      (add (mul a c) (mul (succ u) c))) :=
    E.transitivityOf (E.transitivityOf (comm (add a (succ u)) c) (M.distr c a (succ u)))
      (E.additionOf (comm c a) (comm c (succ u)))
  have h4 := E.additionOf (E.reflexive (mul a c)) (E.symmetryOf positive)
  have h5 := E.symmetryOf leftDistr
  have h6 := E.multiplicationOf hu (E.reflexive c)
  exact ND.lessIntro (mul a c) (mul b c) (add v (mul u c))
    (E.transitivityOf (E.transitivityOf h4 h5) h6)

def mulLtMulInstance (a b c : GroundTerm) : ND.Proof mulOrderContext
    (implies (.and (less a b) (less zero c)) (less (mul a c) (mul b c))) := by
  let Γ := mulOrderContext
  let p := Semiformula.and (less a b) (less zero c)
  let Δ := p :: Γ
  apply ND.impIntro
  have hp : ND.Proof Δ p := ND.assumption (by simp [Δ])
  have hab := ND.andLeft hp
  have hpos := ND.andRight hp
  apply ND.lessElim a b hab
  let a' := Rew.shift a
  let b' := Rew.shift b
  let c' := Rew.shift c
  let u : GroundTerm := .fvar 0
  let h := eq (add a' (succ u)) b'
  let Θ := h :: ND.shifted Δ
  have first : ND.Proof Θ h := ND.assumption (by simp [Θ])
  have second : ND.Proof Θ (less zero c') := by
    have d := ND.weaken (ND.shiftProof hpos) (fun q hq => List.mem_cons_of_mem h hq)
    simpa only [less_shift,rew_zero] using d
  rw [less_shift,rew_mul,rew_mul]
  change ND.Proof Θ (less (mul a' c') (mul b' c'))
  apply ND.lessElim zero c' second
  let a'' := Rew.shift a'
  let b'' := Rew.shift b'
  let c'' := Rew.shift c'
  let u' := Rew.shift u
  let v : GroundTerm := .fvar 0
  let k := eq (add zero (succ v)) c''
  let Ω := k :: ND.shifted Θ
  have incl : ∀ q,q ∈ Γ → q ∈ Ω := by
    intro q hq
    apply List.mem_cons_of_mem
    apply closed_members_shifted mulOrderContext_closed _ q hq
    intro r hr
    apply List.mem_cons_of_mem
    exact closed_members_shifted mulOrderContext_closed (fun r hr => List.mem_cons_of_mem _ hr) r hr
  have hu : ND.Proof Ω (eq (add a'' (succ u')) b'') := by
    have d := ND.weaken (ND.shiftProof first) (fun q hq => List.mem_cons_of_mem k hq)
    simpa only [h,eq_shift,rew_add,rew_succ] using d
  have hv : ND.Proof Ω k := ND.assumption (by simp [Ω])
  have d := mulOrderWitness incl a'' b'' c'' u' v hu hv
  simpa only [less_shift,rew_mul,rew_zero] using d

def foundationMulLtMulProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.mulLtMul) := by
  let Γ := mulOrderContext
  have hc := mulOrderContext_closed
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.mulLtMul)) := by
    apply ND.allIntro
    apply ND.allIntro
    apply ND.allIntro
    have h := mulLtMulInstance (.fvar 2) (.fvar 1) (.fvar 0)
    convert h using 1 <;> first
      | (change ND.shifted (ND.shifted (ND.shifted Γ)) = Γ;
          rw [shifted_closed Γ hc,shifted_closed Γ hc,shifted_closed Γ hc])
      | (change Semiformula.rewAux Rew.free
            (Semiformula.rewAux (Rew.q Rew.free)
              (Semiformula.rewAux (Rew.q Rew.free).q
                (Semiformula.rewAux Rew.emb.q.q.q
                  (implies (.and (less (.bvar 2) (.bvar 1)) (less zero (.bvar 0)))
                    (less (mul (.bvar 2) (.bvar 0)) (mul (.bvar 1) (.bvar 0))))))) = _;
          simp only [rew_implies_any,Semiformula.rewAux,less_rew,rew_mul,rew_zero]; simp [Rew.q]; rfl)
  have h := ND.parameterTheoryProof hp mulOrderContext_mem_theory
  simpa only [Semiformula.univCl_coe_sentence] using h

#print axioms mulLtMulInstance
#print axioms foundationMulLtMulProof
end M6.PA.Presentation
