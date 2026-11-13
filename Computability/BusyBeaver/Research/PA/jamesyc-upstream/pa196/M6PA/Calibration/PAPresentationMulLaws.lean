module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationDistributivity
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

structure MulLaws (Γ : List ND.Form) where
  zero : ∀ a : GroundTerm, ND.Proof Γ (eq (mul a Presentation.zero) Presentation.zero)
  one : ∀ a : GroundTerm, ND.Proof Γ (eq (mul a (succ Presentation.zero)) a)
  distr : ∀ a b c : GroundTerm, ND.Proof Γ
    (eq (mul a (add b c)) (add (mul a b) (mul a c)))
  rightSucc : ∀ a b : GroundTerm, ND.Proof Γ
    (eq (mul a (succ b)) (add a (mul a b)))

namespace MulLaws
def weaken {Γ Δ : List ND.Form} (M : MulLaws Γ) (h : ∀ p,p ∈ Γ → p ∈ Δ) : MulLaws Δ where
  zero a := ND.weaken (M.zero a) h
  one a := ND.weaken (M.one a) h
  distr a b c := ND.weaken (M.distr a b c) h
  rightSucc a b := ND.weaken (M.rightSucc a b) h
end MulLaws

def mulLawsContext : List ND.Form := addLawsContext ++
  (closedContext mulZeroContext ++ (closedContext mulOneContext ++
    (closedContext distrContext ++ [addZero,addSucc])))

def derivedMulLaws : MulLaws mulLawsContext := by
  let Γ := mulLawsContext
  let E := equalityContextPremises.weaken (Δ := Γ)
    (by intro q h; simp [Γ,mulLawsContext,addLawsContext,h])
  have mz (a : GroundTerm) : ND.Proof Γ (eq (mul a zero) zero) := by
    have h := ND.allElim _ a (ND.replaceByClosures mulZeroCertificate)
    have hp : ND.Proof (closedContext mulZeroContext) (eq (mul a zero) zero) := by
      convert h using 1 <;> dsimp [mulZeroProperty] <;> equalityInstanceSyntax
    exact ND.weaken hp (by intro p hp; simp [Γ,mulLawsContext,hp])
  have mo (a : GroundTerm) : ND.Proof Γ (eq (mul a (succ zero)) a) := by
    have h := ND.allElim _ a (ND.replaceByClosures mulOneCertificate)
    have hp : ND.Proof (closedContext mulOneContext) (eq (mul a (succ zero)) a) := by
      convert h using 1 <;> dsimp [mulOneProperty] <;> equalityInstanceSyntax
    exact ND.weaken hp (by intro p hp; simp [Γ,mulLawsContext,hp])
  have md (a b c : GroundTerm) : ND.Proof Γ
      (eq (mul a (add b c)) (add (mul a b) (mul a c))) := by
    have d := ND.closeIter (closedContext_closed distrContext)
      (ND.replaceByClosures distrCertificate) 2
    have h := ND.allElim3 _ a b c d
    have hp : ND.Proof (closedContext distrContext)
        (eq (mul a (add b c)) (add (mul a b) (mul a c))) := by
      convert h using 1 <;> dsimp [closureIter,distrProperty] <;> equalityInstanceSyntax
    exact ND.weaken hp (by intro p hp; simp [Γ,mulLawsContext,hp])
  refine ⟨mz,mo,md,?_⟩
  intro a b
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,mulLawsContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,mulLawsContext])
  have h0 : ND.Proof Γ (eq (add zero b) b) := by
    have h := ND.allElim _ b az
    convert h using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
  have h1 : ND.Proof Γ (eq (add (succ zero) b) (succ (add zero b))) := by
    have h := ND.allElim2 _ zero b ar
    convert h using 1 <;> dsimp [addSucc] <;> equalityInstanceSyntax
  have h2 := ND.mp h0 (E.successor (add zero b) b)
  have hs := E.transitivityOf h1 h2
  have h3 := E.multiplicationOf (E.reflexive a) (E.symmetryOf hs)
  have h4 := E.additionOf (mo a) (E.reflexive (mul a b))
  exact E.transitivityOf (E.transitivityOf h3 (md a (succ zero) b)) h4

theorem mulLawsContext_mem_theory (p : ND.Form) (hp : p ∈ mulLawsContext) :
    p.univCl ∈ ordinaryPAeq := by
  simp only [mulLawsContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | hp | hp | rfl | rfl
  · exact addLawsContext_mem_theory p hp
  · exact closedContext_mem_theory (T := ordinaryPAeq)
      (fun q hq => ⟨q,mulZeroContext_is_PAeq q hq,rfl⟩) p hp
  · exact closedContext_mem_theory (T := ordinaryPAeq)
      (fun q hq => ⟨q,mulOneContext_is_PAeq q hq,rfl⟩) p hp
  · exact closedContext_mem_theory distrContext_mem_theory p hp
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩

theorem mulLawsContext_closed (p : ND.Form) (hp : p ∈ mulLawsContext) : p.freeVariables = ∅ := by
  simp only [mulLawsContext,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | hp | hp | rfl | rfl
  · exact addLawsContext_closed p hp
  · exact closedContext_closed mulZeroContext p hp
  · exact closedContext_closed mulOneContext p hp
  · exact closedContext_closed distrContext p hp
  · simp [addZero,eq,add,zero,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]
  · simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ]

#print axioms derivedMulLaws
end M6.PA.Presentation
