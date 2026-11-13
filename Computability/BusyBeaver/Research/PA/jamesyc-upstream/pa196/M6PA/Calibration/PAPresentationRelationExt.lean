module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationFunctionExt
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def EqualityPremises.lessTransport {Γ : List ND.Form} (E : EqualityPremises Γ)
    (a b c d : GroundTerm) (hac : ND.Proof Γ (eq a c)) (hbd : ND.Proof Γ (eq b d))
    (hab : ND.Proof Γ (less a b)) : ND.Proof Γ (less c d) := by
  have h1 : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![a]) (less (.bvar 0) (Rew.bShift b))) := by
    simpa only [less_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using hab
  have h2 := E.substituteOne (less (.bvar 0) (Rew.bShift b)) a c hac h1
  have h3 : ND.Proof Γ (less c b) := by
    simpa only [less_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using h2
  have h4 : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![b]) (less (Rew.bShift c) (.bvar 0))) := by
    simpa only [less_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using h3
  have h5 := E.substituteOne (less (Rew.bShift c) (.bvar 0)) b d hbd h4
  simpa only [less_rew,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero] using h5

def binaryRelationGround (rel : GroundTerm → GroundTerm → ND.Form)
    (hc : ∀ (Γ : List ND.Form) (E : EqualityPremises Γ) (a b c d : GroundTerm),
      ND.Proof Γ (eq a c) → ND.Proof Γ (eq b d) → ND.Proof Γ (rel a b) → ND.Proof Γ (rel c d))
    (a b c d : GroundTerm) : ND.Proof equalityContext
      (implies (.and (eq a c) (.and (eq b d) .verum)) (implies (rel a b) (rel c d))) := by
  apply ND.impIntro
  apply ND.impIntro
  let p := Semiformula.and (eq a c) (.and (eq b d) .verum)
  let Γ := rel a b :: p :: equalityContext
  let E := equalityContextPremises.weaken (Δ := Γ)
    (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  have h : ND.Proof Γ p := ND.assumption (by simp [Γ])
  have hr : ND.Proof Γ (rel a b) := ND.assumption (by simp [Γ])
  exact hc Γ E a b c d (ND.andLeft h) (ND.andLeft (ND.andRight h)) hr

def foundationEqRelProof : ordinaryPAeq.Proof
    (formula (Theory.Eq.relExt (L := ℒₒᵣ) Language.ORing.Rel.eq)) := by
  apply equalityImageProof
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := binaryRelationGround eq (fun Γ E a b c d h k l => E.atomTransport h k l)
    (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3)
  convert h using 1 <;> first
    | (change ND.shifted (ND.shifted (ND.shifted (ND.shifted equalityContext))) = equalityContext;
        rw [shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed])
    | (dsimp [Theory.Eq.relExt,Matrix.conj,formula,atom,term,implies,Semiformula.neg]; extensionalitySyntax)

def foundationLtRelProof : ordinaryPAeq.Proof
    (formula (Theory.Eq.relExt (L := ℒₒᵣ) Language.ORing.Rel.lt)) := by
  apply equalityImageProof
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := binaryRelationGround less (fun Γ E a b c d h k l => E.lessTransport a b c d h k l)
    (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3)
  convert h using 1 <;> first
    | (change ND.shifted (ND.shifted (ND.shifted (ND.shifted equalityContext))) = equalityContext;
        rw [shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed])
    | (change Semiformula.rewAux Rew.free
          (Semiformula.rewAux Rew.free.q
            (Semiformula.rewAux Rew.free.q.q
              (Semiformula.rewAux Rew.free.q.q.q
                (Semiformula.rewAux Rew.emb.q.q.q.q
                  (implies (.and (eq (.bvar 0) (.bvar 2)) (.and (eq (.bvar 1) (.bvar 3)) .verum))
                    (implies (less (.bvar 0) (.bvar 1)) (less (.bvar 2) (.bvar 3)))))))) = _;
        simp only [rew_implies_any,Semiformula.rewAux,less_rew,eq_rew]; simp [Rew.q]; rfl)

#print axioms foundationEqRelProof
#print axioms foundationLtRelProof
end M6.PA.Presentation

