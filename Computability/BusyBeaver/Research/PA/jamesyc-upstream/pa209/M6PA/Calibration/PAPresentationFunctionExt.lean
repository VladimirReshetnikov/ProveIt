module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationEqualityAxioms
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem equalityContext_closed (p : ND.Form) (hp : p ∈ equalityContext) : p.freeVariables = ∅ :=
  addLawsContext_closed p (by simp [addLawsContext,hp])

def foundationEqZeroProof : ordinaryPAeq.Proof
    (formula (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.zero)) := by
  apply equalityImageProof
  have d : ND.Proof equalityContext (implies .verum (eq zero zero)) := by
    apply ND.impIntro
    exact (equalityContextPremises.weaken (fun p hp => List.mem_cons_of_mem _ hp)).reflexive zero
  convert d using 1 <;> dsimp [Theory.Eq.funcExt,Matrix.conj,formula,atom,term,implies,Semiformula.neg] <;> equalityInstanceSyntax

def foundationEqOneProof : ordinaryPAeq.Proof
    (formula (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.one)) := by
  apply equalityImageProof
  have d : ND.Proof equalityContext (implies .verum (eq (succ zero) (succ zero))) := by
    apply ND.impIntro
    exact (equalityContextPremises.weaken (fun p hp => List.mem_cons_of_mem _ hp)).reflexive (succ zero)
  convert d using 1 <;> dsimp [Theory.Eq.funcExt,Matrix.conj,formula,atom,term,implies,Semiformula.neg] <;> equalityInstanceSyntax

def binaryEqualGround (op : GroundTerm → GroundTerm → GroundTerm)
    (hc : ∀ (Γ : List ND.Form) (E : EqualityPremises Γ) (a b c d : GroundTerm),
      ND.Proof Γ (eq a c) → ND.Proof Γ (eq b d) → ND.Proof Γ (eq (op a b) (op c d)))
    (a b c d : GroundTerm) : ND.Proof equalityContext
      (implies (.and (eq a c) (.and (eq b d) .verum)) (eq (op a b) (op c d))) := by
  apply ND.impIntro
  let p := Semiformula.and (eq a c) (.and (eq b d) .verum)
  let Γ := p :: equalityContext
  let E := equalityContextPremises.weaken (Δ := Γ) (fun q hq => List.mem_cons_of_mem _ hq)
  have h : ND.Proof Γ p := ND.assumption (by simp [Γ])
  exact hc Γ E a b c d (ND.andLeft h) (ND.andLeft (ND.andRight h))

macro "extensionalitySyntax" : tactic => `(tactic|
  repeat' first
    | rfl
    | (change Semiformula.or _ _ = Semiformula.or _ _; apply congrArg₂ (@Semiformula.or language Nat 0))
    | (change Semiformula.and _ _ = Semiformula.and _ _; apply congrArg₂ (@Semiformula.and language Nat 0))
    | (change @Semiformula.rel language Nat 0 2 Rel.eq _ = @Semiformula.rel language Nat 0 2 Rel.eq _;
        apply congrArg (@Semiformula.rel language Nat 0 2 Rel.eq))
    | (change @Semiformula.nrel language Nat 0 2 Rel.eq _ = @Semiformula.nrel language Nat 0 2 Rel.eq _;
        apply congrArg (@Semiformula.nrel language Nat 0 2 Rel.eq))
    | (change @Semiterm.func language Nat 0 2 Func.add _ = @Semiterm.func language Nat 0 2 Func.add _;
        apply congrArg (@Semiterm.func language Nat 0 2 Func.add))
    | (change @Semiterm.func language Nat 0 2 Func.mul _ = @Semiterm.func language Nat 0 2 Func.mul _;
        apply congrArg (@Semiterm.func language Nat 0 2 Func.mul))
    | (funext i; fin_cases i))

def foundationEqAddProof : ordinaryPAeq.Proof
    (formula (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.add)) := by
  apply equalityImageProof
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := binaryEqualGround add (fun Γ E a b c d h k => E.additionOf h k)
    (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3)
  convert h using 1 <;> first
    | (change ND.shifted (ND.shifted (ND.shifted (ND.shifted equalityContext))) = equalityContext;
        rw [shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed])
    | (dsimp [Theory.Eq.funcExt,Matrix.conj,formula,atom,term,implies,Semiformula.neg]; extensionalitySyntax)

def foundationEqMulProof : ordinaryPAeq.Proof
    (formula (Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.mul)) := by
  apply equalityImageProof
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := binaryEqualGround mul (fun Γ E a b c d h k => E.multiplicationOf h k)
    (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3)
  convert h using 1 <;> first
    | (change ND.shifted (ND.shifted (ND.shifted (ND.shifted equalityContext))) = equalityContext;
        rw [shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed,
          shifted_closed equalityContext equalityContext_closed])
    | (dsimp [Theory.Eq.funcExt,Matrix.conj,formula,atom,term,implies,Semiformula.neg]; extensionalitySyntax)

#print axioms foundationEqZeroProof
#print axioms foundationEqOneProof
#print axioms foundationEqAddProof
#print axioms foundationEqMulProof
end M6.PA.Presentation

