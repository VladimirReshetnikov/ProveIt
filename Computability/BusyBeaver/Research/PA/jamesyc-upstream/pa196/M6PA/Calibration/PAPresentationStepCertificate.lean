module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationND
public import M6PA.Calibration.PAPresentationRewriting
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! A concrete finite PAeq certificate needed by the induction-schema adapter:
x + S(0) = S(x). This is not yet the arbitrary-formula induction transport. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def stepProperty : Semiproposition language 1 := eq (add (.bvar 0) (succ zero)) (succ (.bvar 0))
def stepCertificateContext : List (Proposition language) :=
  [addZero,addSucc,succCongruence,transitivity,inductionFormula stepProperty]

theorem stepContext_is_PAeq (p : Proposition language) (hp : p ∈ stepCertificateContext) :
    PAeqAxiom p := by
  simp only [stepCertificateContext,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .fixed _ (by simp [fixedAxioms])
  · exact .induction stepProperty

namespace ND

def shiftClosed {Γ : List Form} {p : Form} (d : Proof Γ p)
    (hp : p.freeVariables = ∅) : Proof (shifted Γ) p := by
  have h : p.shift = p := by
    apply Semiformula.rew_eq_self_of
    · intro i; exact Fin.elim0 i
    · intro i hi; exact False.elim (by simpa [Semiformula.FVar?,hp] using hi)
  exact (shiftProof d).cast (by rw [h])

end ND

/-- Explicit constructor and finite-vector congruence, avoiding opaque
DecidableEq transports and avoiding native evaluation. -/
macro "stepCertificateSyntax" : tactic => `(tactic|
  repeat' first
    | rfl
    | (change Semiformula.or _ _ = Semiformula.or _ _;
        apply congrArg₂ (@Semiformula.or language Nat 0))
    | (change @Semiformula.rel language Nat 0 2 Rel.eq _ = @Semiformula.rel language Nat 0 2 Rel.eq _;
        apply congrArg (@Semiformula.rel language Nat 0 2 Rel.eq))
    | (change @Semiformula.nrel language Nat 0 2 Rel.eq _ = @Semiformula.nrel language Nat 0 2 Rel.eq _;
        apply congrArg (@Semiformula.nrel language Nat 0 2 Rel.eq))
    | (change @Semiterm.func language Nat 0 0 Func.zero _ = @Semiterm.func language Nat 0 0 Func.zero _;
        apply congrArg (@Semiterm.func language Nat 0 0 Func.zero))
    | (change @Semiterm.func language Nat 0 1 Func.succ _ = @Semiterm.func language Nat 0 1 Func.succ _;
        apply congrArg (@Semiterm.func language Nat 0 1 Func.succ))
    | (change @Semiterm.func language Nat 0 2 Func.add _ = @Semiterm.func language Nat 0 2 Func.add _;
        apply congrArg (@Semiterm.func language Nat 0 2 Func.add))
    | (funext i; fin_cases i))

def addOneSuccessorCertificate : ND.Proof stepCertificateContext (.all stepProperty) := by
  let Γ := stepCertificateContext
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ,stepCertificateContext])
  have ar : ND.Proof Γ addSucc := ND.assumption (by simp [Γ,stepCertificateContext])
  have sc : ND.Proof Γ succCongruence := ND.assumption (by simp [Γ,stepCertificateContext])
  have tr : ND.Proof Γ transitivity := ND.assumption (by simp [Γ,stepCertificateContext])
  have ind : ND.Proof Γ (inductionFormula stepProperty) :=
    ND.assumption (by simp [Γ,stepCertificateContext])
  have base : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![zero]) stepProperty) := by
    have h := ND.allElim _ (succ zero) az
    convert h using 1 <;> dsimp [addZero] <;> stepCertificateSyntax
  have step : ND.Proof Γ (.all (implies stepProperty
      (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) stepProperty))) := by
    apply ND.allIntro
    let x : Semiterm language Nat 0 := .fvar 0
    let one : Semiterm language Nat 0 := succ zero
    have ar' := ND.shiftClosed ar (by
      simp [addSucc,eq,add,succ,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have sc' := ND.shiftClosed sc (by
      simp [succCongruence,implies,eq,succ,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have tr' := ND.shiftClosed tr (by
      simp [transitivity,implies,eq,Semiformula.neg,Semiformula.freeVariables,Semiterm.freeVariables,Fin.univ_succ])
    have hr : ND.Proof (ND.shifted Γ) (eq (add (succ x) one) (succ (add x one))) := by
      have h := ND.allElim _ x (ND.allElim _ one ar')
      convert h using 1 <;> dsimp [addSucc,x,one] <;> stepCertificateSyntax
    have hs : ND.Proof (ND.shifted Γ)
        (implies (eq (add x one) (succ x)) (eq (succ (add x one)) (succ (succ x)))) := by
      have h := ND.allElim _ (add x one) (ND.allElim _ (succ x) sc')
      convert h using 1 <;> dsimp [succCongruence,x,one] <;> stepCertificateSyntax
    have ht : ND.Proof (ND.shifted Γ)
        (implies (eq (add (succ x) one) (succ (add x one)))
          (implies (eq (succ (add x one)) (succ (succ x))) (eq (add (succ x) one) (succ (succ x))))) := by
      have h := ND.allElim _ (succ (succ x)) (ND.allElim _ (succ (add x one))
        (ND.allElim _ (add (succ x) one) tr'))
      convert h using 1 <;> dsimp [transitivity,x,one] <;> stepCertificateSyntax
    have h : ND.Proof (ND.shifted Γ)
        (implies (eq (add x one) (succ x)) (eq (add (succ x) one) (succ (succ x)))) := by
      apply ND.impIntro
      exact ND.mp (ND.mp (ND.assumption (by simp)) (ND.weaken hs (by intro q hq; exact List.mem_cons_of_mem _ hq)))
        (ND.mp (ND.weaken hr (by intro q hq; exact List.mem_cons_of_mem _ hq)) (ND.weaken ht (by intro q hq; exact List.mem_cons_of_mem _ hq)))
    convert h using 1 <;> dsimp [x,one] <;> stepCertificateSyntax
  exact ND.mp step (ND.mp base ind)

#print axioms addOneSuccessorCertificate
end M6.PA.Presentation
