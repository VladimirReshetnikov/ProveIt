module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationInstantiation
public import M6PA.Calibration.PAPresentationStepCertificate
@[expose] public section

/-! Actual arbitrary-term instances of the six explicitly allowed equality
axioms. These are finite LK constructions, not an assumed Leibniz rule. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

structure EqualityPremises (Γ : List ND.Form) where
  refl : ND.Proof Γ reflexivity
  symm : ND.Proof Γ symmetry
  trans : ND.Proof Γ transitivity
  succ : ND.Proof Γ succCongruence
  add : ND.Proof Γ addCongruence
  mul : ND.Proof Γ mulCongruence

macro "equalityInstanceSyntax" : tactic => `(tactic|
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
    | (change @Semiterm.func language Nat 0 2 Func.mul _ = @Semiterm.func language Nat 0 2 Func.mul _;
        apply congrArg (@Semiterm.func language Nat 0 2 Func.mul))
    | (funext i; fin_cases i))

namespace EqualityPremises

def reflexive {Γ} (E : EqualityPremises Γ) (a : GroundTerm) : ND.Proof Γ (eq a a) := by
  have h := ND.allElim _ a E.refl
  convert h using 1 <;> dsimp [reflexivity] <;> equalityInstanceSyntax

def symmetric {Γ} (E : EqualityPremises Γ) (a b : GroundTerm) :
    ND.Proof Γ (implies (eq a b) (eq b a)) := by
  have h := ND.allElim2 _ b a E.symm
  convert h using 1 <;> dsimp [symmetry] <;> equalityInstanceSyntax

def transitive {Γ} (E : EqualityPremises Γ) (a b c : GroundTerm) :
    ND.Proof Γ (implies (eq a b) (implies (eq b c) (eq a c))) := by
  have h := ND.allElim3 _ c b a E.trans
  convert h using 1 <;> dsimp [transitivity] <;> equalityInstanceSyntax

def successor {Γ} (E : EqualityPremises Γ) (a b : GroundTerm) :
    ND.Proof Γ (implies (eq a b) (eq (Presentation.succ a) (Presentation.succ b))) := by
  have h := ND.allElim2 _ a b E.succ
  convert h using 1 <;> dsimp [succCongruence] <;> equalityInstanceSyntax

def addition {Γ} (E : EqualityPremises Γ) (a b c d : GroundTerm) :
    ND.Proof Γ (implies (eq a b) (implies (eq c d) (eq (Presentation.add a c) (Presentation.add b d)))) := by
  have h := ND.allElim4 _ a b c d E.add
  convert h using 1 <;> dsimp [addCongruence] <;> equalityInstanceSyntax

def multiplication {Γ} (E : EqualityPremises Γ) (a b c d : GroundTerm) :
    ND.Proof Γ (implies (eq a b) (implies (eq c d) (eq (Presentation.mul a c) (Presentation.mul b d)))) := by
  have h := ND.allElim4 _ a b c d E.mul
  convert h using 1 <;> dsimp [mulCongruence] <;> equalityInstanceSyntax

def weaken {Γ Δ} (E : EqualityPremises Γ) (h : ∀ p, p ∈ Γ → p ∈ Δ) : EqualityPremises Δ where
  refl := ND.weaken E.refl h
  symm := ND.weaken E.symm h
  trans := ND.weaken E.trans h
  succ := ND.weaken E.succ h
  add := ND.weaken E.add h
  mul := ND.weaken E.mul h

def symmetryOf {Γ} (E : EqualityPremises Γ) {a b : GroundTerm}
    (h : ND.Proof Γ (eq a b)) : ND.Proof Γ (eq b a) := ND.mp h (E.symmetric a b)

def transitivityOf {Γ} (E : EqualityPremises Γ) {a b c : GroundTerm}
    (h : ND.Proof Γ (eq a b)) (k : ND.Proof Γ (eq b c)) : ND.Proof Γ (eq a c) :=
  ND.mp k (ND.mp h (E.transitive a b c))

def atomTransport {Γ} (E : EqualityPremises Γ) {a b c d : GroundTerm}
    (hab : ND.Proof Γ (eq a b)) (hcd : ND.Proof Γ (eq c d))
    (hac : ND.Proof Γ (eq a c)) : ND.Proof Γ (eq b d) :=
  E.transitivityOf (E.transitivityOf (E.symmetryOf hab) hac) hcd

def shifted {Γ} (E : EqualityPremises Γ) : EqualityPremises (ND.shifted Γ) where
  refl := ND.shiftClosed E.refl (by simp [reflexivity,eq,Semiformula.freeVariables,
    Semiterm.freeVariables,Fin.univ_succ])
  symm := ND.shiftClosed E.symm (by simp [symmetry,implies,eq,Semiformula.freeVariables,
    Semiformula.neg,Semiterm.freeVariables,Fin.univ_succ])
  trans := ND.shiftClosed E.trans (by simp [transitivity,implies,eq,Semiformula.freeVariables,
    Semiformula.neg,Semiterm.freeVariables,Fin.univ_succ])
  succ := ND.shiftClosed E.succ (by simp [succCongruence,implies,eq,
    Presentation.succ,Semiformula.freeVariables,Semiformula.neg,Semiterm.freeVariables,Fin.univ_succ])
  add := ND.shiftClosed E.add (by simp [addCongruence,implies,eq,
    Presentation.add,Semiformula.freeVariables,Semiformula.neg,Semiterm.freeVariables,Fin.univ_succ])
  mul := ND.shiftClosed E.mul (by simp [mulCongruence,implies,eq,
    Presentation.mul,Semiformula.freeVariables,Semiformula.neg,Semiterm.freeVariables,Fin.univ_succ])

end EqualityPremises

def equalityContext : List ND.Form :=
  [reflexivity,symmetry,transitivity,succCongruence,addCongruence,mulCongruence]

def equalityContextPremises : EqualityPremises equalityContext where
  refl := ND.assumption (by simp [equalityContext])
  symm := ND.assumption (by simp [equalityContext])
  trans := ND.assumption (by simp [equalityContext])
  succ := ND.assumption (by simp [equalityContext])
  add := ND.assumption (by simp [equalityContext])
  mul := ND.assumption (by simp [equalityContext])

theorem equalityContext_is_PAeq (p : ND.Form) (hp : p ∈ equalityContext) : PAeqAxiom p := by
  apply PAeqAxiom.fixed
  simp only [equalityContext,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fixedAxioms]

#print axioms EqualityPremises.multiplication
end M6.PA.Presentation
