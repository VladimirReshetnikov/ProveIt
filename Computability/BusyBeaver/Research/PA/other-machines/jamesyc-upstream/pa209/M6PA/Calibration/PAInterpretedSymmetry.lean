module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualitySymmetry
public import M6PA.Calibration.PAPresentationAxioms
@[expose] public section

/-! The literal typed image of the second fixed PAeq equality axiom. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 600000

private theorem freeBindTwo :
    (fun i : Fin 2 => Rew.free (bindEnv (fun _ : Fin 1 => (Semiterm.fvar 0 : Term 0)) i)) =
      (![.fvar 0,.fvar 1] : Fin 2 → Term 0) := by
  funext i
  fin_cases i <;> rfl

def equalitySymmetryImp {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (hsym : ND.Proof Γ PairGraph.isoSymmetryClosed) :
    ND.Proof Γ (equal s t b f 🡒 equal t s b f) := by
  apply impIntro
  exact equalitySymmetry s t b f (up hsym _) (assumption (by simp))

def interpretedSymmetry {Γ : List Form}
    (hsym : ND.Proof Γ PairGraph.isoSymmetryClosed) (f : Nat → Term 0) :
    ND.Proof Γ (formula Presentation.symmetry Fin.elim0 f) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0)
  have hs1 : ND.Proof (d::shifted Γ) PairGraph.isoSymmetryClosed :=
    up (interpretedSymmetryShift hsym) d
  have hs2 : ND.Proof (d::shifted (d::shifted Γ)) PairGraph.isoSymmetryClosed :=
    up (interpretedSymmetryShift hs1) d
  let b : Fin 2 → Term 0 := ![.fvar 0,.fvar 1]
  let fs : Nat → Term 0 := fun i => Rew.shift (Rew.shift (f i))
  have out := equalitySymmetryImp (.bvar 1) (.bvar 0) b fs hs2
  let b1 : Fin 1 → Term 0 := fun _ => .fvar 0
  let fs1 : Nat → Term 0 := fun i => Rew.shift (f i)
  have inner : ND.Proof (d::shifted Γ)
      (formula (.all (Presentation.implies (Presentation.eq (.bvar 1) (.bvar 0))
        (Presentation.eq (.bvar 0) (.bvar 1)))) b1 fs1) := by
    apply allIntro
    convert impIntro out using 1 <;>
      (dsimp [d,b,fs,b1,fs1] <;>
        (try simp only [formula,Presentation.implies,Presentation.eq,bindEnv]) <;>
        interpretedWitnessSyntax <;>
        simp only [formula_rew,formula_neg,formula,bindEnv,rew_neg,Semiformula.rewAux_neg] <;>
        (try interpretedWitnessSyntax) <;>
        (try simp only [freeBindTwo]) <;> (try constructor) <;> (try congr 2) <;> (try (funext i; fin_cases i <;> rfl)) <;> (try (funext i; simp [shiftEnv])) <;> (try trivial) <;>
      (try (cases f i with
        | bvar j => nomatch j
        | func fn _ => nomatch fn
        | fvar k => rfl)))
  convert impIntro inner using 1 <;>
    (dsimp [d,b1,fs1] <;>
      (try simp only [formula,Presentation.symmetry,bindEnv]) <;>
      interpretedWitnessSyntax <;>
      simp only [formula_rew,formula_neg,formula,bindEnv,rew_neg,Semiformula.rewAux_neg] <;>
      (try interpretedWitnessSyntax) <;>
        (try simp only [freeBindTwo]) <;> (try constructor) <;> (try congr 2) <;> (try (funext i; fin_cases i <;> rfl)) <;> (try (funext i; simp [shiftEnv])) <;> (try trivial) <;>
      (try (cases f i with
        | bvar j => nomatch j
        | func fn _ => nomatch fn
        | fvar k => rfl)))

#print axioms equalitySymmetryImp
#print axioms interpretedSymmetry
end M6.PA.ForwardRelational

