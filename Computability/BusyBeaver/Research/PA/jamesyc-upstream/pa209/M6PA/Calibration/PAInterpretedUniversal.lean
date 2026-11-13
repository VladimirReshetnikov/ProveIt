module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualityWitnesses
@[expose] public section

/-! A capture-aware introduction rule for the literal guarded source universal.
The entire finite context is shifted; its domain guard remains an actual premise. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

theorem freeShiftTerm (x : Term 0) : Rew.free (Rew.bShift x) = Rew.shift x := by
  cases x with
  | bvar i => nomatch i
  | func fn _ => nomatch fn
  | fvar k => rfl

theorem freeBindEnv {n : Nat} (b : Fin n → Term 0) :
    (fun i => Rew.free (bindEnv b i)) = Fin.cases (.fvar 0) (fun i => Rew.shift (b i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact freeShiftTerm (b j)

def interpretedAllIntro {Γ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ND.Proof (Ordinal.domain (.fvar 0)::shifted Γ)
      (formula p (Fin.cases (.fvar 0) (fun i => Rew.shift (b i))) (fun i => Rew.shift (f i)))) :
    ND.Proof Γ (formula (.all p) b f) := by
  apply allIntro
  convert impIntro h using 1 <;>
    (simp only [formula,Semiformula.free,Rewriting.free,app_eq_rewAux,Semiformula.rewAux,
      Semiformula.imp_eq,Semiformula.neg_eq,rew_neg,Ordinal.domain_rew,formula_rew,
      freeBindEnv] <;>
      (try simp only [shiftEnv,freeShiftTerm]) <;> finishSourceSyntax)

#print axioms interpretedAllIntro
end M6.PA.ForwardRelational

