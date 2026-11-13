module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedLKUniversal
@[expose] public section

/-! Structural recursion on actual Foundation source LK derivations.
The target proofs are actual relational LK values; arithmetic premises and
host environment domain coverage are explicit. Theory transport and internal
numeric proof-code correctness remain separate. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def interpretedLK {Γ : LK.Sequent Presentation.language} (d : LK.Derivation Γ) :
    InterpretedRefutes Γ := by
  cases d with
  | identity r ts => exact interpretedRefutesIdentity r ts
  | verum => exact interpretedRefutesVerum
  | cut d e => exact interpretedRefutesCut (interpretedLK d) (interpretedLK e)
  | contraction d => exact interpretedRefutesContraction (interpretedLK d)
  | weakening d => exact interpretedRefutesWeakening (interpretedLK d)
  | or d => exact interpretedRefutesOr (interpretedLK d)
  | and d e => exact interpretedRefutesAnd (interpretedLK d) (interpretedLK e)
  | @all Γ p d =>
    exact interpretedRefutesAll (LK.Derivation.all d).traversal.remove p (interpretedLK d)
  | @exs Γ p t d => exact interpretedRefutesExists p t (interpretedLK d)
termination_by structural d

def interpretedLKSingleton {C : List Form} (p : SourceFormula 0)
    (d : LK.Derivation ⦃p⦄) (f : Nat → Term 0)
    (A : SubstitutionPremises C) (H : DomainEnvironment C f) :
    ND.Proof C (formula p Fin.elim0 f) := by
  have hr : InterpretedRefutes (0+⦃p⦄) := by simpa using interpretedLK d
  exact hr.positive f A H (fun q hq => False.elim (by simpa using hq))

#print axioms interpretedLK
#print axioms interpretedLKSingleton
end M6.PA.ForwardRelational

