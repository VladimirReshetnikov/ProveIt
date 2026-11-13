module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherence
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain

def functionBoundEnv : (n : Nat) → Fin n → Term 0
  | 0 => Fin.elim0
  | n+1 => Fin.cases (.fvar 0) (freeShiftEnv (functionBoundEnv n))

def functionGuardContext : Nat → List Form → List Form
  | 0, Γ => Γ
  | n+1, Γ => Ordinal.domain (.fvar 0) :: shifted (functionGuardContext n Γ)

def functionGuardDomain {Γ : List Form} (n : Nat) (i : Fin n) :
    ND.Proof (functionGuardContext n Γ) (Ordinal.domain (functionBoundEnv n i)) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact assumption (by simp [functionGuardContext,functionBoundEnv])
    · have hh := functionGuardDomain (Γ := Γ) n j
      simpa only [Semiformula.shift,Rewriting.shift,app_eq_rewAux,Ordinal.domain_rew,
        functionGuardContext,functionBoundEnv,freeShiftEnv,Fin.cases_succ] using
        up (shiftProof hh) (Ordinal.domain (.fvar 0))

def functionGuardCoherence {Γ : List Form} (A : CoherencePremises Γ) :
    (n : Nat) → CoherencePremises (functionGuardContext n Γ)
  | 0 => A
  | n+1 => ((functionGuardCoherence A n).shift).up (Ordinal.domain (.fvar 0))

def functionGuardTotality {Γ : List Form} (T : TotalityPremises Γ) :
    (n : Nat) → TotalityPremises (functionGuardContext n Γ)
  | 0 => T
  | n+1 => ((functionGuardTotality T n).shift).up (Ordinal.domain (.fvar 0))

#print axioms functionGuardDomain
#print axioms functionGuardCoherence
#print axioms functionGuardTotality
end M6.PA.ForwardRelational

