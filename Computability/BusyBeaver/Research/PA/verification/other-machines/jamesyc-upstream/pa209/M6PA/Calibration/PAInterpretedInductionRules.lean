module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionInstances
@[expose] public section

/-! Guarded universal specialization and implication normalization for the
literal typed induction image. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain
set_option maxHeartbeats 800000

theorem inductionFormula_implies {n m : Nat} (p q : SourceFormula n)
    (b : Fin n → Term m) (f : Nat → Term m) :
    formula (Presentation.implies p q) b f = (formula p b f 🡒 formula q b f) := by
  simp only [Presentation.implies,formula,formula_neg,Semiformula.imp_eq,Semiformula.neg_eq]

def inductionAllElim {Γ : List Form} (p : SourceFormula 1)
    (f : Nat → Term 0) (a : Term 0)
    (h : ND.Proof Γ (formula (.all p) Fin.elim0 f))
    (ha : ND.Proof Γ (Ordinal.domain a)) : ND.Proof Γ (formula p (fun _ => a) f) := by
  rw [formula] at h
  have hi := allElim _ a h
  have he : (Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv Fin.elim0) (shiftEnv f))/[a] =
      (Ordinal.domain a 🡒 formula p (fun _ => a) f) := by
    simp only [app_eq_rewAux,Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux,
      rew_neg,Ordinal.domain_rew,formula_rew]
    congr 2
    · funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    · funext i
      cases hf : f i with
      | bvar j => nomatch j
      | func fn _ => nomatch fn
      | fvar k => simp only [shiftEnv,hf]; rfl
  exact mp ha (he ▸ hi)

#print axioms inductionFormula_implies
#print axioms inductionAllElim
end M6.PA.ForwardRelational
