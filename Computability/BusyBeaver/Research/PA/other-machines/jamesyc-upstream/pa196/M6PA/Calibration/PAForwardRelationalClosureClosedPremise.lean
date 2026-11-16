module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalClosureCoverage
@[expose] public section

/-! Logical introduction from a single shift-invariant closed theorem. The
closedness equation and uniform specialization interface remain explicit; no
open schema premise is erased or generalized. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def sourceAllClosureFromClosed {Γ : List Form} {n : Nat} (p : SourceFormula n)
    (C : Form) (hclosed : C.shift = C)
    (body : ∀ {Δ : List Form}, ND.Proof Δ C → ∀ (b : Fin n → Term 0) (f : Nat → Term 0),
      (∀ i, ND.Proof Δ (Ordinal.domain (b i))) → ND.Proof Δ (formula p b f))
    (hC : ND.Proof Γ C) (f : Nat → Term 0) :
    ND.Proof Γ (formula (∀¹* p) Fin.elim0 f) := by
  induction n generalizing Γ f with
  | zero => exact body hC Fin.elim0 f (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih (.all p) ?_ hC f
    intro Δ hC' b g Hb
    apply formulaAllIntro p b g
    let d : Form := Ordinal.domain (.fvar 0)
    have hd : ND.Proof (d :: shifted Δ) d := assumption (by simp)
    have hc : ND.Proof (d :: shifted Δ) C := by
      simpa only [hclosed] using up (shiftProof hC') d
    apply body hc (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv g)
    intro i
    refine Fin.cases hd (fun j => ?_) i
    simpa only [Fin.cases_succ, freeShiftEnv, Semiformula.shift, Rewriting.shift,
      app_eq_rewAux, Ordinal.domain_rew] using up (shiftProof (Hb j)) d

/-- To use this with a fully supplied closed guarded theorem, separately prove
its shift invariance and the displayed finite-assignment specialization. Neither
obligation is inferred from an open ND schema premise. -/
def sourceUniversalClosureFromClosed {Γ : List Form} (p : SourceFormula 0)
    (C : Form) (hclosed : C.shift = C)
    (body : ∀ {Δ : List Form}, ND.Proof Δ C → ∀ f : Nat → Term 0,
      FiniteParameterDomains Δ p.fvSup f → ND.Proof Δ (formula p Fin.elim0 f))
    (hC : ND.Proof Γ C) (f : Nat → Term 0) :
    ND.Proof Γ (formula p.univCl' Fin.elim0 f) := by
  apply sourceAllClosureFromClosed (Semiformula.rewAux (Rew.fixitr 0 p.fvSup) p) C hclosed ?_ hC f
  intro Δ hC' b g Hb
  have out := body hC' (fixedEnvironment b g) (fun i => by
    simpa only [fixedEnvironment_lt] using Hb (Fin.natAdd 0 i))
  simpa only [formula_sourceFixitr] using out

def sourceUniversalClosureFromClosedOccurrences {Γ : List Form} (p : SourceFormula 0)
    (C : Form) (hclosed : C.shift = C)
    (body : ∀ {Δ : List Form}, ND.Proof Δ C → ∀ f : Nat → Term 0,
      FormulaDomainCoverage Δ Fin.elim0 f p → ND.Proof Δ (formula p Fin.elim0 f))
    (hC : ND.Proof Γ C) (f : Nat → Term 0) :
    ND.Proof Γ (formula p.univCl' Fin.elim0 f) :=
  sourceUniversalClosureFromClosed p C hclosed
    (fun h g H => body h g (formulaCoverageFromPrefix p g H)) hC f

#print axioms sourceAllClosureFromClosed
#print axioms sourceUniversalClosureFromClosed
#print axioms sourceUniversalClosureFromClosedOccurrences
end M6.PA.ForwardRelational
