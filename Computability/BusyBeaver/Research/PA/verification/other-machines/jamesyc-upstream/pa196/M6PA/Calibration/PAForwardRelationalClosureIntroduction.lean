module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalClosureApplication
@[expose] public section

/-! Conditional exact source universal closure. Uniform body proof data are
required explicitly; an arbitrary open ND or Separation assumption is NOT
silently generalized. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- Finite domain proof data for the prefix actually bound by source univCl'. -/
def FiniteParameterDomains (Γ : List Form) (m : Nat) (f : Nat → Term 0) :=
  ∀ i : Fin m, ND.Proof Γ (Ordinal.domain (f i.val))

/-- A genuine context-uniform body proof family. This assumption cannot be
replaced by a proof under free-parameter-dependent open schema hypotheses. -/
def UniformBoundBody {n : Nat} (p : SourceFormula n) :=
  ∀ {Δ : List Form}, SubstitutionPremises Δ → ∀ (b : Fin n → Term 0) (f : Nat → Term 0),
    (∀ i, ND.Proof Δ (Ordinal.domain (b i))) → ND.Proof Δ (formula p b f)

def sourceAllClosureIntro {Γ : List Form} {n : Nat} (p : SourceFormula n)
    (body : UniformBoundBody p) (A : SubstitutionPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula (∀¹* p) Fin.elim0 f) := by
  induction n generalizing Γ f with
  | zero => exact body A Fin.elim0 f (fun i => Fin.elim0 i)
  | succ n ih =>
    apply ih (.all p) ?_ A f
    intro Δ A' b g Hb
    apply formulaAllIntro p b g
    let d : Form := Ordinal.domain (.fvar 0)
    have hd : ND.Proof (d :: shifted Δ) d := assumption (by simp)
    apply body (A'.shift.up d) (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv g)
    intro i
    refine Fin.cases hd (fun j => ?_) i
    simpa only [Fin.cases_succ, freeShiftEnv, Semiformula.shift, Rewriting.shift, app_eq_rewAux,
      Ordinal.domain_rew] using up (shiftProof (Hb j)) d

/-- Exact guarded source universal parameter closure, using the actual
fixitr/allClosure definition of univCl'. Every parameter premise is finite. -/
def sourceUniversalClosureIntro {Γ : List Form} (p : SourceFormula 0)
    (body : ∀ {Δ : List Form}, SubstitutionPremises Δ → ∀ f : Nat → Term 0,
      FiniteParameterDomains Δ p.fvSup f → ND.Proof Δ (formula p Fin.elim0 f))
    (A : SubstitutionPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula p.univCl' Fin.elim0 f) := by
  apply sourceAllClosureIntro (Semiformula.rewAux (Rew.fixitr 0 p.fvSup) p) ?_ A f
  intro Δ A' b g Hb
  have out := body A' (fixedEnvironment b g) (fun i => by
    simpa only [fixedEnvironment_lt] using Hb (Fin.natAdd 0 i))
  simpa only [formula_sourceFixitr] using out

/-- The Empty-free-variable sentence embedding is the exact same source
closure, rather than a replacement target-language universal formula. -/
def sourceUniversalSentenceIntro {Γ : List Form} (p : SourceFormula 0)
    (body : ∀ {Δ : List Form}, SubstitutionPremises Δ → ∀ f : Nat → Term 0,
      FiniteParameterDomains Δ p.fvSup f → ND.Proof Δ (formula p Fin.elim0 f))
    (A : SubstitutionPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula (Rewriting.emb p.univCl : SourceFormula 0) Fin.elim0 f) := by
  have he : (Rewriting.emb p.univCl : SourceFormula 0) = p.univCl' :=
    Semiformula.coe_univCl_eq_univCl' p
  rw [he]
  exact sourceUniversalClosureIntro p body A f

#print axioms sourceAllClosureIntro
#print axioms sourceUniversalClosureIntro
#print axioms sourceUniversalSentenceIntro
end M6.PA.ForwardRelational

