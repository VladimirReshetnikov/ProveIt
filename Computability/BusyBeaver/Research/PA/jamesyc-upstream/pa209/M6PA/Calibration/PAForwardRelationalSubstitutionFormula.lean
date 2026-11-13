module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionQuantifiers
@[expose] public section

/-! Actual source formula substitution equivalence under finite occurrence
realizations. The general Rew recursion lifts through every binder with q. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def realizedFormulaCompatible {n : Nat} (p : SourceFormula n) : RealizedFormulaCompatible p :=
  match p with
  | .verum => { forward := by intros; assumption, backward := by intros; assumption }
  | .falsum => { forward := by intros; assumption, backward := by intros; assumption }
  | .rel .eq ts => realizedFormulaRel ts
  | .nrel .eq ts => realizedFormulaNrel ts
  | .and p q => realizedFormulaAnd p q (realizedFormulaCompatible p) (realizedFormulaCompatible q)
  | .or p q => realizedFormulaOr p q (realizedFormulaCompatible p) (realizedFormulaCompatible q)
  | .all p => realizedFormulaAll p (realizedFormulaCompatible p)
  | .exs p => realizedFormulaExists p (realizedFormulaCompatible p)

/-- The proof-transformer construction is discharged into literal ND
implication introductions; no meta-level equivalence replaces the conclusion. -/
def realizedFormulaIff {Γ : List Form} {n k : Nat} (p : SourceFormula n)
    (σ : Rew Presentation.language Nat n Nat k) (A : SubstitutionPremises Γ)
    (b : Fin k → Term 0) (f : Nat → Term 0) (c : Fin n → Term 0) (g : Nat → Term 0)
    (H : FormulaRealization Γ σ b f c g p) :
    ND.Proof Γ ((formula (Semiformula.rewAux σ p) b f 🡒 formula p c g) ⋏
      (formula p c g 🡒 formula (Semiformula.rewAux σ p) b f)) := by
  apply andIntro
  · apply impIntro
    exact (realizedFormulaCompatible p).forward σ (A.up _) b f c g
      (FormulaRealization.up H _) (assumption (by simp))
  · apply impIntro
    exact (realizedFormulaCompatible p).backward σ (A.up _) b f c g
      (FormulaRealization.up H _) (assumption (by simp))

/-- Capture-aware head substitution of a genuine arithmetic term. Its source
bound vector has length n+1 and keeps every old tail variable. -/
def singleBoundFormulaSubst {n : Nat} (u : SourceTerm n) (p : SourceFormula (n+1)) : SourceFormula n :=
  Semiformula.rewAux (Rew.subst (Fin.cases u Semiterm.bvar)) p

/-- All free parameters and nested quantifiers are retained. The chosen `a` is
an actual value witness, not a canonical representative. Guards cover only the
finite external occurrences of p and u; closed totality/iso data stay explicit. -/
def sourceBoundSubstitutionFormula {Γ : List Form} {n : Nat}
    (A : SubstitutionPremises Γ) (p : SourceFormula (n+1)) (u : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (a : Term 0)
    (Hu : EnvironmentCoverage Γ b f u)
    (Hp : FormulaDomainCoverage Γ (Fin.cases a b) f p)
    (ha : ND.Proof Γ (value u b f a)) :
    ND.Proof Γ ((formula (singleBoundFormulaSubst u p) b f 🡒 formula p (Fin.cases a b) f) ⋏
      (formula p (Fin.cases a b) f 🡒 formula (singleBoundFormulaSubst u p) b f)) := by
  unfold singleBoundFormulaSubst
  exact realizedFormulaIff p (Rew.subst (Fin.cases u Semiterm.bvar)) A b f (Fin.cases a b) f
    (headFormulaRealization p u b f a A.coherence.equality Hu ha Hp)

#print axioms realizedFormulaCompatible
#print axioms realizedFormulaIff
#print axioms sourceBoundSubstitutionFormula
end M6.PA.ForwardRelational
